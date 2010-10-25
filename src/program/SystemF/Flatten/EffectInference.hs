
{-# LANGUAGE FlexibleInstances, ViewPatterns, Rank2Types, ScopedTypeVariables #-}
module SystemF.Flatten.EffectInference(inferSideEffects)
where

import Control.Monad
import Control.Monad.Trans
import Control.Concurrent.MVar
import qualified Data.IntMap as IntMap
import Data.Maybe
import Data.Monoid
import qualified Data.Set as Set
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.Label
import Gluon.Common.MonadLogic
import Gluon.Common.SourcePos
import Gluon.Common.Supply
import Gluon.Core.Level
import Gluon.Core.Variance
import Gluon.Core(Rec, SynInfo(..), mkSynInfo, internalSynInfo,
                  Con, conID, Var, varID)
import qualified Gluon.Core as Gluon
import Gluon.Eval.Eval
import qualified SystemF.Builtins as SF
import qualified SystemF.Syntax as SF
import qualified SystemF.Print as SF
import qualified SystemF.Typecheck as SF
import qualified Core.Syntax as Core
import Core.Syntax(Representation(..))
import qualified Core.BuiltinTypes as Core
import qualified Core.Print as Core
import SystemF.Flatten.Constraint
import SystemF.Flatten.Effect
import SystemF.Flatten.EffectType
import SystemF.Flatten.EffectExp
import SystemF.Flatten.GenCore
import Globals

-- | Direction of data flow
data Direction = InDir          -- ^ Input, as a function parameter
               | OutDir         -- ^ Output, as a function return
               | UnDir          -- ^ Undirected
                 deriving(Eq)

-------------------------------------------------------------------------------
-- The effect inference monad

-- | The effect inference monad.  When effect inference runs, it keeps track
-- of constraints and free effect variables in the code that it scans.
newtype EI a =
  EI {runEI :: EffectEnv -> IO (a, Endo Constraint, Endo [EffectVar])}

returnEI x = return (x, mempty, mempty)

data EffectEnv =
  EffectEnv
  { -- | Environment used by 'RegionM'
    efRegionEnv :: {-# UNPACK #-}!RegionEnv
    
    -- | Regions assigned to constructors
  , efConRegions :: !(IntMap.IntMap RVar)
    
    -- | Effect types assigned to variables in the environment
  , efEnv :: !(IntMap.IntMap EffectAssignment)
  }

instance Monad EI where
  return x = EI $ \_ -> returnEI x
  m >>= k = EI $ \env -> do (x, cs, vs) <- runEI m env
                            (y, cs', vs') <- runEI (k x) env
                            return (y, cs `mappend` cs', vs `mappend` vs')

instance MonadIO EI where
  liftIO m = EI $ \_ -> m >>= returnEI

instance Supplies EI (Ident EffectVar) where
  fresh = EI $ \env -> supplyValue (reRegionIDs $ efRegionEnv env) >>= returnEI

instance Supplies EI (Ident Var) where
  fresh = EI $ \env -> supplyValue (reVarIDs $ efRegionEnv env) >>= returnEI

instance RegionMonad EI where
  assumeRegion v m = assertRVar v $ EI $ \env ->
    let region_env' =
          (efRegionEnv env) {reRegionEnv =
                                Set.insert v $ reRegionEnv $ efRegionEnv env}
        env' = env {efRegionEnv = region_env'}
    in runEI m env'

  assumeEffect v m = assertEVar v $ EI $ \env ->
    let region_env' =
          (efRegionEnv env) {reRegionEnv =
                                Set.insert v $ reRegionEnv $ efRegionEnv env}
        env' = env {efRegionEnv = region_env'}
    in runEI m env'

  getRigidEffectVars = EI $ \env -> returnEI $ reRegionEnv $ efRegionEnv env

runEffectInference evar_ids var_ids con_map m = do
  let renv = RegionEnv evar_ids var_ids Set.empty
      env = EffectEnv renv con_map IntMap.empty
  (x, _, _) <- runEI m env
  return x

liftRegionM :: RegionM a -> EI a
liftRegionM m = EI $ \env -> doRegionM m (efRegionEnv env) >>= returnEI

assumeAssignment :: Var -> EffectAssignment -> EI a -> EI a
assumeAssignment v ass m = EI $ \env ->
  let env' = env {efEnv = IntMap.insert (fromIdent $ varID v) ass $ efEnv env}
  in runEI m env'

assumeType :: Var -> EReturnType -> EI a -> EI a
assumeType v ty m = assume_region $ EI $ \env -> do
  -- Add variable to environment
  let env' = env {efEnv = IntMap.insert (fromIdent $ varID v) (MonoEffect ty) $
                          efEnv env}
  
  -- Run the computation in the local environment
  runEI m env'
  where
    -- If there is a local region, add it to the environment
    assume_region m =
      case ty
      of WriteRT rgn _ -> assumeRegion rgn m
         _ -> m

addPredicate :: Predicate -> EI ()
addPredicate p = EI $ \_ -> return ((), Endo (p:), mempty)

addConstraint :: Constraint -> EI ()
addConstraint cst = EI $ \_ -> return ((), Endo (cst ++), mempty)

transformConstraint :: (a -> Constraint -> [EffectVar] -> RegionM (Constraint, [EffectVar]))
                    -> EI a -> EI a
transformConstraint t m = EI $ \env -> do
  (x, cst, vars) <- runEI m env
  (cst', vars') <-
    doRegionM (t x (appEndo cst []) (appEndo vars [])) (efRegionEnv env)
  return (x, Endo (cst' ++), Endo (vars' ++))

assertDoesn'tMention :: EffectVar -> EReturnType -> EI ()
assertDoesn'tMention v rt =
  whenM (liftIO $ rt `mentionsE` v) $ fail "Region variable escapes"

assertEmptyEffect :: Effect -> EI ()
assertEmptyEffect e = assertSubeffect e emptyEffect

assertEqualEffect :: Effect -> Effect -> EI ()
assertEqualEffect e1 e2 =
  addConstraint =<< liftRegionM (mkEqualityConstraint e1 e2)

assertSubeffect :: Effect -> Effect -> EI ()
assertSubeffect e1 e2 = addConstraint (subEffect e1 e2)

-- | Get the constraint produced by the computation.  The constraint is
-- not propagated.
extractConstraint :: EI a -> EI (a, Constraint)
extractConstraint m = EI $ \env -> do
  (x, cs, vs) <- runEI m env
  return ((x, appEndo cs []), mempty, vs)

-- | Look up the type that was assigned to a variable.  Throw an error if the
-- variable is not found.
lookupVarType :: Var -> EI EffectAssignment
lookupVarType v = EI $ \env ->
  case IntMap.lookup (fromIdent $ varID v) $ efEnv env
  of Just rt -> returnEI rt
     Nothing -> internalError "lookupVarType: No information for variable"

-- | Look up the region inhabited by a constructor that uses 'Reference' 
-- representation.  Constructors with other representations aren't in the map.
lookupConRegion :: Con -> EI RVar
lookupConRegion c = EI $ \env ->
  case IntMap.lookup (fromIdent $ conID c) $ efConRegions env
  of Just rgn -> returnEI rgn
     Nothing -> internalError "lookupConRegion: No information for constructor"

-- | Record that a new effect variable was created
tellNewEffectVar :: EffectVar -> EI ()
tellNewEffectVar v = EI $ \env -> return ((), mempty, Endo (v:))

tellNewEffectVars :: [EffectVar] -> EI ()
tellNewEffectVars vs = EI $ \env -> return ((), mempty, Endo (vs ++))

-- | Create a new effect variable that does not have a binding.  The variable 
-- will either be unified with something else or assigned a binding during
-- generalization.
newFlexibleEffectVar :: EI EffectVar
newFlexibleEffectVar = do v <- newEffectVar
                          tellNewEffectVar v
                          return v



toReturnType :: Gluon.RExp -> EI EReturnType
toReturnType ty = do
  (ty', evars) <- liftRegionM $ toEffectType =<< evalHead' ty
  tellNewEffectVars evars
  liftRegionM $ etypeToReturnType ty'

toPureReturnType :: Gluon.RExp -> EI EReturnType
toPureReturnType ty = liftRegionM $ do
  etypeToReturnType =<< toPureEffectType =<< evalHead' ty

-------------------------------------------------------------------------------
-- Effect inference

fromTRExp (SF.TypedSFExp (SF.TypeAnn _ e)) = e

fromTRType (SF.TypedSFType (SF.TypeAnn _ t)) = t

-- | Remove the type annotations from an expression.  Used to produce an 
-- expression that can be printed, when debugging.
eraseTypeAnnotations :: SF.TRExp -> SF.RExp
eraseTypeAnnotations (SF.TypedSFExp (SF.TypeAnn _ e)) =
  SF.mapSFExp fromExp fromAlt fromFun fromType e
  where
    fromExp = eraseTypeAnnotations
    fromAlt (SF.TypedSFAlt (SF.TypeAnn _ a)) = SF.mapAlt fromExp fromType a
    fromFun (SF.TypedSFFun (SF.TypeAnn _ f)) =
      SF.Fun { SF.funInfo = SF.funInfo f
                  , SF.funTyParams = map (\(SF.TyPat v ty) -> SF.TyPat v (fromType ty)) $ SF.funTyParams f
                  , SF.funParams = map (SF.mapPat fromType) $ SF.funParams f
                  , SF.funReturnType = fromType $ SF.funReturnType f
                  , SF.funBody = fromExp $ SF.funBody f
                  }
    fromType = fromTRType

-- | Perform effect inference on an expression.
-- Effect inference returns a new expression with explicit coercions and
-- effect parameters, the inferred return type, and the inferred
-- side effect.
inferExp :: SF.TRExp -> EI (EExp, Effect)
inferExp typed_expression@(SF.TypedSFExp (SF.TypeAnn ty expression)) =
 debug $ do
  (effect_exp, effect) <-
    case expression
    of SF.VarE {SF.expInfo = inf, SF.expVar = v} ->
         inferVarE inf v
       SF.ConE {SF.expInfo = inf, SF.expCon = c} ->
         inferConE inf c
       SF.LitE {SF.expInfo = inf, SF.expLit = l} ->
         inferLitE ty inf l
       SF.TyAppE {SF.expInfo = inf} -> do
         (OrdinaryOper op, ty_args) <- unpackTypeApplication typed_expression
         inferApp ty inf op (zip ty_args $ repeat emptyEffect)
       
       SF.CallE {SF.expInfo = inf, SF.expOper = op, SF.expArgs = args} -> do
         (unpacked_op, ty_args) <- unpackTypeApplication op
         args' <- mapM inferExp args
         
         -- The 'do' operator is evaluated lazily, so we handle it specially
         case unpacked_op of
           OrdinaryOper op' ->
             inferApp ty inf op' (zip ty_args (repeat emptyEffect) ++ args')
           DoOper ->
             inferDo inf ty_args args'
       SF.FunE {SF.expInfo = inf, SF.expFun = f} -> do
         (f_type, f') <- inferFun True f
         return_type <- liftRegionM $ etypeToReturnType f_type
         let new_exp = EExp inf return_type $ FunE f'
         return (new_exp, emptyEffect)
       SF.LetE { SF.expInfo = inf
               , SF.expBinder = lhs
               , SF.expValue = rhs
               , SF.expBody = body} ->
         inferLet ty inf lhs rhs body
       SF.LetrecE {SF.expInfo = inf, SF.expDefs = defs, SF.expBody = body} ->
         inferLetrec ty inf defs body
       SF.CaseE { SF.expInfo = inf
                , SF.expScrutinee = scr
                , SF.expAlternatives = alts} ->
         inferCase ty inf scr alts
  return (effect_exp, effect)
  where
    debug x =
      let message = text "inferExp" <+>
                    SF.pprExp (eraseTypeAnnotations typed_expression)
      in traceShow message x

-- | Convert a type from System F's type inference pass
fromInferredType :: SF.TRType -> EI EExp
fromInferredType (SF.TypedSFType (SF.TypeAnn k t)) = do
  (t', effs) <- liftRegionM $ toEffectType =<< evalHead' t
  tellNewEffectVars effs
  let info = Gluon.internalSynInfo (getLevel t')
  return_type <- toReturnType (Gluon.fromWhnf k)
  return $ EExp info return_type $ TypeE (discardTypeRepr t')

data UnpackedOper = OrdinaryOper !(EExp, Effect)
                  | DoOper

unpackTypeApplication :: SF.TRExp -> EI (UnpackedOper, [EExp])
unpackTypeApplication expr = unpack [] expr
  where
    unpack ty_args (fromTRExp -> SF.TyAppE { SF.expOper = op
                                           , SF.expTyArg = arg}) = do
      arg' <- fromInferredType arg
      unpack (arg' : ty_args) op

    -- Don't infer effects in the 'do' operator, it's not a real function
    unpack ty_args op 
      | is_do_oper op =
          return (DoOper, ty_args)
      | otherwise = do
          op' <- inferExp op
          return (OrdinaryOper op', ty_args)
    
    is_do_oper (SF.TypedSFExp (SF.TypeAnn _ expr)) =
      case expr
      of SF.ConE {SF.expCon = c} -> c `SF.isPyonBuiltin` SF.the_oper_DO
         _ -> False

inferVarE inf v = do 
  typeass <- lookupVarType v
  exp <- instantiateEffectAssignment inf (Left v) typeass
  return (exp, emptyEffect)

inferConE inf c = do
  -- Translate the constructor's type back from Core 
  (eff_qvars, eff_type) <- liftRegionM $ coreToEffectType $ Core.conCoreType c
  mapM_ tellNewEffectVar eff_qvars
  
-- Create an expression
  let exp1 = if null eff_qvars
             then ConE c
             else InstE (Right c) (map varEffect eff_qvars)
                  
  -- Create a return type.  If the constructor is a reference to a global
  -- variable, look up the region.
  rt <- case eff_type
        of ERepType Value t      -> return $ ValRT t
           ERepType Boxed t      -> return $ OwnRT t
           ERepType Referenced t -> do rgn <- lookupConRegion c
                                       return $ ReadRT rgn t
  
  return (EExp inf rt exp1, emptyEffect)

inferLitE ty inf lit = do
  return_ty <- toReturnType (Gluon.fromWhnf ty)
  -- Literal value has no side effect and returns by value
  return (EExp inf return_ty (LitE lit (returnTypeType return_ty)), emptyEffect)

-- | Effect inference on a stream constructor (\"do\").  Since streams are
-- lazy, always return the empty effect.  The body's side effect appears in
-- the type of the stream that is created.
inferDo :: SynInfo -> [EExp] -> [(EExp, Effect)] -> EI (EExp, Effect)
inferDo inf [return_type] [(repr_exp, repr_eff), (body_exp, body_eff)] = do
  -- Type class expressions should never have a side effect
  assertEmptyEffect repr_eff
  
  -- The body must return a reference
  return_rv <- newRegionVar False
  let co_type = WriteRT return_rv (returnTypeType $ expReturn body_exp)
  (_, _, body_co, co_eff) <- coerceReturn co_type (expReturn body_exp)
  let body_co_exp = applyCoercion body_co body_exp
  let body_co_eff = body_eff `effectUnion` varsEffect co_eff

  let expr = DoE { expTyArg = return_type
                 , expPassConv = repr_exp
                 , expEffect = body_co_eff
                 , expBody = body_co_exp
                 }
  let stream_type = AppT (InstT stream_con [body_eff]) [returnTypeType $ expReturn body_exp]
  stream_return_type <-
    liftRegionM $ etypeToReturnType $ etypeWithStandardRepr stream_type

  return (EExp inf stream_return_type expr, emptyEffect)
  where
    stream_con = Right (SF.pyonBuiltin SF.the_LazyStream)

inferDo _ _ _ =
  internalError "inferDo: Invalid stream constructor found in effect inference"

inferApp :: Gluon.WRExp
         -> SynInfo 
         -> (EExp, Effect)
         -> [(EExp, Effect)]
         -> EI (EExp, Effect)
inferApp result_type info (op, op_effect) (unzip -> (args, arg_effects)) = 
 traceShow (text "inferApp" <+> vcat (map pprEExp (op : args))) $ do
  let variances = expVariance op
  -- Compute side effects of function application and coerce arguments
  (args', call_effect, return_type) <- applyArguments (expReturn op) args

  -- Add effects of operands
  let effect = effectUnions $ call_effect : op_effect : arg_effects
  let exp = EExp info return_type $ CallE op args'
  return (exp, effect)

-- | Get the variance of an expression's parameters.  Unknowns are treated
-- as 'Invariant'.  Functions are covariant in all parameters.
-- Constructors have customizable variance on each parameter.
expVariance :: EExp -> [Variance]
expVariance exp =
  case expExp exp
  of ConE c ->
       let con_variance =
             map (Gluon.patVariance . Gluon.binder'Value) $ Gluon.conParams c
       in con_variance ++ repeat Invariant
     _ -> repeat Invariant

-- | Compute the effect of applying an operator to its arguments.
-- Argument coercions are inserted, side effects are computed, and the 
-- return type is computed.
applyArguments :: EReturnType -> [EExp]
               -> EI ([EExp], Effect, EReturnType)
applyArguments oper_type args = traceShow (text "applyArguments" <+> (pprEReturnType oper_type $$ vcat (map pprEExp args))) $ do
  ((), (eff, oper_type', crs), args') <- go oper_type init_acc args
  
  -- Remove from the effect regions that are local to the function call
  let eff' = foldr deleteFromEffect eff crs
  return (args', eff', oper_type')
  where
    go (OwnRT fun_type) acc (arg : args) = do
      (call_regions, (), (eff, op_type, crs), args') <-
        applyType fun_type arg $
        \arg' eff return_type scoped_regions local_regions -> do
          retval@((), (eff, oper_type, _), args') <-
            go return_type (add_acc acc arg' eff) args
          
          -- DEBUG: print effect
          liftIO $ putStrLn $ "applyArguments " ++ show (pprEffect eff)
          return retval
      return ((), (eff, op_type, call_regions ++ crs), args')
    
    -- If applying an argument, the function type must be owned
    go _ _ (_:_) = internalError "applyArguments: Expecting owned type"
    
    go oper_type (args, eff) [] = do
      -- DEBUG: print effect
      liftIO $ putStrLn $ "applyArguments " ++ show (pprEffect eff)
      return ((), (eff, oper_type, []), reverse args)

    -- Accumulate the result of applying one argument.
    add_acc (args, eff) new_arg new_eff =
      (new_arg : args, eff `effectUnion` new_eff)

    -- Initially, there is no side effect.
    init_acc = ([], emptyEffect)

-- | Compute the result of a function application.
--
-- Returns the coerced argument, the application's result type, 
-- the side effect of the application, and an effect transformation that
-- masks out effects on any locally created memory.
applyType :: EType              -- ^ Operator type
          -> EExp               -- ^ Argument
          -> (EExp -> Effect -> EReturnType -> [RVar] -> [RVar]
              -> EI ((), (Effect, EReturnType, [RVar]), a))
          -> EI ([RVar], (), (Effect, EReturnType, [RVar]), a)
applyType op_type arg k =
  case op_type
  of FunT param_type eff return_type -> do
       (_, _, call_regions, (a, b, c)) <- coerceParameter param_type arg_type $
         \coercion _ dep_renaming local_regions exposed_regions -> do
           -- Apply coercion to argument
           let arg' = applyCoercion coercion arg

           -- Rename return and effect types to the given parameter value
           -- if it was dependent
           rrtype <- liftIO $ evalAndApplyRenaming (dep_renaming arg) return_type
           reff <- liftIO $ evalAndApplyRenaming (dep_renaming arg) eff

           -- Continue
           let eff' = reff `effectUnion` varsEffect exposed_regions
           x@(_, (eff, rt, _), _) <- k arg' eff' rrtype local_regions exposed_regions
           traceShow (text "applyType" <+> pprEffect eff) $ return x
       return (call_regions, a, b, c)
     _ -> internalError "applyType: Not a function type"
  where
    arg_type = expReturn arg

inferLet :: Gluon.WRExp -> SynInfo -> SF.Pat SF.TypedRec
         -> SF.TRExp -> SF.TRExp -> EI (EExp, Effect)
inferLet _ inf lhs rhs body = do 
  (rhs_exp, rhs_eff) <- inferExp rhs
  (lhs_var, lhs_ty) <- patternAsLetBinder lhs (expReturn rhs_exp)
  (body_exp, body_eff) <- assumeType lhs_var lhs_ty $ do
    (body_exp, body_eff) <- inferExp body
    mask_local_region lhs_ty body_exp body_eff
  
  -- Create a let expression
  let let_exp = LetE lhs_var lhs_ty rhs_exp body_exp
      eff = rhs_eff `effectUnion` body_eff
  return (EExp inf (expReturn body_exp) let_exp, eff)
  where
    mask_local_region (WriteRT rgn _) body_exp body_eff = do
      -- If a local region was created, the return value must not mention it
      -- and the effect should not be visible outside
      assertDoesn'tMention rgn $ expReturn body_exp
      let body_eff' = deleteFromEffect rgn body_eff
      return (body_exp, body_eff')
    
    mask_local_region _ body_exp body_eff = return (body_exp, body_eff)
    

inferLetrec :: Gluon.WRExp -> SynInfo -> [SF.Def SF.TypedRec] -> SF.TRExp
            -> EI (EExp, Effect)
inferLetrec _ inf defs body = do
  (defs', (body', body_eff)) <- inferDefGroupOver defs $ inferExp body

  let exp = LetrecE defs' body'
  return (EExp inf (expReturn body') exp, body_eff)

inferCase :: Gluon.WRExp -> SynInfo -> SF.TRExp -> [SF.RecAlt SF.TypedRec]
          -> EI (EExp, Effect)
inferCase case_type inf scr alts = do
  (scr', scr_eff) <- inferExp scr
  (alts', alt_effects, return_type) <- infer_alternatives alts
  
  let new_expr = CaseE { expScrutinee = scr'
                       , expAlts = alts'
                       }
  let eff = effectUnions (scr_eff : alt_effects)
  return (EExp inf return_type new_expr, eff)
  where
    infer_alternatives [alt] = do
      (alt', alt_eff) <- inferAlt Nothing alt
      return ([alt'], [alt_eff], expReturn $ ealtBody alt')
  
    -- If there are multiple alternatives, then determine the return type 
    -- based on the expression's type.  Coerce all alternatives' returns
    -- to that return type.
    infer_alternatives alts = do
      return_type <- toReturnType  (Gluon.fromWhnf case_type)
      (alts, effs) <- mapAndUnzipM (inferAlt (Just return_type)) alts
      return (alts, effs, return_type)

tyPatAsBinder :: SF.TyPat SF.TypedRec -> EI EParam
tyPatAsBinder (SF.TyPat v (SF.TypedSFType (SF.TypeAnn _ ty))) = do
  param_type <- liftRegionM $ toPureEffectType =<< evalHead' ty
  return $ ValP v $ discardTypeRepr param_type

patternAsBinder :: Bool -> SF.Pat SF.TypedRec -> EI EParam
patternAsBinder no_effects (SF.VarP v (SF.TypedSFType (SF.TypeAnn _ ty))) = do
  (param_type, effs) <- liftRegionM $ do
    ty' <- evalHead' ty
    (etype, effs) <- if no_effects
                     then do etype <- toPureEffectType ty'
                             return (etype, [])
                     else toEffectType ty'
    -- Value parameters aren't used dependently                          
    param_type <- etypeToParamType etype Nothing
    return (param_type, effs)
  tellNewEffectVars effs
  return $! case param_type
            of ValPT _ ty -> ValP v ty
               OwnPT ty -> OwnP v ty
               ReadPT rgn ty -> ReadP v rgn ty

patternAsBinder _ _ = internalError "patternAsBinder"

patternsAsBinders no_effects xs = mapM (patternAsBinder no_effects) xs

withBinder :: EParam -> EI a -> EI a
withBinder param m =
  case return_type
  of ValRT ty -> assumeType v return_type m
     OwnRT ty -> assumeType v return_type m
     ReadRT rgn ty -> assumeRegion rgn $ assumeType v return_type m
  where
    v = paramVar param
    return_type = paramReturnType param

withBinders bs m = foldr withBinder m bs

-- | Add a function definition to the environment 
withDef :: EDef -> EI a -> EI a
withDef (EDef v f) m = assumeAssignment v (efunPolyType f) m

-- | Get the type of a function, but do not generalize the function's type.
-- The type so produced is used when processing recursive functions.
inferFunMonoType :: SF.Fun SF.TypedRec -> EI EReturnType
inferFunMonoType (SF.TypedSFFun (SF.TypeAnn _ f)) = do
  -- Convert parameters
  ty_params <- mapM tyPatAsBinder $ SF.funTyParams f
  val_params <- patternsAsBinders False $ SF.funParams f
  let params = ty_params ++ val_params
  
  -- Convert return type
  return_type <- toReturnType (fromTRType $ SF.funReturnType f)
    
  -- Create a new variable for the effect type
  effect_type <- newFlexibleEffectVar
  
  -- Return this type
  liftRegionM $ etypeToReturnType $
    funMonoEType params (varEffect effect_type) return_type

-- | Add a set of recursive function definitions to the environment.  The
-- functions are given monotypes, derived from their System F types.
assumeRecursiveDefGroup :: [SF.Def SF.TypedRec] -> EI a -> EI a
assumeRecursiveDefGroup fs m = do
  -- Create types for each function
  mono_types <- mapM make_monotype fs
  
  -- Add these types to the environment
  foldr (uncurry assumeAssignment) m mono_types
  where
    make_monotype (SF.Def v f) = do
      monotype <- inferFunMonoType f
      placeholder <- liftIO newEmptyMVar
      return (v, RecEffect placeholder monotype)

-- | Convert a System F pattern to a binder in a @let@ expression.
-- To decide how to convert the pattern, if the type is passed borrowed,
-- we need to know how the RHS returns its return value.
patternAsLetBinder :: SF.Pat SF.TypedRec
                   -> EReturnType 
                   -> EI (Var, EReturnType)
patternAsLetBinder (SF.VarP v ty) rhs_return = do
  -- Don't need to convert the type. Just use the type from the RHS.
  -- etype <- liftRegionM $ toEffectType ty
  
  return (v, rhs_return)

patternAsLetBinder _ _ = internalError "patternAsLetBinder"

inferFun :: Bool -> SF.Fun SF.TypedRec -> EI (ERepType, EFun)
inferFun is_lambda (SF.TypedSFFun (SF.TypeAnn _ f)) = do
  -- Convert parameters
  ty_params <- mapM tyPatAsBinder $ SF.funTyParams f
  val_params <- patternsAsBinders False $ SF.funParams f
  let params = ty_params ++ val_params

  (fun_type, body, body_eff, return_type) <- withBinders params $ do
    -- Use the declared return type as the function's return type.  This is
    -- so that we have the correct representation in the type.  The type
    -- inferred from the function body may have a different representation.
    return_type <- toReturnType (fromTRType $ SF.funReturnType f)

    -- Eliminate constraints on flexible variables if this function is going 
    -- to be generalized.  Otherwise, don't because it creates more
    -- variables.
    if is_lambda
      then infer_function_body return_type params
      else prepare_for_generalization (infer_function_body return_type params)
  
  let new_fun = EFun { funInfo = SF.funInfo f
                     , funEffectParams = []
                     , funParams = params
                     , funReturnType = return_type
                     , funEffect = body_eff
                     , funBody = body
                     }
  return (fun_type, new_fun)
  where
    infer_function_body return_type params = do
      -- Infer the function body
      (body, body_eff) <- inferExp $ SF.funBody f

      -- Coerce the return value to the right representation
      (return_type', _, coercion, _) <-
        coerceReturn return_type (expReturn body)
      let body' = applyCoercion coercion body

      -- Create and return the function's type.  It will be used for
      -- generalization.
      let fun_type = funMonoEType params body_eff return_type'
      return (fun_type, body', body_eff, return_type')
  
    -- Make all flexible variables in the function body independent of one
    -- another.  Clear all flexible variables that don't escape in the return 
    -- type.
    prepare_for_generalization infer_body = 
      transformConstraint mfvi infer_body
      where
        mfvi return_value@(fun_type, body, body_eff, _) cst vs = do
          let get_free_vars = do
                -- Make sure to get the actu
                fvs <- freeEffectVars fun_type
                return (freePositiveVars fvs, freeNegativeVars fvs)
          cst' <-
            makeFlexibleVariablesIndependentWithConstraint get_free_vars cst
          clearFlexibleEffectVariables get_free_vars vs
          return (cst', [])

-- | Perform effect inference on a definition group and add the definition 
-- group to the environment during some other computation.  Return the
-- inferred definition group and the result of the other computation.
inferDefGroupOver :: SF.DefGroup SF.TypedRec -> EI a -> EI (EDefGroup, a)
inferDefGroupOver defs m = do
  defs' <- inferDefGroup defs
  x <- foldr withDef m defs'
  return (defs', x)

inferDefGroup :: SF.DefGroup SF.TypedRec -> EI EDefGroup
inferDefGroup defs = do
  -- Add first-order bindings to the environment and do effect inference.
  -- Generalize the returned types.
  inferred_defs <- assumeRecursiveDefGroup defs $ mapM effect_infer_def defs
  gen_defs <- generalize inferred_defs
  
  -- Force type unification so that we can read the actual type signatures
  -- when instantiating function types
  liftIO $ mapM forceEDefTypeFields gen_defs

  -- TODO: replace placeholders
  where
    -- Infer the function type.  Eliminate constraints on effect variables 
    -- that were generated from the function body.
    effect_infer_def :: SF.Def SF.TypedRec -> EI (ERepType, EDef)
    effect_infer_def (SF.Def v f) = do
      (f_type, f') <- inferFun False f
      return (f_type, EDef v f')
    
    generalize :: [(ERepType, EDef)] -> EI EDefGroup
    generalize defs = forM defs $ \(ty, EDef v f) -> do
      -- Get all effect variables mentioned in the monotype
      FreeEffectVars ftvs_pos ftvs_neg <- liftIO $ freeEffectVars ty

      -- The non-rigid effect variables are the function paramters.
      -- Rigid effect variables are bound at an outer scope.
      let ftvs = Set.union ftvs_pos ftvs_neg
          effect_params = Set.toList ftvs
      flexible_effect_params <- filterM isFlexible effect_params

      -- Set the function's effect variables
      return $ EDef v (f {funEffectParams = flexible_effect_params})

-- | Infer effects in a case alternative.  If a return type is given,
-- coerce the return value to that return type.
inferAlt :: Maybe EReturnType -> SF.RecAlt SF.TypedRec -> EI (EAlt, Effect)
inferAlt mreturn_type (SF.TypedSFAlt (SF.TypeAnn _ alt)) = do
  ty_args <- liftRegionM $ mapM inferTypeExp $ SF.altTyArgs alt
  
  -- Do not allow extra side effects in alternatives 
  params <- sequence [patternAsBinder True (SF.VarP v ty)
                     | SF.Binder v ty () <- SF.altParams alt]
  let local_regions = mapMaybe paramRegion params

  (body_exp, body_eff) <- withBinders params $ do
    (body_exp, body_eff) <- inferExp $ SF.altBody alt
  
    -- Coerce return value
    (body_exp', co_eff) <- coerce_return mreturn_type body_exp
    let alt_eff = body_eff `effectUnion` varsEffect co_eff

    -- Pattern-bound variable effects must not escape
    whenM (liftIO $ expReturn body_exp' `mentionsAnyE` Set.fromList local_regions) $
      fail "inferAlt: Local region escapes"

    -- Hide effects on pattern-bound variables
    let eff = deleteListFromEffect local_regions alt_eff
    return (body_exp', eff)

  let con = SF.altConstructor alt
  return (EAlt con (map discardTypeRepr ty_args) params body_exp, body_eff)
  where
    coerce_return Nothing e = return (e, [])
    coerce_return (Just rt) e = do
      (_, _, coercion, exposed_reads) <- coerceReturn rt (expReturn e)
      return (applyCoercion coercion e, exposed_reads)

inferTypeExp :: SF.RecType SF.TypedRec -> RegionM ERepType
inferTypeExp (SF.TypedSFType (SF.TypeAnn k t)) = do
  (t', []) <- toEffectType =<< evalHead' t
  return t'

inferExport :: SF.Export SF.TypedRec -> EI EExport
inferExport export = do
  (_, fun) <- inferFun False $ SF.exportFunction export
  let inf = mkSynInfo (SF.exportSourcePos export) ObjectLevel
  return $ EExport inf (SF.exportSpec export) fun

-- | Instantiate a possibly polymorphic variable or constructor.
-- Get the effect type.
instantiateEffectAssignment :: SynInfo
                            -> Either Var Con
                            -> EffectAssignment
                            -> EI EExp
instantiateEffectAssignment info poly_op assignment = 
  case assignment
  of MonoEffect rt -> do
       -- Construct a variable/constructor expression with the given type
       let exp1 = case poly_op
                  of Left v -> VarE v
                     Right c -> ConE c
       rt' <- inst_return rt
       return $ EExp info rt' exp1
     PolyEffect qvars rt -> do
       -- Construct an instance expression with the given type.  Create fresh
       -- variables.
       new_vars <- replicateM (length qvars) $ newFlexibleEffectVar
       let new_rt = foldr (uncurry renameE) rt (zip qvars new_vars)
           exp1 = InstE poly_op (map varEffect new_vars)
       rt' <- inst_return new_rt
       traceShow (text "instantiated" <+> hsep (map pprEffectVar new_vars)) $ return $ EExp info rt' exp1
     RecEffect placeholder rt -> do
       let var = case poly_op 
                 of Left v -> v
                    Right _ -> internalError "instantiateEffectAssignment: Constructor must have known type"
       rt' <- inst_return rt
       return $ EExp info rt' $ RecPlaceholderE var placeholder
  where
    -- Instantiate a monotype.  Locally bound region variables are renamed.
    inst_mono ty =
      case ty
      of AppT op args ->
           AppT `liftM` inst_mono op `ap` mapM inst_mono args
         InstT {} -> return ty
         FunT pt eff rt -> do
           (pt', rn) <- inst_param pt
           eff' <- liftIO $ evalAndApplyRenaming rn eff
           rt' <- inst_return =<< liftIO (evalAndApplyRenaming rn rt)
           return $ FunT pt' eff' rt'
         VarT {} -> return ty
         ConT {} -> return ty
         LitT {} -> return ty

    -- Instantiate a parameter type.  If it binds a region, rename the region.
    -- The new region variable is unifiable.
    inst_param pt = do
      param_type <- inst_mono $ paramTypeType pt
      case pt of
        ValPT mv _ -> return (ValPT mv param_type, idRenaming)
        OwnPT _ -> return (OwnPT param_type, idRenaming)
        ReadPT rgn _ -> do
          rgn' <- newRegionVar True
          return (ReadPT rgn' param_type, Renaming (renameE rgn rgn'))
          
    inst_return rt = do
      ret_type <- inst_mono $ returnTypeType rt
      case rt of
        ValRT _ -> return $ ValRT ret_type
        OwnRT _ -> return $ OwnRT ret_type

        -- Do not rename a 'read' region.  The read region must be equal to   
        -- the region where this value was assigned.
        ReadRT r _ -> do
          return $ ReadRT r ret_type

        -- A 'write' region creates fresh data, so rename it.
        WriteRT rgn _ -> do
          rgn' <- newRegionVar True
          return $ WriteRT rgn' ret_type

-------------------------------------------------------------------------------
-- Subtyping and coercion

-- | A renaming of a dependently typed expression
type DepRenaming = EExp -> Renaming

-- | Perform some computation where a parameter region is in scope.
--   Eliminate the region from generated constraints.
withParamRegion :: RVar -> EI a -> EI a
withParamRegion rv m = transformConstraint eliminate_rv m
  where
    eliminate_rv _ cst free_evars = do
      cst' <- eliminateRigidVariable rv cst
      return (cst', free_evars)

-- | Perform some computation where a parameter region is in scope.
--   Eliminate the region from generated constraints.
withRenamedParamRegion :: Parametric a =>
                          RVar 
                       -> (RVar -> EI (a, b)) 
                       -> EI (a, b)
withRenamedParamRegion rv f = do
  rv' <- newRegionVar False
  unrename rv' =<< transformConstraint (eliminate rv') (f rv')
  where
    eliminate rv' _ cst free_evars = do
      cst' <- eliminateRigidVariable rv' cst
      return (cst', free_evars)
    
    unrename rv' (thing, x) =
      return (renameE rv' rv thing, x)

-- | Unify two regions and perform some computation where the region is in
--   scope.  A fresh region variable will be created.  The worker function
--   should rename its inputs to this fresh region name.
--   After the computation finishes, the region will be eliminated 
--   from constraints and renamed back to its original names.  All return
--   values that should be renamed to the expected region should be returned
--   as the first tuple element.  All return values that should be renamed
--   to the given region should be returned as the second tuple element.
withUnifiedParamRegions :: (Parametric a, Parametric b) =>
                           RVar -- ^ Expected parameter region
                        -> RVar -- ^ Given parameter region
                        -> (RVar -> EI (a, b, c))
                           -- ^ Computation with unified regions
                        -> EI (a, b, c) -- ^ Computation
withUnifiedParamRegions e_rv g_rv f = do
  u_rv <- newRegionVar False
  traceShow (text "withUnifiedParamRegions" <+> pprEffectVar e_rv <+> pprEffectVar g_rv <+> pprEffectVar u_rv) $ unrename u_rv =<< transformConstraint (eliminate u_rv) (f u_rv)
  where
    eliminate u_rv _ cst free_evars = do
      cst' <- eliminateRigidVariable u_rv cst
      return (cst', free_evars)

    unrename u_rv (e_thing, g_thing, x) =
      return (renameE u_rv e_rv e_thing, renameE u_rv g_rv g_thing, x)

withUnifiedParamVariables :: (Parametric a, Parametric b) =>
                             Maybe Var -- ^ Expected parameter variable
                          -> Maybe Var -- ^ Given parameter variable
                          -> (Maybe Var -> EI (a, b, c))
                             -- ^ Computation with unified variables
                          -> EI (a, b, c) -- ^ Computation
withUnifiedParamVariables Nothing Nothing f = f Nothing
withUnifiedParamVariables (Just e_v) Nothing f = f (Just e_v)
withUnifiedParamVariables Nothing (Just g_v) f = f (Just g_v)
withUnifiedParamVariables (Just e_v) (Just g_v) f = do
  u_v <- Gluon.newVar (Gluon.varName e_v) (getLevel e_v)
  (x, y, z) <- f (Just u_v)
  return (renameT u_v e_v x, renameT u_v g_v y, z)

{- Parameter coercions

The job of parameter coercion is to convert the return value and
representation of some expression, GIVEN, to the expected value and
representation of some expression USE.

* Read -> Val or Read -> Owned
USE (coerce_value (loadValue GIVEN))

Has an extra, exposed given load

* Write -> Val or Write -> Owned
USE (coerce_value (loadTemporaryValue GIVEN))
becomes
let tmp = GIVEN
in USE (coerce_value (loadValue tmp))

Has an extra, callsite-local given load

* Read -> Read
USE (coerce_value GIVEN)

* Write -> Read
let tmp = GIVEN
in USE (coerce_value tmp)

Has a callsite-local load

-}


-- | Coerce a function argument.
--
--   The worker function takes a coercion (in terms of the renamed variable),
--   a renaming to apply to the given type, a renaming to apply to the
--   parameter type,
--   the set of regions read by the /expected/ type that were satisfied by 
--   coercions, and the set of regions read by the /given/ type that
--   were satisfied by coercions.
--
--   Returns the new parameter and return types, and the set of
--   callsite-local side effects.
coerceParameter :: (Parametric a, Parametric b) =>
                   EParamType   -- ^ Parameter type (expected)
                -> EReturnType  -- ^ Argument type (given)
                -> (Coercion
                 -> Renaming
                 -> DepRenaming
                 -> [RVar]
                 -> [RVar]
                 -> EI (a, b, c))
                -> EI (EParamType, EReturnType, [RVar], (a, b, c))
coerceParameter expected given f = do
  -- Coerce the parameter value
  (coerce_value, expected', given') <- coerceParameterType expected given

  -- Coerce the representation
  case expected' of
    ValPT mv _ ->
      -- Renaming of dependent variables
      let dep_renaming :: DepRenaming =
            case mv
            of Nothing -> const idRenaming
               Just v  -> \e ->
                 case expExp e
                 of TypeE ty -> Renaming (assignT v ty)
                    _ -> internalError "coerceParameter: Not a type"
      in case given'
         of ValRT _ -> do
              retval <- f coerce_value idRenaming dep_renaming [] []
              return (expected', given', [], retval)
            OwnRT _ -> no_coercion
            ReadRT rv _ -> do
              let co = coerce_value `mappend` genLoadValue
              retval <- f co idRenaming dep_renaming [] [rv]
              return (expected', given', [], retval)
            WriteRT rv _ -> do
              let co = coerce_value `mappend` genTempLoadValue
              retval <- f co idRenaming dep_renaming [] [rv]
              return (expected', given', [rv], retval)
    OwnPT _ ->
      case given'
      of ValRT _ -> no_coercion
         OwnRT _ -> do
           retval <- f coerce_value idRenaming (const idRenaming) [] []
           return (expected', given', [], retval)
         ReadRT rv _ -> do
           let co = coerce_value `mappend` genLoadOwned
           retval <- f co idRenaming (const idRenaming) [] [rv]
           return (expected', given', [], retval)
         WriteRT rv _ -> do
           let co = coerce_value `mappend` genTempLoadOwned
           retval <- f co idRenaming (const idRenaming) [] [rv]
           return (expected', given', [rv], retval)
    ReadPT pv _ ->
      case given'
      of ValRT _ -> do
           let co = genTempStoreValue pv `mappend` coerce_value
           retval <- f co idRenaming (const idRenaming) [pv] []
           return (expected', given', [pv], retval)
         OwnRT _ -> do
           let co = genTempStoreOwned pv `mappend` coerce_value
           retval <- f co idRenaming (const idRenaming) [pv] []
           return (expected', given', [pv], retval)
         ReadRT rv _ -> do
           retval <- withUnifiedParamRegions pv rv $ \pv' ->
             f coerce_value (Renaming $ renameE rv pv') (const $ Renaming $ renameE pv pv') [] []
           return (expected', given', [], retval)
         WriteRT rv _ -> do
           retval <- withUnifiedParamRegions pv rv $ \pv' ->
             f coerce_value (Renaming $ renameE rv pv') (const $ Renaming $ renameE pv pv') [] []
           return (expected', given', [pv], retval)
   where
    no_coercion = internalError "coerceParameter: Cannot coerce"
  
-- | Helper function for coerceParameter
coerceParameterType expected given = do
  (etype, gtype, coerce_value) <-
    compareTypes InDir Covariant (paramTypeType expected) (returnTypeType given)

  let expected' = case expected
                  of ValPT mv _  -> ValPT mv etype
                     OwnPT _     -> OwnPT etype
                     ReadPT rv _ -> ReadPT rv etype
      given' = case given
               of ValRT _      -> ValRT gtype
                  OwnRT _      -> OwnRT gtype
                  ReadRT rv _  -> ReadRT rv gtype
                  WriteRT rv _ -> WriteRT rv gtype

  return (coerce_value, expected', given')

-- | Coerce a return type.
--
-- Returns the coercion and the set of regions that are read by the coercion,
-- and not local to the coercion expression.
coerceReturn :: EReturnType
             -> EReturnType
             -> EI (EReturnType, EReturnType, Coercion, [RVar])
coerceReturn expected given = traceShow (text "coerceReturn" <+> (pprEReturnType expected $$ pprEReturnType given)) $ do
  -- Coerce the value
  (coerce_value, expected', given') <- coerceReturnTypes expected given
  
  -- Coerce the representation
  case expected' of
    ValRT _ ->
      case given'
      of ValRT _ -> return (expected', given', coerce_value, [])
         OwnRT _ -> no_coercion
         ReadRT rv _ ->
           let co = coerce_value `mappend` genLoadValue
           in return (expected', given', co, [rv])
         WriteRT rv _ ->
           let co = coerce_value `mappend` genTempLoadValue
           in return (expected', given', co, [])
    OwnRT _ ->
      case given'
      of ValRT _ -> no_coercion
         OwnRT _ -> return (expected', given', coerce_value, [])
         ReadRT rv _ ->
           let co = coerce_value `mappend` genLoadOwned
           in return (expected', given', co, [rv])
         WriteRT rv _ ->
           let co = coerce_value `mappend` genTempLoadOwned
           in return (expected', given', co, [])
    ReadRT _ _ ->
      internalError "coerceReturn: Cannot coerce to a borrowed read return value"
    WriteRT rv _ ->
      case given'
      of ValRT _ ->
           let co = genStoreValue rv `mappend` coerce_value
           in return (expected', given', co, [])
         OwnRT _ ->
           let co = genStoreOwned rv `mappend` coerce_value
           in return (expected', given', co, [])
         ReadRT gv _ -> do
           return (expected', given', coerce_value, [gv])
         WriteRT gv _ -> do
           return (expected', given', coerce_value, [])
   where
    no_coercion = internalError "coerceReturn: Cannot coerce"
 
coerceReturnTypes expected given = do
  (etype, gtype, co) <-
    compareTypes OutDir Covariant (returnTypeType expected) (returnTypeType given)
  
  return (co, rebuild expected etype, rebuild given gtype)
  where
    rebuild (ValRT _) rt = ValRT rt
    rebuild (OwnRT _) rt = OwnRT rt
    rebuild (ReadRT v _) rt = ReadRT v rt
    rebuild (WriteRT v _) rt = WriteRT v rt

-- | Compare two types.  If the types are not compatible, an error is thrown.
-- Otherwise, a coercion and a set of temporary regions is returned.
--     
-- The types are assumed to have the same representation.  If coercion is
-- required, that should be handled by 'coerceParameter' or 'coerceReturn'.
--
-- The direction determines what kind of coercions to generate.
-- If 'UnDir', no coercions are generated; an error is generated if coercions
-- would be required.
--
-- The variance determines what subtyping relationship to allow. 
-- If 'Covariant', the given type must be a subtype of the expected type.  If
-- 'Contravariant', it is the opposite.
compareTypes :: Direction       -- ^ Direction of data flow
             -> Variance        -- ^ Subtyping relationship
             -> EType           -- ^ Expected type
             -> EType           -- ^ Given type
             -> EI (EType, EType, Coercion)
compareTypes direction variance expected given =
  case (expected, given)
  of (AppT e_op e_args, AppT g_op g_args) -> do
       (e_op', g_op', _) <- compareTypes UnDir variance e_op g_op

       -- If operators match, they take the same number of arguments
       unless (length e_args == length g_args) $
         internalError "compareTypes"

       let variances = etypeOrdinaryParamVariance g_op
       (e_args', g_args', arg_cos) <- compareTypeLists variances e_args g_args
       
       -- Cannot construct a coercion for this type
       unless (all isIdCoercion arg_cos) $
         internalError "compareTypes: Cannot construct coercion for data type"
       return (AppT e_op' e_args', AppT g_op' g_args', mempty)

     (InstT e_op e_effs, InstT g_op g_effs) -> do
       when (e_op /= g_op) type_mismatch
       let variances = case g_op
                       of Right con -> conEffectParamVariance con
                          Left _ -> repeat Invariant
       
       unless (length e_effs == length g_effs &&
               length e_effs == length variances) $
         internalError "compareTypes"
         
       compareEffectLists variances e_effs g_effs
       return (InstT e_op e_effs, InstT g_op g_effs, mempty)

     (FunT {}, FunT {}) -> do
       (co, e_type, g_type) <- compareFunctionTypes expected given
       when (direction == UnDir && not (isIdCoercion co)) $
         internalError "compareTypes: Unhandled coercion"
       return (e_type, g_type, co)

     (VarT e_v, VarT g_v)
       | e_v == g_v -> no_change
       | otherwise -> type_mismatch

     (ConT e_c, ConT g_c)
       | e_c == g_c -> no_change
       | otherwise -> type_mismatch

     (LitT e_l, LitT g_l)
       | e_l == g_l -> no_change
       | otherwise -> type_mismatch
     _ ->
       traceShow (pprEType expected $$ pprEType given) $ internalError "compareTypes"
  where
    no_change = return (expected, given, mempty)
    type_mismatch = fail "Type mismatch"

compareTypeLists variances es gs = go variances es gs 
  where
    go (v:vs) (e:es) (g:gs) = do
      (e', g', co) <- compareTypes UnDir v e g
      (es', gs', cos) <- go vs es gs
      return (e':es', g':gs', co:cos)
    
    go _ [] [] = return ([], [], [])
    go [] _ _ = internalError "compareTypeLists: Variance not given"
    go _ _ _ = internalError "compareTypeLists: List length mismatch"

compareFunctionTypes :: EType   -- ^ Expected type
                     -> EType   -- ^ Given type
                     -> EI (Coercion, EType, EType)
compareFunctionTypes expected given = 
  cftCoerceParameters [] [] [] expected given
  where

cftCoerceParameters :: [(EParamType, Coercion)]
                    -> [RVar]
                    -> [RVar]
                    -> EType
                    -> EType
                    -> EI (Coercion, EType, EType)
cftCoerceParameters rev_cos e_xrs g_xrs expected given =
  case (expected, given)
  of (FunT e_param e_eff e_return, FunT g_param g_eff g_return) -> do
       let epv = paramTypeVariable e_param
           gpv = paramTypeVariable g_param
    
       -- First unify parameter variables
       ((g_eff', g_ret'), (e_eff', e_ret'), (e_param_ret, g_param2, co)) <-
         withUnifiedParamVariables epv gpv $ \mpv -> do
           let e_param1 = rebuild_param mpv e_param
               e_eff1   = renameT_maybe epv mpv e_eff
               e_ret1   = renameT_maybe epv mpv e_return
               g_param1 = rebuild_param mpv g_param
               g_eff1   = renameT_maybe gpv mpv g_eff
               g_ret1   = renameT_maybe gpv mpv g_return

           -- Compute new effect and range types
           coerce_this_parameter e_param1 e_eff1 e_ret1 g_param1 g_eff1 g_ret1

       -- Rebuild the function type
       let e_param' = rebuild_expected_param e_param e_param_ret
           g_param' = rebuild_param gpv g_param2
       return (co, FunT e_param' e_eff' e_ret', FunT g_param' g_eff' g_ret')
  where
    -- Modify the parameter variable
    rebuild_param (Just v) (ValPT (Just _) t) = ValPT (Just v) t
    rebuild_param (Just v) (ValPT Nothing  t) = ValPT Nothing t
    rebuild_param Nothing  p                  = p
    rebuild_param _ _ = internalError "cftCoerceParameters"
    
    -- Rebuild the expected paramter, with the type taken from the return type
    rebuild_expected_param (ValPT mpv _) rt = ValPT mpv (returnTypeType rt)
    rebuild_expected_param (OwnPT _)     rt = OwnPT (returnTypeType rt)
    rebuild_expected_param (ReadPT rv _) rt = ReadPT rv (returnTypeType rt)

    -- Coerce the parameter.  Parameter variables have been renamed so the
    -- bound variable is now the same.
    -- Parameter regions have not been renamed.
    coerce_this_parameter e_param e_eff e_ret g_param g_eff g_ret = do
      -- Construct the coercion from this parameter.  Coerce the value
      -- obtained via the expected parameter to the given parameter.   
      -- Note that the direction of coercion changed
      -- (parameters are contravariant).
      (g_param', e_param_ret, _, (g_range', e_range', co)) <-
        coerceParameter g_param (paramTypeToReturnType e_param) $
        \co e_rn g_dep_rn e_xeff g_xeff ->
        -- Rename the effects and return values
        let e_eff1 = applyRenaming e_rn e_eff
            e_ret1 = applyRenaming e_rn e_ret
            g_eff1 = applyRenaming (g_dep_rn undefined) g_eff
            g_ret1 = applyRenaming (g_dep_rn undefined) g_ret
        in coerce_next_parameter
           ((e_param, co) : rev_cos)
           (e_xeff ++ e_xrs)
           (g_xeff ++ g_xrs)
           e_eff1 e_ret1 g_eff1 g_ret1

      -- Swap order of return values to go back to the original coercion
      -- direction.  Needed for renaming of return values.
      return (g_range', e_range', (e_param_ret, g_param', co))

    coerce_next_parameter rev_cos e_xeff g_xeff e_eff e_return g_eff g_return =
      case (e_return, g_return)
      of (OwnRT e_ftype@(FunT {}), OwnRT g_ftype@(FunT {}))
           -- FIXME: Use evaluate-me tags to determine where to end the
           -- coercion function, instead of this hack
           
           -- If given side effect is literally the empty effect,
           -- then this isn't the end of the function.  Continue coercing
           -- parameters
           | isEmptyEffect g_eff -> do
               assertEmptyEffect e_eff
               (co, e_ftype', g_ftype') <-
                 cftCoerceParameters rev_cos e_xeff g_xeff e_ftype g_ftype
               return ((emptyEffect, OwnRT e_ftype'),
                       (emptyEffect, OwnRT g_ftype'),
                       co)
         _ ->
           cftCoerceReturn rev_cos e_xeff g_xeff e_eff e_return g_eff g_return

cftCoerceReturn rev_cos e_xeff g_xeff e_eff e_return g_eff g_return = do
  -- The actual effect consists of the given effect and effects produced
  -- by coercion
  let co_g_eff = effectUnion g_eff (varsEffect g_xeff)

  -- Create a relationship between the given and expected effects. 
  -- In the absence of coercions, the given expect must be a
  -- subeffect of the expected effect.
  -- We can exclude coercion-induced reads from the expected effect
  -- and coercion-created local regions from the given effect.
  assertSubeffect
    (deleteListFromEffect e_xeff g_eff)
    (deleteListFromEffect g_xeff e_eff)

  -- Coerce from given return type to expected return type
  (e_return', g_return', ret_co, ret_eff) <- coerceReturn e_return g_return
  
  -- If all coercions are identities, then return the identity coercion
  coercion <-
    if all isIdCoercion [c | (_, c) <- rev_cos] && isIdCoercion ret_co
    then return mempty
    else cftFunctionCoercion (reverse rev_cos) ret_co e_return g_eff g_return

  return ((g_eff, g_return), (e_eff, e_return), coercion)

paramTypeVariable (ValPT (Just v) _) = Just v
paramTypeVariable _ = Nothing

renameT_maybe Nothing   Nothing   x = x
renameT_maybe (Just v1) (Just v2) x = renameT v1 v2 x

cftFunctionCoercion param_coercions return_coercion e_return g_eff g_return = do
  -- Create function parameters
  params <- liftRegionM $ forM param_coercions $ \(param_type, co) -> do 
    param <- mkParamFromTypeParam param_type
    return (param, co)

  return (coercion $ mk_coercion params)
  where
    mk_coercion params g_expr =
      -- Create a call to the given expression
      let param_arguments =
            [applyCoercion c $ paramVarExp p | (p, c) <- params]
          info = mkSynInfo (getSourcePos $ expInfo g_expr) ObjectLevel
          call = EExp { expInfo = info
                      , expReturn = g_return
                      , expExp = CallE g_expr param_arguments
                      }

          -- Coerce the call's return value
          ret_expr = applyCoercion return_coercion call
          
          function = EFun { funInfo = info
                          , funEffectParams = []
                          , funParams = [p | (p, _) <- params]
                          , funReturnType = e_return
                          , funEffect = g_eff
                          , funBody = ret_expr
                          }
          function_type =
            OwnRT
            (discardTypeRepr $ funMonoEType (map fst params) g_eff e_return)
      in EExp info function_type (FunE function)

compareEffectLists variances es gs = go variances es gs 
  where
    go (v:vs) (e:es) (g:gs) = do
      compareEffects v e g
      go vs es gs
    
    go _ [] [] = return ()
    go [] _ _ = internalError "compareEffectLists: Variance not given"
    go _ _ _ = internalError "compareEffectLists: List length mismatch"

compareEffects Covariant e_eff g_eff = assertSubeffect g_eff e_eff
compareEffects Invariant e_eff g_eff = assertEqualEffect g_eff e_eff
compareEffects Contravariant e_eff g_eff = assertSubeffect e_eff g_eff

-------------------------------------------------------------------------------
-- Top-level effect inference routines

inferTopLevel :: [SF.DefGroup SF.TypedRec]
              -> [SF.Export SF.TypedRec]
              -> EI ([EDefGroup], [EExport])
inferTopLevel (dg:dgs) exports = do
  (dg', (dgs', exports')) <- inferDefGroupOver dg $ inferTopLevel dgs exports
  return (dg' : dgs', exports')

inferTopLevel [] exports = do
  exports' <- mapM inferExport exports
  return ([], exports')

inferModule :: SF.Module SF.TypedRec
            -> EI (ModuleName, [EDefGroup], [EExport])
inferModule (SF.Module module_name defss exports) = do
  ((defss', exports'), cst) <- extractConstraint $ inferTopLevel defss exports

  -- No constraints should remain
  liftRegionM $ solveGlobalConstraint cst

  -- DEBUG: force effects
  -- defss'' <- liftIO $ forceEffects defss'
  -- exports'' <- liftIO $ mapM forceExportEffects exports'

  -- DEBUG: print the module
  -- liftIO $ putStrLn "Effect inference"
  -- liftIO $ print $ vcat $ map pprDefGroup defss''
  return (module_name, defss', exports')

inferSideEffects :: SF.Module SF.TypedRec -> IO (Core.CModule Rec)
inferSideEffects mod = do
  evar_ids <- newIdentSupply
  
  (region_var_map, module_name, defss, exports) <-
    withTheVarIdentSupply $ \var_ids -> do
      -- Initialize some global data that is used during effect inference
      (region_var_map, con_region_map) <-
        runRegionM evar_ids var_ids mkGlobalRegions

      -- Run effect inference
      (module_name, defss, exports) <-
        runEffectInference evar_ids var_ids con_region_map $ inferModule mod

      return (region_var_map, module_name, defss, exports)
    
  -- DEBUG: print definitions
  forced_defss <- mapM (mapM forceEDef) defss
  print $ vcat $ map pprEDefs forced_defss
  print $ vcat $ map pprEExport exports
  
  -- Generate a core module
  core_module <- generateCore region_var_map module_name defss exports
  
  -- DEBUG
  print $ Core.pprCModule core_module
  
  return core_module