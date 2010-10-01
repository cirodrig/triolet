
{-# LANGUAGE FlexibleInstances, ViewPatterns, Rank2Types #-}
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

  assumeEffect v m = trace "assumeEffect" $ assertEVar v $ EI $ \env ->
    let region_env' =
          (efRegionEnv env) {reRegionEnv =
                                Set.insert v $ reRegionEnv $ efRegionEnv env}
        env' = env {efRegionEnv = region_env'}
    in runEI m env'

  getRigidEffectVars = EI $ \env -> returnEI $ reRegionEnv $ efRegionEnv env

runEffectInference evar_ids var_ids m = do
  let renv = RegionEnv evar_ids var_ids Set.empty
      env = EffectEnv renv (IntMap.empty)
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

-- | Record that a new effect variable was created
tellNewEffectVar :: EffectVar -> EI ()
tellNewEffectVar v = EI $ \env -> return ((), mempty, Endo (v:))

-- | Create a new effect variable that does not have a binding.  The variable 
-- will either be unified with something else or assigned a binding during
-- generalization.
newFlexibleEffectVar :: EI EffectVar
newFlexibleEffectVar = do v <- newEffectVar
                          tellNewEffectVar v
                          return v

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
  traceShow (text "inferExp" <+> SF.pprExp (eraseTypeAnnotations typed_expression)) $ do
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

-- | Convert a type from System F's type inference pass
fromInferredType :: SF.TRType -> EI EExp
fromInferredType (SF.TypedSFType (SF.TypeAnn k t)) = do
  t' <- liftRegionM $ toEffectType =<< evalHead' t
  kind <- liftRegionM $ toEffectType =<< evalHead' (Gluon.fromWhnf k)
  let info = Gluon.internalSynInfo (getLevel t')
  return_type <- liftRegionM $ etypeToReturnType kind
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
  
  -- DEBUG
  liftIO $ print (text "inferConE" <+> (text $ showLabel $ Gluon.conName c) <+> (Core.pprType (Core.conCoreType c) $$ pprERepType eff_type))
  
  -- Create an expression
  let exp1 = if null eff_qvars
             then ConE c
             else InstE (Right c) (map varEffect eff_qvars)
  rt <- trace "inferConE2" $ liftRegionM $ etypeToReturnType eff_type
  trace "inferConE1" $ return (EExp inf rt exp1, emptyEffect)

inferLitE ty inf lit = liftRegionM $ do
  ty' <- toEffectType =<< evalHead' (Gluon.fromWhnf ty)
  return_ty <- etypeToReturnType ty'
  -- Literal value has no side effect and returns by value
  return (EExp inf return_ty (LitE lit (discardTypeRepr ty')), emptyEffect)

-- | Effect inference on a stream constructor (\"do\").  Since streams are
-- lazy, always return the empty effect.  The body's side effect appears in
-- the type of the stream that is created.
inferDo :: SynInfo -> [EExp] -> [(EExp, Effect)] -> EI (EExp, Effect)
inferDo inf [return_type] [(repr_exp, repr_eff), (body_exp, body_eff)] = do
  -- Type class expressions should never have a side effect
  assertEmptyEffect repr_eff
  
  let expr = DoE { expTyArg = return_type
                 , expPassConv = repr_exp
                 , expBody = body_exp
                 }
  let stream_type = AppT (InstT stream_con [body_eff]) [returnTypeType $ expReturn body_exp]
  stream_return_type <-
    liftRegionM $ etypeToReturnType $ etypeWithStandardRepr stream_type

  return (EExp inf stream_return_type expr, emptyEffect)
  where
    stream_con = Right (SF.pyonBuiltin SF.the_LazyStream)

inferDo _ _ _ =
  internalError "inferDo: Invalid stream constructor found in effect inference"

-- | During function application, keep track of local regions created due to
-- parameter passing coercions.  The lifetime of a local region is limited to
-- the function call that uses the region; effects on the region are not
-- visible outside that region.
type LocalRegions = [RVar]

inferApp :: Gluon.WRExp
         -> SynInfo 
         -> (EExp, Effect)
         -> [(EExp, Effect)]
         -> EI (EExp, Effect)
inferApp result_type info (op, op_effect) (unzip -> (args, arg_effects)) = 
 traceShow (text "inferApp" <+> vcat (map pprEExp (op : args))) $ do
  let variances = expVariance op
  -- Compute side effects of function application and coerce arguments
  (args', app_effect, local_regions, return_type) <-
    applyArguments (expReturn op) args

  -- Delete local regions from the side effect
  let app_effect' = deleteListFromEffect local_regions app_effect
  
  -- Add effects of operands
  let effect = effectUnions $ app_effect' : op_effect : arg_effects
  
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
               -> EI ([EExp], Effect, LocalRegions, EReturnType)
applyArguments oper_type args = go oper_type init_acc args
  where
    go (OwnRT fun_type) acc (arg : args) = do
      (arg', eff, return_type, local_regions) <-
        applyType fun_type arg
      go return_type (add_acc acc arg' eff local_regions) args
    
    -- If applying an argument, the function type must be owned
    go _ _ (_:_) = internalError "applyArguments: Expecting owned type"
    
    go oper_type (args, eff, local_regions) [] =
      return (reverse args, eff, local_regions, oper_type)

    -- Accumulate the result of applying one argument.
    add_acc (args, eff, rgns) new_arg new_eff new_rgns =
      (new_arg : args, eff `effectUnion` new_eff, rgns ++ new_rgns)
      
    -- Initially, there is no side effect.
    init_acc = ([], emptyEffect, [])

-- | Compute the result of a function application.
--
-- Returns the coerced argument, the application's result type, 
-- the side effect of the application, and an effect transformation that
-- masks out effects on any locally created memory.
applyType :: EType              -- ^ Operator type
          -> EExp               -- ^ Argument
          -> EI (EExp, Effect, EReturnType, LocalRegions)
applyType op_type arg = debug $
  case op_type
  of FunT param_type eff return_type -> do
       (coercion, co_eff, subst, local_regions) <-
         coerceParameter Covariant param_type arg_type
       let arg' = applyCoercion coercion arg
           
       -- Rename return type based on dependent parameters
       return_type' <- liftIO $ evalAndApplyRenaming (subst arg) return_type
       
       -- Rename effect type, and add the coercion's effect
       eff' <- liftIO $ evalAndApplyRenaming (subst arg) eff
       let eff'' = eff' `effectUnion` co_eff
       -- DEBUG
       liftIO $ print $ pprEExp arg'
       return (arg', eff'', return_type', local_regions)
     FunT _ _ _ -> internalError "applyType: Unexpected function representation"
     _ -> internalError "applyType: Not a function type"
  where
    arg_type = expReturn arg

    debug m = do 
      op_type_f <- liftIO $ forceEType op_type
      arg_f <- liftIO $ forceEExp arg
      ret@(_, eff, rt, _) <- m
      eff_f <- liftIO $ evalEffect eff
      rt_f <- liftIO $ forceEReturnType rt
      liftIO $ print $
        text "applyType" <+> (braces (pprEType op_type_f) $$
                              braces (pprEExp arg_f) $$
                              pprEffect eff_f $$
                              pprEReturnType rt_f)
      return ret

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
      return_type <- liftRegionM $
                     etypeToReturnType =<< toEffectType =<< evalHead' (Gluon.fromWhnf case_type)
      (alts, effs) <- mapAndUnzipM (inferAlt (Just return_type)) alts
      return (alts, effs, return_type)

tyPatAsBinder :: SF.TyPat SF.TypedRec -> EI EParam
tyPatAsBinder (SF.TyPat v (SF.TypedSFType (SF.TypeAnn _ ty))) = do
  param_type <- liftRegionM $ toEffectType =<< evalHead' ty
  return $ ValP v $ discardTypeRepr param_type

patternAsBinder :: SF.Pat SF.TypedRec -> EI EParam
patternAsBinder (SF.VarP v (SF.TypedSFType (SF.TypeAnn _ ty))) = do
  param_type <- liftRegionM $ do
    ty' <- evalHead' ty
    etype <- toEffectType ty'
    etypeToParamType etype Nothing -- Value parameters aren't used dependently
  return $! case param_type
            of ValPT _ ty -> ValP v ty
               OwnPT ty -> OwnP v ty
               ReadPT rgn ty -> ReadP v rgn ty

patternAsBinder _ = internalError "patternAsBinder"

patternsAsBinders = mapM patternAsBinder

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
  val_params <- patternsAsBinders $ SF.funParams f
  let params = ty_params ++ val_params
  
  -- Convert return type
  return_type <-
    liftRegionM $
    etypeToReturnType =<< toEffectType =<< evalHead' (fromTRType $ SF.funReturnType f)
    
  -- Create a new variable for the effect type
  effect_type <- newEffectVar
  
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
  val_params <- patternsAsBinders $ SF.funParams f
  let params = ty_params ++ val_params

  (fun_type, body, body_eff, return_type) <- withBinders params $ do
    (fun_type, body, body_eff) <-
      -- Eliminate constraints on flexible variables if this function is going 
      -- to be generalized.  Otherwise, don't because it creates more
      -- variables.
      if is_lambda
      then infer_function_body params
      else prepare_for_generalization (infer_function_body params)
    return_type <-
      liftRegionM $ etypeToReturnType =<< toEffectType =<< evalHead' (fromTRType $ SF.funReturnType f)
    return (fun_type, body, body_eff, return_type)
  
  let new_fun = EFun { funInfo = SF.funInfo f
                     , funEffectParams = []
                     , funParams = params
                     , funReturnType = return_type
                     , funEffect = body_eff
                     , funBody = body
                     }
  return (fun_type, new_fun)
  where
    infer_function_body params = do
      (body, body_eff) <- inferExp $ SF.funBody f
      
      -- Create and return the function's type.  It will be used for
      -- generalization.
      let fun_type = funMonoEType params body_eff (expReturn body)
      return (fun_type, body, body_eff)
  
    -- Make all flexible variables in the function body independent of one
    -- another.  Clear all flexible variables that don't escape in the return 
    -- type.
    prepare_for_generalization infer_body = 
      transformConstraint mfvi infer_body
      where
        mfvi return_value@(fun_type, body, body_eff) cst vs = do
          let get_free_vars = do
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
  params <- sequence [patternAsBinder (SF.VarP v ty)
                     | SF.Binder v ty () <- SF.altParams alt]
  let local_regions = mapMaybe paramRegion params

  (body_exp, body_eff) <- withBinders params $ do
    (body_exp, body_eff) <- inferExp $ SF.altBody alt
  
    -- Coerce return value
    body_exp' <- coerce_return mreturn_type body_exp

    -- Pattern-bound variable effects must not escape
    whenM (liftIO $ expReturn body_exp' `mentionsAnyE` Set.fromList local_regions) $
      fail "inferAlt: Local region escapes"

    -- Hide effects on pattern-bound variables
    let eff = deleteListFromEffect local_regions body_eff
    return (body_exp', eff)

  let con = SF.altConstructor alt
  return (EAlt con (map discardTypeRepr ty_args) params body_exp, body_eff)
  where
    coerce_return Nothing e = return e
    coerce_return (Just rt) e = do
      (coercion, local_regions) <- coerceReturn Covariant rt (expReturn e)
      return $ applyCoercion coercion e

inferTypeExp :: SF.RecType SF.TypedRec -> RegionM ERepType
inferTypeExp (SF.TypedSFType (SF.TypeAnn k t)) =
  toEffectType =<< evalHead' t

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
       traceShow (text "IEA" <+> hcat (map pprEffectVar new_vars)) $ return $ EExp info rt' exp1
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
          -- DEBUG print region
          liftIO $ print $ text "Instantiating return region" <+> pprEffectVar r <+> text (show $ isFlexible' r)
          return $ ReadRT r ret_type

        -- A 'write' region creates fresh data, so rename it.
        WriteRT rgn _ -> do
          rgn' <- newRegionVar True
          return $ WriteRT rgn' ret_type

-------------------------------------------------------------------------------
-- Subtyping and coercion

-- | A renaming of a dependently typed expression
type DepRenaming = EExp -> Renaming

noRenaming _ = Renaming id

-- | Rename a dependent variable to the given type
renameToType :: Var -> DepRenaming
renameToType v e =
  case expExp e
  of TypeE ty -> Renaming (assignT v ty)
     _ -> internalError "renameToType: Not a type"

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
             -> EI Coercion
compareTypes direction variance expected given =
  case (expected, given)
  of (AppT e_op e_args, AppT g_op g_args) -> do
       _ <- compareTypes UnDir variance e_op g_op
       
       -- If operators are equal, they take the same number of arguments
       unless (length e_args == length g_args) $
         internalError "compareStandardTypes"

       let variances = etypeOrdinaryParamVariance g_op
       compareTypeLists UnDir variances e_args g_args
       return mempty

     (InstT e_op e_effs, InstT g_op g_effs) -> do
       when (e_op /= g_op) type_mismatch
       let variances = case g_op
                       of Right con -> conEffectParamVariance con
                          Left _ -> repeat Invariant
       
       unless (length e_effs == length g_effs &&
               length e_effs == length variances) $
         internalError "compareStandardTypes"
         
       compareEffectLists variances e_effs g_effs
       return mempty

     (FunT {}, FunT {}) -> do
       co <- compareFunctionTypes variance expected given
       when (direction == UnDir && not (isIdCoercion co)) $
         internalError "compareStandardTypes: Unhandled coercion"
       return co

     (VarT e_v, VarT g_v)
       | e_v == g_v -> no_change
       | otherwise -> type_mismatch

     (ConT e_c, ConT g_c)
       | e_c == g_c -> no_change
       | otherwise -> type_mismatch

     (LitT e_l, LitT g_l)
       | e_l == g_l -> no_change
       | otherwise -> type_mismatch
  where
    no_change = return mempty
    type_mismatch = traceShow (pprEType expected $$ pprEType given) $ fail "Type mismatch"

compareTypeLists direction variances es gs = go variances es gs 
  where
    go (v:vs) (e:es) (g:gs) = do
      compareTypes direction v e g
      go vs es gs
    
    go _ [] [] = return ()
    go [] _ _ = internalError "compareEffectLists: Variance not given"
    go _ _ _ = internalError "compareEffectLists: List length mismatch"

compareEffectLists variances es gs = go variances es gs 
  where
    go (v:vs) (e:es) (g:gs) = do
      compareEffects v e g
      go vs es gs
    
    go _ [] [] = return ()
    go [] _ _ = internalError "compareTypeLists: Variance not given"
    go _ _ _ = internalError "compareTypeLists: List length mismatch"

-- | Handle the function case for 'compareTypes'.
--
-- If a coercion is generated, it will be a lambda function that calls the
-- original expression.  In the lambda function body, the function arguments 
-- are coerced from expected to given type, then the original function is
-- called, then the result is coerced from given to expected type.
compareFunctionTypes variance expected given =
  coerce_parameters [] [] expected given
  where
    -- Coerce function parameters.  Accumulate a list of coercions and a list
    -- of local regions.
    coerce_parameters rev_cos local_regions
      (FunT e_param e_eff e_return)
      (FunT g_param g_eff g_return) = do
        -- Coerce this parameter
        (co, co_eff, mk_renaming, param_local_regions) <-
          coerceParameter Covariant g_param (paramTypeToReturnType e_param)

        -- Rename the dependent parameter variable in the expected type
        (e_type_param', e_renaming) <-
          liftRegionM $ freshenParamTypeTypeParam e_param
        e_eff' <- liftIO $ evalAndApplyRenaming e_renaming e_eff
        e_return' <- liftIO $ evalAndApplyRenaming e_renaming e_return
        
        -- Create function parameter
        e_param <- liftRegionM $ mkParamFromTypeParam e_type_param'
        let param_exp = paramVarExp e_param
            
        -- Rename the dependent parameter variable in the given type
        let g_renaming = mk_renaming param_exp
        g_return' <- liftIO $ evalAndApplyRenaming g_renaming g_return
        g_eff' <- liftIO $ evalAndApplyRenaming g_renaming g_eff
        
        -- Add the coercion effect
        let g_eff'' = effectUnion g_eff' co_eff

        -- Continue with remaining parameters
        coerce_next_parameter ((e_param, co) : rev_cos)
          (param_local_regions ++ local_regions)
          e_eff' e_return' g_eff'' g_return'

    coerce_parameters _ _ _ _ = internalError "compareFunctionTypes"
    
    coerce_next_parameter rev_cos local_regions e_eff e_return g_eff g_return =
      case (e_return, g_return)
      of (OwnRT e_ftype@(FunT {}), OwnRT g_ftype@(FunT {}))
           -- FIXME: Use evaluate-me tags to determine where to end the
           -- coercion function, instead of this hack
           
           -- If given side effect is literally the empty effect,
           -- then this isn't the end of the function.  Continue coercing
           -- parameters
           | isEmptyEffect g_eff -> do
               assertEmptyEffect e_eff
               coerce_parameters rev_cos local_regions e_ftype g_ftype
         _ ->
           coerce_returns rev_cos local_regions e_eff e_return g_eff g_return

    coerce_returns rev_cos local_regions e_eff e_return g_eff g_return = do
      -- Given effect must be a subeffect of expected effect
      assertSubeffect g_eff e_eff

      -- Coerce from given return type to expected return type
      (ret_co, ret_regions) <- coerceReturn Covariant e_return g_return

      -- If all coercions are identities, then return the identity coercion
      if all isIdCoercion [c | (_, c) <- rev_cos] && isIdCoercion ret_co
        then if null ret_regions
             then return mempty
             else internalError "compareFunctionTypes"
        else do
          -- Remove local regions from the side effect
          let all_local_regions = ret_regions ++ local_regions
              exposed_effect = deleteListFromEffect all_local_regions g_eff

          -- Local regions must not be mentioned in the return type
          liftIO $ whenM (e_return `mentionsAnyE` Set.fromList all_local_regions) $
            fail "Effect produced on a variable outside its scope"
          
          return $ coercion $
                   coerce_expr (reverse rev_cos) ret_co g_return exposed_effect e_return

    -- Construct the actual function coercion.  The coercion wraps a function 
    -- in a lambda function that coerces the argument and return values
    coerce_expr params ret_co original_ret_type eff_type ret_type original_expr =
      let param_arguments =
            [applyCoercion c $ paramVarExp p | (p, c) <- params]
          info = mkSynInfo (getSourcePos $ expInfo original_expr) ObjectLevel
          call = EExp { expInfo = info
                      , expReturn = original_ret_type
                      , expExp = CallE original_expr param_arguments
                      }
          ret_expr = applyCoercion ret_co call
          function = EFun { funInfo = info
                          , funEffectParams = []
                          , funParams = [p | (p, _) <- params]
                          , funReturnType = ret_type
                          , funEffect = eff_type 
                          , funBody = ret_expr
                          }
      in EExp info ret_type (FunE function)

-- | Determine how to coerce an expression that is used as a parameter to 
-- a function call.
--
-- Based on the parameter passing conventions involved, we may insert
-- parameter-passing convention coercions.  Functions may get wrapped in
-- a lambda term.  If the parameter inhabits a region, the region will be
-- unified with something.  The coercion may induce a side effect, which is
-- returned along with the coercion.
coerceParameter :: Variance
                -> EParamType
                -> EReturnType 
                -> EI (Coercion, Effect, DepRenaming, LocalRegions)
coerceParameter variance p_passtype r_passtype =
  traceShow (text "coerceParameter" <+> (pprEParamType p_passtype $$
                                         pprEReturnType r_passtype)) $ do
  -- Coerce the value if its type has changed
  astype <- compareTypes InDir variance (paramTypeType p_passtype) (returnTypeType r_passtype)

  -- Combine the type coercion with a parameter-passing coercion
  case p_passtype of
    ValPT mv p_type ->
      let renaming = case mv
                     of Nothing -> noRenaming
                        Just depvar -> renameToType depvar
                     
          val_coercion c e r = return (c, e, renaming, r)
      in case r_passtype
         of ValRT {} -> val_coercion astype emptyEffect []
            OwnRT {} -> no_coercion
            ReadRT rv r_type ->
              val_coercion (astype `mappend` genLoadValue) (varEffect rv) []
            WriteRT rv r_type ->
              val_coercion (astype `mappend` genTempLoadValue) emptyEffect [rv]
    OwnPT p_type ->
      case r_passtype
      of ValRT {} -> no_coercion
         OwnRT {} -> coercion astype emptyEffect []
         ReadRT rv r_type -> coercion (astype `mappend` genLoadOwned) (varEffect rv) []
         WriteRT rv r_type -> coercion (astype `mappend` genTempLoadOwned) emptyEffect [rv]
    ReadPT pv p_type ->
      case r_passtype
      of ValRT {} -> coercion (genTempStoreValue pv `mappend` astype) emptyEffect [pv]
         OwnRT {} -> coercion (genTempStoreOwned pv `mappend` astype) emptyEffect [pv]
         ReadRT rv r_type -> do
           liftIO $ unifyRegionVars pv rv
           coercion astype (varEffect rv) []
         WriteRT rv r_type -> do
           liftIO $ unifyRegionVars pv rv
           coercion astype emptyEffect [rv]
  where
    coercion f e params = return (f, e, noRenaming, params)
    no_coercion = internalError "coerceParameter: Cannot coerce"

-- | Determine how to coerce an expression that is returned from a statement
-- or function call.
coerceReturn :: Variance -> EReturnType -> EReturnType -> EI (Coercion, LocalRegions)
coerceReturn variance expect_type given_type = do
  -- Coerce the value if its effect type has changed
  astype <- compareTypes OutDir variance (returnTypeType expect_type) (returnTypeType given_type)

  -- Combine the type coercion with a parameter-passing coercion
  case expect_type of
    ValRT e_type ->
      case given_type
      of ValRT g_type -> coercion astype []
         OwnRT _ -> no_coercion
         ReadRT rv r_type ->
           coercion (astype `mappend` genLoadValue) []
         WriteRT rv r_type ->
           coercion (astype `mappend` genTempLoadValue) [rv]
    OwnRT e_type ->
      case given_type
      of ValRT _ -> no_coercion
         OwnRT _ -> coercion astype []
         ReadRT rv r_type ->
           coercion (astype `mappend` genLoadOwned) []
         WriteRT rv r_type ->
           coercion (astype `mappend` genTempLoadOwned) [rv]
    ReadRT {} ->
      internalError "coerceReturn: Cannot coerce to a borrowed read return value"
    WriteRT rv e_type ->
      case given_type
      of ValRT g_type -> coercion (genStoreValue rv `mappend` astype) []
         OwnRT g_type -> coercion (genStoreOwned rv `mappend` astype) []
         ReadRT gv g_type -> do
           liftIO $ unifyRegionVars rv gv
           coercion astype []
         WriteRT gv g_type -> do
           liftIO $ unifyRegionVars rv gv
           coercion astype []
  where
    coercion c rgns = return (c, rgns)
    no_coercion = internalError "coerceReturn: Cannot coerce"

compareEffects Covariant e_eff g_eff = assertSubeffect g_eff e_eff
compareEffects Invariant e_eff g_eff = assertEqualEffect g_eff e_eff
compareEffects Contravariant e_eff g_eff = assertSubeffect e_eff g_eff

requireEqual = compareTypes UnDir Invariant

-------------------------------------------------------------------------------
-- Top-level effect inference routines

inferTopLevel :: [SF.DefGroup SF.TypedRec]
              -> [SF.Export SF.TypedRec]
              -> EI ([EDefGroup], ())
inferTopLevel (dg:dgs) exports = do
  (dg', (dgs', exports')) <- inferDefGroupOver dg $ inferTopLevel dgs exports
  return (dg' : dgs', exports')

inferTopLevel [] exports = do
  return ([], ())

inferModule :: SF.Module SF.TypedRec
            -> EI (ModuleName, [EDefGroup], ())
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
  return (module_name, defss', ())

inferSideEffects :: SF.Module SF.TypedRec
                 -> IO (ModuleName, [EDefGroup], ())
inferSideEffects mod = do
  evar_ids <- newIdentSupply
  
  (module_name, defss, ()) <- withTheVarIdentSupply $ \var_ids ->
    runEffectInference evar_ids var_ids $ inferModule mod
    
  -- DEBUG: print definitions
  forced_defss <- mapM (mapM forceEDef) defss
  print $ vcat $ map pprEDefs forced_defss
  
  return (module_name, defss, ())