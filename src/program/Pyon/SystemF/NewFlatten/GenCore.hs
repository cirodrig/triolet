
{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, ViewPatterns #-}
module Pyon.SystemF.NewFlatten.GenCore(flatten)
where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.ST
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.Label
import Gluon.Common.SourcePos
import Gluon.Common.Supply
import Gluon.Common.MonadLogic
import Gluon.Core
import Gluon.Core.Builtins
import qualified Gluon.Core.Builtins.Effect
import qualified Pyon.SystemF.Syntax as SystemF
import Pyon.SystemF.Builtins
import qualified Pyon.SystemF.Typecheck as SystemF
import qualified Pyon.SystemF.NewFlatten.PassConv
import Pyon.SystemF.NewFlatten.PassConv
import qualified Pyon.SystemF.NewFlatten.SetupEffect as Effect

import Pyon.Core.Syntax
import Pyon.Core.Print
import Pyon.Globals

type EffectType = RecCType Rec

emptyEffectType :: EffectType
emptyEffectType = expCT Gluon.Core.Builtins.Effect.empty

readEffectType :: RExp -> RCType -> EffectType
readEffectType addr ty =
  let at = mkInternalConE $ builtin the_AtE
  in appByValue at [expCT addr, ty]

unionEffect :: EffectType -> EffectType -> EffectType
unionEffect t1 t2 =
  let sconj = mkInternalConE $ builtin the_SconjE 
  in appCT sconj [(ByValue, t1), (ByValue, t2)]

unionEffects :: [EffectType] -> EffectType
unionEffects [] = emptyEffectType
unionEffects es = foldr1 unionEffect es

-------------------------------------------------------------------------------
-- Monad for translating result of effect inference

newtype EffEnv a = EffEnv {runEffEnv :: ReaderT Env IO a}
                 deriving(Monad, MonadIO)

data Env = Env { -- | Each region variable is mapped to an address variable,
                 --   a pointer variable, and a type.
                 regionEnv :: Map.Map RVar (AddrVar, PtrVar, RCType)
                 -- | Each effect variable is mapped to a Gluon variable.
               , effectEnv :: Map.Map EVar Var
                 -- | Parameter-passing convention dictionaries
               , passConvEnv :: [(RCType, Var)]
               , varSupply :: {-# UNPACK #-}!(IdentSupply Var)
               }

instance Supplies EffEnv (Ident Var) where
  fresh = EffEnv $ ReaderT $ \env -> supplyValue $ varSupply env
  supplyToST f = EffEnv $ ReaderT $ \env ->
    stToIO (f (unsafeIOToST $ supplyValue $ varSupply env))

-- | Translate a region variable to a Gluon variable.
withNewRegionVariable :: RVar   -- ^ Region variable
                      -> PtrVar -- ^ Pointer-to-region variable
                      -> RCType -- ^ Type stored in region
                      -> (AddrVar -> EffEnv a) -- ^ Continuation
                      -> EffEnv a
withNewRegionVariable region_var ptr_var region_ty f = assertRVar region_var $ do
  addr_var <- newVar (effectVarName region_var) ObjectLevel

  let val = (addr_var, ptr_var, region_ty)
      insert_var env =
        env {regionEnv = Map.insert region_var val $ regionEnv env}

  val `seq` EffEnv $ local insert_var $ runEffEnv (f addr_var)

-- | Translate an effect variable to a Gluon variable.
withNewEffectVariable :: EVar -> (Var -> EffEnv a) -> EffEnv a
withNewEffectVariable effect_var f = assertEVar effect_var $ do
  var <- newVar (effectVarName effect_var) ObjectLevel
  
  let insert_var env =
        env {effectEnv = Map.insert effect_var var $ effectEnv env}

  EffEnv $ local insert_var $ runEffEnv (f var)

-- | If the given type is a @PassConv@ object, add it to the local environment.
-- This function is called by 'convertParameter' to keep track of dictionaries
-- that may be needed during flattening.
withParameterVariable :: Var    -- ^ Parameter variable
                       -> RCType -- ^ Parameter's type
                       -> EffEnv a
                       -> EffEnv a
withParameterVariable v ty m =
  case ty
  of AppCT {ctOper = ConE {expCon = con}, ctArgs = args}
       | con `isPyonBuiltin` the_PassConv ->
           case args
           of [(_, t)] ->
                let insert_var env =
                      env {passConvEnv = (t, v) : passConvEnv env}
                in EffEnv $ local insert_var $ runEffEnv m
              _ -> traceShow (pprType ty) $ internalError "withParameterVariable"
     _ -> m

-- | Print the known environment of passing convention values.  For debugging.
tracePassConvEnv :: EffEnv a -> EffEnv a
tracePassConvEnv m = EffEnv $ do
  env <- asks passConvEnv
  traceShow (print_env env) $ runEffEnv m
  where
    print_env env =
      hang (text "PassConv variables") 8 $ vcat $ map print_pc env
    
    print_pc (t, v) =
      hang (pprVar v) 6 $ pprType t

lookupRegion :: RVar -> EffEnv (AddrVar, PtrVar, RCType)
lookupRegion rv = assertRVar rv $ EffEnv $ asks $ \env ->
  case Map.lookup rv $ regionEnv env
  of Just x -> x
     Nothing -> internalError "convertRegion: No region"

-------------------------------------------------------------------------------
-- Type conversion

convertEffect :: Effect -> EffEnv EffectType
convertEffect eff = do
  -- Get the variables mentioned by the effect
  effect_vars <- liftIO $ fromEffect eff

  -- Convert to a conjunction of region and effect variables.
  -- Look up each variable, then build a conjunction expression.
  env <- EffEnv ask
  
  return $ unionEffects $ map (lookup env) effect_vars
  where
    lookup env v
      | isRVar v =
          case Map.lookup v $ regionEnv env
          of Just (v, _, ty) -> readEffectType (mkInternalVarE v) ty
             Nothing -> cannot_find_variable v
      | otherwise = 
          case Map.lookup v $ effectEnv env
          of Just v -> expCT $ mkInternalVarE v
             Nothing -> cannot_find_variable v

    cannot_find_variable _ =
      internalError "convertEffect: Cannot find region or effect variable"
      
convertPassType :: PassTypeAssignment -> RExp -> EffEnv (PassConv, RCType)
convertPassType (MonoAss pt) sf_type = convertMonoPassType pt sf_type

convertPassType (PolyAss (PolyPassType [] pt)) sf_type =
  convertMonoPassType pt sf_type

convertPassType (PolyAss (PolyPassType eff_vars pt)) sf_type = do
  withMany withNewEffectVariable eff_vars $ \eff_vars' -> do
    (pc, mono_type) <- convertMonoPassType pt sf_type
    let mono_fun_type = asFunctionType pc mono_type
        poly_type = foldr pureArrCT mono_fun_type $ map mk_param eff_vars'
    return (Owned, funCT poly_type)
  where
    mk_param ev = ValPT (Just ev) ::: effect_type
    effect_type = expCT effectKindE

asFunctionType :: PassConv -> RCType -> RCFunType
asFunctionType Owned (FunCT t) = t
asFunctionType pc ty = retCT emptyEffectType $! case pc
                                                of ByValue -> ValRT ::: ty
                                                   Owned -> OwnRT ::: ty
                                                   Borrowed -> WriteRT ::: ty

-- | Given a type produced by effect inference and the corresponding
-- original System F type, construct an ANF type.
convertMonoPassType :: PassType -> RExp -> EffEnv (PassConv, RCType)
convertMonoPassType pass_type sf_type =
  case pass_type
  of AppT pc op args ->
       case sf_type
       of AppE {expOper = sf_op, expArgs = sf_args}
            | length args /= length sf_args -> mismatch
            | otherwise -> do
                -- The type operator remains unchanged
                let core_op = sf_op

                -- Convert type arguments
                core_args <- zipWithM convertMonoPassType args sf_args

                -- Type arguments are not mangled
                return (pc, appCT core_op core_args)
     FunT {} -> liftM ((,) Owned . FunCT) $ convertFunctionType pass_type sf_type 
     RetT {} -> internalError "convertMonoPassType: Can't handle nullary functions"

     StreamT eff pass_rng ->
       case sf_type
       of AppE { expInfo = app_info
               , expOper = ConE {expInfo = stream_info, expCon = stream_con}
               , expArgs = args}
            | stream_con `isPyonBuiltin` the_Stream -> do
                -- This constructor takes one argument
                let arg = case args
                          of [arg] -> arg
                             _ -> mismatch

                -- Convert it to an effect-decorated stream type
                core_eff <- convertEffect eff
                core_rng <- convertMonoPassType pass_rng arg
                return (Owned,
                        stream_type app_info stream_info core_eff core_rng)
            
          _ -> mismatch

     VarT pc v ->
       case sf_type
       of VarE {} -> return_sf_type pc
          _ -> mismatch
     ConstT pc e -> return_sf_type pc
     TypeT -> return_sf_type ByValue
  where
    -- Inconsistency found between effect inference and System F types 
    mismatch = internalError "convertMonoPassType"
    
    -- Return the System F type unchanged
    return_sf_type pc = return (pc, expCT sf_type)
                     
    -- Build a stream type
    stream_type app_info op_info eff rng =
      let con = pyonBuiltin the_LazyStream
          op = mkConE (getSourcePos op_info) con
      in appCT op [(ByValue, eff), rng]

convertFunctionType :: PassType -> RExp -> EffEnv RCFunType
convertFunctionType pass_type sf_type =
  case pass_type
  of FunT param pass_rng ->
       case sf_type
       of FunE {expMParam = binder, expRange = sf_rng} -> do
            convertPassTypeParam param binder $ \core_binder ->
              liftM (pureArrCT core_binder) $
              convertFunctionType pass_rng sf_rng
          _ -> internalError "convertFunctionType"
     RetT eff pass_rng -> do
       core_eff <- convertEffect eff
       core_rng <- convertMonoPassType pass_rng sf_type
       return $ make_function core_eff core_rng
     _ -> do
       core_rng <- convertMonoPassType pass_type sf_type
       return $ make_function emptyEffectType core_rng
  where
    make_function eff (pc, ty) =
      let return_type = case pc
                        of ByValue  -> ValRT ::: ty
                           Owned    -> OwnRT ::: ty
                           Borrowed -> WriteRT ::: ty
      in retCT eff return_type

convertPassTypeParam :: FunParam -> RBinder' () -> (CBind CParamT Rec -> EffEnv a) -> EffEnv a
convertPassTypeParam param (Binder' mv dom ()) k = do
  (dom_pc, dom_ty) <- convertMonoPassType (paramType param) dom

  case dom_pc of
    ByValue -> k $ ValPT mv ::: dom_ty
    Owned -> k $ OwnPT ::: dom_ty
    Borrowed ->
      -- Create a new region variable for the parameter's region.
      -- Because this variable only appears in types, its corresponding  
      -- pointer variable is not used
      case paramRegion param
      of Just rv -> withNewRegionVariable rv no_ptr dom_ty $ \rv' ->
           k $ ReadPT rv' ::: dom_ty
         Nothing -> internalError "convertPassTypeParam"
  where
    no_ptr = internalError "convertPassTypeParam: No pointer variable"

{-convertEType :: EType -> RExp -> EffEnv RCType
convertEType etype sf_type =
  case etype
  of AppT op args ->
       case sf_type
       of AppE {expOper = sf_op, expArgs = sf_args}
            | length args /= length sf_args -> mismatch
            | otherwise -> do
                -- The type operator remains unchanged
                let core_op = sf_op

                -- Convert type arguments
                core_args <- zipWithM convertEType args sf_args

                -- Type arguments are not mangled
                return $ appByValue core_op core_args

     StreamT eff pass_rng ->
       case sf_type
       of AppE { expInfo = app_info
               , expOper = ConE {expInfo = stream_info, expCon = stream_con}
               , expArgs = args}
            | stream_con `isPyonBuiltin` the_Stream -> do
                -- This constructor takes one argument
                let arg = case args
                          of [arg] -> arg
                             _ -> mismatch

                -- Convert it to an effect-decorated stream type
                core_eff <- convertEffect eff
                core_rng <- convertEType pass_rng arg
                return $ stream_type app_info stream_info core_eff core_rng
            
          _ -> mismatch

     VarT v ->
       case sf_type
       of VarE {} -> return_sf_type
          _ -> mismatch
     ConstT e -> return_sf_type
     TypeT -> return_sf_type
  where
    -- Inconsistency found between effect inference and System F types 
    mismatch = internalError "convertEType"
    
    -- Return the System F type unchanged
    return_sf_type = return $ expCT sf_type
                     
    -- Build a stream type
    stream_type app_info op_info eff rng =
      let con = pyonBuiltin the_LazyStream
          op = mkConE (getSourcePos op_info) con
      in appCT op [(ByValue, eff), (Borrowed, rng)]-}

convertType :: Effect.ExpOf Effect.EI Effect.EI -> RCType
convertType ty = expCT $ Effect.fromEIType ty

-------------------------------------------------------------------------------
-- Expression conversion

newtype Context = Context (Maybe (RCExp -> RCExp))

context f = Context (Just f)
idContext = Context Nothing

isIdContext (Context Nothing)  = True
isIdContext (Context (Just _)) = False

instance Monoid Context where
  mempty = idContext
  mappend (Context Nothing) x = x
  mappend x (Context Nothing) = x
  mappend (Context (Just x)) (Context (Just y)) =
    Context (Just (x . y))

applyContext (Context Nothing)  x = x
applyContext (Context (Just f)) x = f x

-- | When an expression is flattened to something that returns a borrowed
-- result, it writes into a return address that is provided by the caller.
-- However the caller's return address is not available until later.  So
-- a placeholder return address and pointer are created, and later renamed
-- to the real address and pointer.
data FlatExp = FlatExp { flattenedExp :: !RCExp
                       , flattenedReturn :: !(CBind CReturnT Rec)
                         -- | The location that the expression writes its
                         -- return value to.  It's a 'Just' value if the
                         -- return type is 'WriteRT', otherwise 'Nothing'.
                       , flattenedDst :: !(Maybe (AddrVar, PtrVar))
                       }

applyContextFlat :: Context -> FlatExp -> FlatExp
applyContextFlat ctx e = e {flattenedExp = applyContext ctx $ flattenedExp e}

hasRelocatableReturn :: FlatExp -> Bool
hasRelocatableReturn e = isJust $ flattenedDst e 

-- | Generate code to bind a statement's return value to a new temporary
-- variable.
genLet :: FlatExp -> EffEnv ContextExp
genLet fexp = do
  -- Create a binder for the new temporary value
  binder <- make_binder
  
  -- Create a 'let' statement to bind the result
  let letexp body =
        let pos = getSourcePos $ cexpInfo body
            info = mkSynInfo pos ObjectLevel
        in LetCE { cexpInfo = info
                 , cexpBinder = binder
                 , cexpRhs = flattenedExp fexp
                 , cexpBody = body}
  
      val = letBinderValue $ fromCBind binder
      val_exp = let inf = mkSynInfo (getSourcePos $ flattenedExp fexp) ObjectLevel
                in ValCE inf val
  return (context letexp,
          FlatExp val_exp (letBinderType binder) Nothing)
  where
    make_binder =
      case flattenedReturn fexp
      of rt ::: ty -> 
           case rt
           of ValRT -> do
                bound_var <- newAnonymousVariable ObjectLevel
                return $ ValB bound_var ::: ty
              OwnRT -> do
                bound_var <- newAnonymousVariable ObjectLevel
                return $ OwnB bound_var ::: ty
              WriteRT ->
                -- Use the address and pointer that were generated
                -- along with the expression
                case flattenedDst fexp
                of Just (a, p) -> return $ LocalB a p ::: ty
                   Nothing -> internalError "genLet"
              ReadRT addr -> do
                bound_ptr <- newAnonymousVariable ObjectLevel
                return $ RefB addr bound_ptr ::: ty

-- | Store the expression's result into the given location.
genStore :: AddrVar -> PtrVar -> FlatExp -> FlatExp
genStore dst_addr dst_ptr fexp =
  case flattenedReturn fexp
  of WriteRT ::: _ ->
       case flattenedDst fexp
       of Just (a, p) ->
            -- Rename the expression to write to the given destination
            let exp' = substFully $ rename a dst_addr $ rename p dst_ptr $
                       verbatim $ flattenedExp fexp
            in return_exp exp'
     ReadRT _ ::: _ ->
       -- Copy from source to destination
       genCopy fexp dst_addr dst_ptr
     _ -> internalError "genStore"
  where
    return_exp e =
      FlatExp e (WriteRT ::: return_type) (Just (dst_addr, dst_ptr))

    return_type = case flattenedReturn fexp of _ ::: ty -> ty
                                             
    pos = getSourcePos $ flattenedExp fexp

-- | Generate a statement that copies the expression's result into the given
-- destination.  The expression should return a borrowed reference to an
-- existing variable.
genCopy :: FlatExp -> AddrVar -> PtrVar -> FlatExp
genCopy src dst_addr dst_ptr =
  let rt = case flattenedReturn src
           of ReadRT _ ::: ty -> WriteRT ::: ty
  in trace "FIXME: genCopy " $
     FlatExp (flattenedExp src) rt (Just (dst_addr, dst_ptr))

-------------------------------------------------------------------------------

type ContextExp = (Context, FlatExp)

-- | FIXME: compare types; coerce functions
coerce :: CBind CReturn Rec     -- ^ Target type and passing convention
       -> FlatExp               -- ^ Expression to coerce
       -> EffEnv FlatExp        -- ^ Returns a coerced expression
coerce (expect_return ::: expect_type) val =
  case expect_return
  of ValR ->
       case flattenedReturn val
       of ValRT ::: given_type -> no_change
          _ -> not_implemented
     OwnR ->
       case flattenedReturn val
       of OwnRT ::: given_type -> no_change
          _ -> not_implemented
     WriteR expect_addr expect_ptr ->
       -- Ensure that the expression writes into the given destination
       case flattenedReturn val
       of WriteRT ::: given_type -> gen_store expect_addr expect_ptr
          ReadRT _ ::: given_type -> gen_store expect_addr expect_ptr
          _ -> traceShow (pprReturn (expect_return ::: expect_type) $$ pprReturnT (flattenedReturn val)) not_implemented
  where
    no_change = return val
    not_implemented = internalError "coerce: not implemented"
    
    gen_store expect_addr expect_ptr =
      case flattenedDst val
      of Just (given_addr, given_ptr) ->
           return $ genStore expect_addr expect_ptr val
         _ -> internalError "coerce"

-- | Coerce a value that will be passed as a parameter to a function call
coerceParameter :: CBind CParamT Rec
                -> FlatExp
                -> EffEnv ContextExp
coerceParameter (expect_param ::: expect_type) val =
  case expect_param
  of ValPT _ ->
       case flattenedReturn val
       of ValRT ::: _ -> no_change
          _ -> not_implemented
     OwnPT ->
       case flattenedReturn val
       of OwnRT ::: _ -> no_change
          _ -> not_implemented
     ReadPT _ ->
       case flattenedReturn val
       of WriteRT ::: _ -> do
            -- Write into a temporary variable and return the variable
            genLet val
          ReadRT _ ::: _ -> do
            -- Pass this borrowed reference
            return (idContext, val)
          _ -> not_implemented
  where
    no_change = return (idContext, val)
    not_implemented = internalError "coerceParameter: not implemented"       

-- | Coerce an expression to a callable expression.
-- The expression must have function type.  The function type is also returned.
coerceToCallable :: FlatExp -> EffEnv (FlatExp, RCFunType)
coerceToCallable expr =
  let callable_type =
        case flattenedReturn expr of _ ::: ty -> OwnR ::: ty
      function_type =
        case flattenedReturn expr
        of _ ::: FunCT t -> t
           _ -> internalError "coerceToCallable: not a function type"

  in do fexp <- coerce callable_type expr
        return (fexp, function_type)

-- | Convert a parameter binder
convertParameter :: Effect.EIBinder 
                 -> (CBind CParam Rec -> EffEnv a)
                 -> EffEnv a
convertParameter (Binder v ty (rgn, pass_type)) k = do
  (conv, ty') <- convertMonoPassType pass_type (Effect.fromEIType ty)
  case conv of
    ByValue  ->
      -- Also add the parameter to the environment if we need to
      withParameterVariable v ty' $ k $ ValP v ::: ty'
    Owned    -> k $ OwnP v ::: ty'
    Borrowed ->
      case rgn
      of Just rv -> withNewRegionVariable rv v ty' $ \rv' ->
                    k $! ReadP rv' v ::: ty'
         Nothing -> traceShow (pprType ty') $ internalError "convertParameter"

convertLetBinder :: Effect.EIBinder 
                 -> (CBind LetBinder Rec -> EffEnv a)
                 -> EffEnv a
convertLetBinder (Binder v ty (rgn, pass_type)) k = do
  (conv, ty') <- convertMonoPassType pass_type (Effect.fromEIType ty)
  case conv of
    ByValue  -> k $ ValB v ::: ty'
    Owned    -> k $ OwnB v ::: ty'
    Borrowed ->
      case rgn
      of Just rv -> withNewRegionVariable rv v ty' $ \rv' ->
                    k $! LocalB rv' v ::: ty'
         Nothing -> internalError "convertLetBinder"

-- | Determine what this expression returns based on its effect-inferred type,
-- assuming the expression creates a new return value.  The answer will not be
-- correct for other expressions.
effectReturnType :: Effect.EIExp -> EffEnv (CBind CReturnT Rec)
effectReturnType expr = do
  (new_conv, new_type) <-
    convertPassType (Effect.eiReturnType expr) (Effect.eiType expr)
  let rt = case new_conv
           of ByValue -> ValRT
              Owned -> OwnRT
              Borrowed -> WriteRT
  return $ rt ::: new_type

-- | Convert an effect to the corresponding type
effectValue :: SourcePos -> Effect -> EffEnv RCExp
effectValue pos eff = do
  ty <- convertEffect eff
  let info = mkSynInfo pos TypeLevel
  return $ ValCE info $ TypeV ty

flattenExp :: Effect.EIExp -> EffEnv FlatExp
flattenExp expression =
  case Effect.eiExp expression
  of Effect.VarE {Effect.expVar = v} ->
       flattenVarExp expression v
     Effect.ConE {Effect.expCon = c} ->
       flattenConExp expression c
     Effect.LitE {Effect.expLit = l} ->
       flattenLitExp expression l
     Effect.TypeE {Effect.expTypeValue = ty} -> do
       rt <- effectReturnType expression
       let inf = mkSynInfo (getSourcePos expression) TypeLevel
           exp = ValCE inf $ TypeV $ convertType ty
       return $ FlatExp exp rt Nothing
     Effect.InstanceE { Effect.expOper = op
                      , Effect.expEffectArgs = effects} ->
       flattenInstanceExp expression op effects
     Effect.RecPlaceholderE { Effect.expVar = v
                            , Effect.expPlaceholderValue = ph_val} ->
       internalError "Not implemented: flattening recursive placeholders"
     Effect.CallE {Effect.expOper = op, Effect.expArgs = args} ->
       flattenCall expression op args
     Effect.FunE {Effect.expFun = f} -> do
       rt <- effectReturnType expression
       let inf = mkSynInfo (getSourcePos expression) ObjectLevel
       f' <- flattenFun f
       return $ FlatExp (LamCE inf f') rt Nothing
     Effect.DoE { Effect.expTyArg = ty
                , Effect.expPassConv = pc
                , Effect.expBody = body} ->
       flattenDo expression ty pc body
     Effect.LetE { Effect.expBinder = b
                 , Effect.expValue = val
                 , Effect.expBody = body} ->
       flattenLet expression b val body
     Effect.LetrecE {Effect.expDefs = defs, Effect.expBody = body} ->
       flattenLetrec expression defs body
     Effect.CaseE {Effect.expScrutinee = scr, Effect.expAlternatives = alts} ->
       flattenCase expression scr alts
       
flattenVarExp expression v = do
  -- Get the variable's type
  (conv, ty) <- convertPassType (Effect.eiReturnType expression) (Effect.eiType expression)
  
  -- Create an expression
  let inf = mkSynInfo (getSourcePos expression) (getLevel v)
  new_expr <-
    case conv
    of ByValue ->
         return $ FlatExp (ValCE inf (ValueVarV v)) (ValRT ::: ty) Nothing
       Owned ->
         return $ FlatExp (ValCE inf (OwnedVarV v)) (OwnRT ::: ty) Nothing 
       Borrowed ->
         -- Get the variable's regin
         case Effect.eiRegion expression
         of Just rv -> do
              (addr, ptr, ty) <- lookupRegion rv
              
              -- This is a borrowed reference to the variable
              let addr_exp = mkInternalVarE addr
                  new_exp = ValCE inf (ReadVarV addr_exp ptr)
                  ret = ReadRT addr_exp ::: ty
              return $ FlatExp new_exp ret (Just (addr, ptr))
  return new_expr

flattenConExp expression c = do
  rt <- effectReturnType expression
  
  let inf = mkSynInfo (getSourcePos expression) (getLevel c)
      val = case rt
            of ValRT ::: _ -> ValueConV c
               OwnRT ::: _ -> OwnedConV c
               _ -> internalError "flattenConExp"
  return $ FlatExp (ValCE inf val) rt Nothing

flattenLitExp expression l = do
  rt <- effectReturnType expression
  let inf = mkSynInfo (getSourcePos expression) ObjectLevel
  return $ FlatExp (ValCE inf (LitV l)) (ValRT ::: cbindType rt) Nothing

flattenInstanceExp expression op effects = do
  -- Flatten the operator
  flat_op <- flattenExp op
  (call_op, call_type) <- coerceToCallable flat_op
  
  -- Make effect operands
  effect_vals <- mapM (effectValue $ getSourcePos expression) effects

  -- Get the type of this instance of the operator
  inst_return <- applyCallType (verbatim call_type) effect_vals

  -- Can't handle borrowed return type
  case inst_return of
    WriteRT ::: _ -> internalError "flattenInstanceExp"
    _ -> return ()
  
  let inf = mkSynInfo (getSourcePos expression) ObjectLevel
      exp = AppCE inf (flattenedExp call_op) effect_vals Nothing
  return $ FlatExp exp inst_return Nothing

flattenCall call_expression op args = do
  -- Flatten the operator
  flat_op <- flattenExp op
  (call_op, call_type) <- coerceToCallable flat_op

  -- Flatten arguments and create call expression
  (call_ctx, call_val) <-
    applyCall (getSourcePos $ flattenedExp flat_op)
              (verbatim call_type)
              (flattenedExp call_op)
              args

  -- Apply the context to the entire call expression
  let call = applyContextFlat call_ctx call_val
  return call

-- | Compute the result type of an application, given the operand type and 
-- arguments.
applyCallType :: RecCFunType SubstRec
              -> [RCExp]
              -> EffEnv (CBind CReturnT Rec)
applyCallType op_type (atype:atypes) = do
  op_type' <- freshenHead op_type
  case op_type' of
    ArrCT {ctParam = param, ctRange = rng} -> do
      let rng' = case param
                 of ValPT (Just param_var) ::: _ ->
                      case atype
                      of ValCE {cexpVal = TypeV ty} ->
                           verbatim $ assignTypeFun param_var ty rng
                         _ -> internalError "applyCallType"
                    _ -> rng
      applyCallType rng' atypes
    RetCT {} -> internalError "applyCallType: Too many arguments"

applyCallType op_type [] = do
  op_type' <- freshenHead op_type
  case op_type' of
    RetCT {ctReturn = ret} -> return $ substituteCBind substituteCReturnT substFully ret
    ArrCT {} -> return $ OwnRT ::: FunCT (substFullyUnder op_type')

applyCall :: SourcePos
          -> RecCFunType SubstRec -- ^ Operator type
          -> RCExp              -- ^ Operator expression
          -> [Effect.EIExp]     -- ^ Operands
          -> EffEnv ContextExp  -- ^ Return a flattened expression
applyCall pos op_type op args = do
  (ret_type, flat_args, excess) <- applyCallOperands op_type args
  let (mconcat -> arg_context, arg_exps) = unzip flat_args
  call <- make_call_expression arg_context (substituteCBind substituteCReturnT substFully ret_type) op arg_exps
  if null excess
    then return (idContext, call)
    else call_return_value pos call excess
  where
    -- Apply the remaining arguments to the call's return value
    call_return_value pos call excess = do
      (op', function_type) <- coerceToCallable call
      (call_ctx, call) <-
        applyCall pos (verbatim function_type) (flattenedExp op') excess
      return (call_ctx, call)

    -- Create a function call expression.  Insert the return parameter if one
    -- is called for.
    make_call_expression context ret_type op arg_exps = do
      (return_arg, dst) <- make_return_type ret_type
      let inf = mkSynInfo pos ObjectLevel
          exp = applyContext context $ AppCE inf op arg_exps return_arg
      return $ FlatExp exp ret_type dst

    make_return_type :: CBind CReturnT Rec
                     -> EffEnv (Maybe RCExp, Maybe (AddrVar, PtrVar))
    make_return_type (rt ::: ty) =
      case rt
      of ValRT -> return (Nothing, Nothing)
         OwnRT -> return (Nothing, Nothing)
         WriteRT -> do
           addr <- newAnonymousVariable ObjectLevel
           ptr <- newAnonymousVariable ObjectLevel
           return (Just $ writePointerRV noSourcePos (mkInternalVarE addr) ptr,
                   Just (addr, ptr))

applyCallOperands :: RecCFunType SubstRec
                  -> [Effect.EIExp]
                  -> EffEnv (CBind CReturnT SubstRec, [(Context, RCExp)], [Effect.EIExp])
applyCallOperands op_type oprds = do
  op_type' <- freshenHead op_type
  go op_type' oprds id 
  where
    go (ArrCT {ctParam = param, ctRange = rng}) (oprd:oprds) hd = do
      (oprd', oprd_type) <- applyCallOperand param oprd
      
      -- If this is a dependent type, then substitute the operand's type
      rng' <- freshenHead $
              case param
              of ValPT (Just param_var) ::: _ ->
                   -- Dependent type; operand must be a type
                   case snd oprd' of
                     ValCE {cexpVal = TypeV ty} ->
                       verbatim $ assignTypeFun param_var ty rng
                     _ -> internalError "applyCallOperands"
                 _ -> rng
      go rng' oprds (hd . (oprd':))

    go t@(ArrCT {}) [] hd = return (OwnRT ::: verbatim (funCT (substFullyUnder t)), hd [], [])

    go (RetCT _ rt) oprds hd = return (rt, hd [], oprds)

-- | Flatten an operand of a function call and compute the call's side effect
-- and result type.
applyCallOperand :: CBind CParamT SubstRec
                 -> Effect.EIExp 
                 -> EffEnv ((Context, RCExp), RCType)
applyCallOperand param_type operand = do
  -- Flatten and coerce the operand
  arg_val <- flattenExp operand
  (arg_context, arg_val2) <-
    coerceParameter (substituteCBind substituteCParamT substFully param_type) arg_val
    
  let arg_type = cbindType $ flattenedReturn arg_val2
  return ((arg_context, flattenedExp arg_val2), arg_type)

flattenDo expression ty pc body = trace "FIXME: flattenDo" $ do
  body' <- flattenExp body
  
  -- FIXME: build a stream object
  return (body' {flattenedReturn = OwnRT ::: cbindType (flattenedReturn body'),
                 flattenedDst = Nothing})

flattenLet expression b rhs body = do
  rhs' <- flattenExp rhs
  convertLetBinder b $ \b' -> do
    rhs'' <- coerce (letBinderReturn b') rhs'
    body' <- flattenExp body
    let inf = mkSynInfo (getSourcePos expression) ObjectLevel
        new_exp = LetCE inf b' (flattenedExp rhs'') (flattenedExp body')
    return $ FlatExp new_exp (flattenedReturn body') (flattenedDst body')

flattenLetrec expression defs body = do
  defs' <- mapM flattenDef defs
  body' <- flattenExp body
  let inf = mkSynInfo (getSourcePos expression) ObjectLevel
      new_exp = LetrecCE inf defs' (flattenedExp body')
  return $ FlatExp new_exp (flattenedReturn body') (flattenedDst body')

flattenCase expression scr alts = do
  scr' <- flattenExp scr

  flat_alts <- mapM (flattenAlt (getSourcePos expression)) alts
  (alts', rtype, raddr) <- combine_alternatives flat_alts

  let inf = mkSynInfo (getSourcePos expression) ObjectLevel  
  let new_exp = CaseCE inf (flattenedExp scr') alts'
  return $ FlatExp new_exp rtype raddr
  where
    combine_alternatives flat_alts
      | any is_val returns =
          -- Coerce all alternatives to return a value
          coerce_alternatives (ValR ::: return_type)
      | any is_own returns =
          -- Coerce all alternatives to return an owned value
          coerce_alternatives (OwnR ::: return_type)
      | otherwise = do
          -- Return a borrowed value
          raddr <- newAnonymousVariable ObjectLevel
          rptr <- newAnonymousVariable ObjectLevel
          coerce_alternatives (WriteR raddr rptr ::: return_type)
      where
        (alt_binder_data, alt_bodies) = unzip flat_alts
        returns = map flattenedReturn alt_bodies
        return_type = case head returns of _ ::: ty -> ty

        is_val (ValRT ::: _) = True
        is_val _ = False

        is_own (OwnRT ::: _) = True
        is_own _ = False

        coerce_alternatives return_binder = do
          alt_bodies' <- mapM (coerce return_binder) alt_bodies
          let new_alts = zipWith rebuild_alt alt_binder_data alt_bodies'
              return_type = case return_binder
                            of r ::: t -> returnType r ::: t
              return_addr = case return_binder
                            of WriteR a p ::: _ -> Just (a, p)
                               _ -> Nothing
          return (new_alts, return_type, return_addr)

        alt_info = mkSynInfo (getSourcePos expression) ObjectLevel

        rebuild_alt (con, ty_args, params) body =
          CAlt alt_info con ty_args params (flattenedExp body)

flattenAlt :: SourcePos -> Effect.AltOf Effect.EI Effect.EI
           -> EffEnv ((Con, [RCExp], [CBind CParam Rec]), FlatExp)
flattenAlt pos alt = do
  -- Convert type arguments
  let ty_arg_info = mkSynInfo pos TypeLevel
  let ty_args = map (ValCE ty_arg_info . TypeV) $
                map convertType $
                Effect.eialtTyArgs alt

  -- Convert parameters and body
  withMany convertParameter (Effect.eialtParams alt) $ \params -> do
    body <- flattenExp $ Effect.eialtBody alt
    
    -- Create return value
    let con = Effect.eialtConstructor alt
    return ((con, ty_args, params), body)

flattenFun :: Effect.FunOf Effect.EI Effect.EI -> EffEnv RCFun
flattenFun fun =
  -- Add effect parameters to the environment
  assume_effects (Effect.funEffectParams fun) $ \effect_vars ->

  -- Convert binders and add parameter regions to environment
  withMany convertParameter (Effect.funParams fun) $ \binders ->
  
  -- Convert the return type and create a return binder
  convert_return_type $ \ret_binder -> do
    
    -- Flatten the function body
    body_exp <- flattenExp $ Effect.funBody fun
    body_exp' <- coerce ret_binder body_exp
    effect <- convertEffect $ Effect.funEffect fun

    let effect_params = [ValP v ::: effect_type | v <- effect_vars]
          where effect_type = ExpCT effectKindE
        
    let new_fun = CFun { cfunInfo = Effect.funInfo fun
                       , cfunParams = effect_params ++ binders
                       , cfunReturn = ret_binder
                       , cfunEffect = effect
                       , cfunBody = flattenedExp body_exp'
                       }
    return new_fun
  where
    assume_effects = withMany withNewEffectVariable
    
    convert_return_type k = do
      (return_conv, return_type) <-
        convertMonoPassType
        (Effect.funReturnPassType fun)
        (Effect.fromEIType $ Effect.funReturnType fun)

      case return_conv of
        ByValue  -> k $ ValR ::: return_type
        Owned    -> k $ OwnR ::: return_type
        Borrowed -> do
          -- Create parameters for the return pointer
          ret_addr <- newAnonymousVariable ObjectLevel
          ret_ptr <- newAnonymousVariable ObjectLevel
          k $ WriteR ret_addr ret_ptr ::: return_type

flattenDef (Effect.Def v fun) = do
  fun' <- flattenFun fun
  return $ CDef v fun'

flattenModule defss =
  mapM (mapM flattenDef) defss

flatten :: SystemF.Module SystemF.TypedRec -> IO [[CDef Rec]]
flatten mod = do
  -- Run effect inference
  effect_defss <- Effect.runEffectInference mod
  
  -- Run flattening
  flattened <-
    withTheVarIdentSupply $ \var_supply ->
    let env = Env Map.empty Map.empty [] var_supply
    in runReaderT (runEffEnv $ flattenModule effect_defss) env

  -- DEBUG: print flattened code
  putStrLn "Flattened"
  print $ vcat $ concat $ map (map pprCDef) flattened
  
  return flattened
