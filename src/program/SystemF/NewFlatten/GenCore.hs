
{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, ViewPatterns,
    ScopedTypeVariables #-}
module SystemF.NewFlatten.GenCore(flatten)
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
import Gluon.Core.RenameBase
import Gluon.Core.Builtins
import qualified Gluon.Core.Builtins.Effect
import Gluon.Core.Variance
import Gluon.Eval.Environment
import Gluon.Eval.Eval
import Gluon.Eval.Equality
import qualified SystemF.Syntax as SystemF
import SystemF.Builtins
import qualified SystemF.Typecheck as SystemF
import qualified SystemF.NewFlatten.PassConv
import SystemF.NewFlatten.PassConv
import qualified SystemF.NewFlatten.SetupEffect as Effect

import Core.Syntax
import Core.Print
import Core.Gluon
import Globals

-- | Set to 'True' to print each time a value is coerced.
-- All coercions of borrowed values are printed (including no-op coercions). 
-- Coercions of by-value or owned values are only printed if coercion is
-- necessary.
printCoercions :: Bool
printCoercions = False

-- | Set to 'True' to print which function calls are flattened.
printCalls :: Bool
printCalls = False

type EffectType = RecCType Rec

emptyEffectType :: EffectType
emptyEffectType = expCT Gluon.Core.Builtins.Effect.empty

readEffectType :: RExp -> RCType -> EffectType
readEffectType addr ty =
  let at = mkInternalConE $ builtin the_AtE
  in appExpCT at [ty, expCT addr]

unionEffect :: EffectType -> EffectType -> EffectType
unionEffect t1 t2 =
  let sconj = mkInternalConE $ builtin the_SconjE 
  in appExpCT sconj [t1, t2]

unionEffects :: [EffectType] -> EffectType
unionEffects [] = emptyEffectType
unionEffects es = foldr1 unionEffect es

addressType :: RExp
addressType = mkInternalConE $ builtin the_Addr

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
                 -- | Gluon types of in-scope variables.  This is used for
                 -- comparing types and looking up parameter-passing
                 -- convention variables.  Other variables are unimportant,
                 -- so they may be absent.
               , gluonTypeEnv :: [(Var, RExp)]
               , varSupply :: {-# UNPACK #-}!(IdentSupply Var)
               }

cleanEnv var_supply = Env Map.empty Map.empty [] [] var_supply

instance Supplies EffEnv (Ident Var) where
  fresh = EffEnv $ ReaderT $ \env -> supplyValue $ varSupply env
  supplyToST f = EffEnv $ ReaderT $ \env ->
    stToIO (f (unsafeIOToST $ supplyValue $ varSupply env))

instance EvalMonad EffEnv where
  liftEvaluation m = EffEnv $ ReaderT $ \env -> do
    mx <- runEvalIO (varSupply env) m
    case mx of
      Just x -> return x
      Nothing -> internalError "EffEnv: evaluation failed"

instance PureTypeMonad EffEnv where
  assumePure v t m = EffEnv $ local insert_type $ runEffEnv m
    where
      insert_type env = env {gluonTypeEnv = (v, t) : gluonTypeEnv env}

  getType v = EffEnv $ asks lookup_type
    where
      lookup_type env = lookup v $ gluonTypeEnv env

  peekType = getType
             
  getPureTypes = EffEnv $ asks gluonTypeEnv
  
  liftPure = runPureInEffEnv
  
  formatEnvironment f = EffEnv $ ReaderT $ \env ->
    runReaderT (runEffEnv (f (doc env))) env
    where
      doc env = vcat [pprVar v <+> text ":" <+> pprExp t
                     | (v, t) <- gluonTypeEnv env]

runPureInEffEnv :: PureTC a -> EffEnv a
runPureInEffEnv m = EffEnv $ ReaderT $ \env -> do
  x <- runPureTCIO (varSupply env) $
    -- Transfer the type environment
    foldr (uncurry assumePure) m $ reverse $ gluonTypeEnv env
  case x of
    Left errs -> internalError "runPureInEffEnv: Computation failed"
    Right y   -> return y

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

  val `seq` assumePure addr_var addressType $
    EffEnv $ local insert_var $ runEffEnv (f addr_var)

-- | Translate an effect variable to a Gluon variable.
withNewEffectVariable :: EVar -> (Var -> EffEnv a) -> EffEnv a
withNewEffectVariable effect_var f = assertEVar effect_var $ do
  var <- newVar (effectVarName effect_var) TypeLevel
  
  let insert_var env =
        env {effectEnv = Map.insert effect_var var $ effectEnv env}

  assumePure var effectKindE $ EffEnv $ local insert_var $ runEffEnv (f var)

-- | Add the given type to the local environment.  If the type is a
-- @PassConv@ object, add it to the PassConv list as well.
-- This function is called by 'convertParameter' to keep track of dictionaries
-- that may be needed during flattening.
-- This should only be called on pass-by-value variables.
withParameterVariable :: Var    -- ^ Parameter variable
                       -> RCType -- ^ Parameter's type
                       -> EffEnv a
                       -> EffEnv a
withParameterVariable v ty m = do
  gluon_type <- coreToGluonTypeWithoutEffects $ verbatim ty
  assumePure v gluon_type $ assume_passconv_type m
  where
    assume_passconv_type m =
      case unpackConAppCT ty
      of Just (con, args)
           | con `isPyonBuiltin` the_PassConv ->
               case args
               of [t] ->
                    let insert_var env =
                          env {passConvEnv = (t, v) : passConvEnv env}
                    in EffEnv $ local insert_var $ runEffEnv m
                  _ -> internalError "withParameterVariable"
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
asFunctionType pc ty = retCT $! case pc
                                of ByValue -> ValRT ::: ty
                                   Owned -> OwnRT ::: ty
                                   Borrowed -> WriteRT ::: ty

-- | Given a type produced by effect inference and the corresponding
-- original System F type, construct an ANF type.
convertMonoPassType :: PassType -> RExp -> EffEnv (PassConv, RCType)
convertMonoPassType pass_type sf_type =
  case pass_type
  of AppT op args ->
       case sf_type
       of AppE {expOper = sf_op, expArgs = sf_args}
            | length args /= length sf_args -> mismatch
            | otherwise -> do
                -- The type operator remains unchanged
                (_, core_op) <- convertMonoPassType op sf_op

                -- Convert type arguments
                core_args <- zipWithM convertMonoPassType args sf_args

                -- Type arguments are not mangled
                pass_conv <- liftM Effect.typePassConv $ evalHead' sf_type
                return (pass_conv, appCT core_op $ map snd core_args)
     FunT ft -> do
       t <- convertFunctionType ft sf_type
       return (Owned, FunCT t)

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
                (_, core_rng) <- convertMonoPassType pass_rng arg
                return (Owned,
                        stream_type app_info stream_info core_eff core_rng)
            
          _ -> mismatch

     VarT v ->
       case sf_type
       of VarE {} -> return_sf_type
          _ -> mismatch
     ConstT e -> return_sf_type
     TypeT -> return_sf_type
  where
    -- Inconsistency found between effect inference and System F types 
    mismatch = internalError "convertMonoPassType"
    
    -- Return the System F type unchanged
    return_sf_type = do 
      pass_conv <- liftM Effect.typePassConv $ evalHead' sf_type
      return (pass_conv, expCT sf_type)
                     
    -- Build a stream type
    stream_type app_info op_info eff rng =
      let con = pyonBuiltin the_LazyStream
          op = mkConE (getSourcePos op_info) con
      in appExpCT op [eff, rng]

convertFunctionType :: FunPassType -> RExp -> EffEnv RCFunType
convertFunctionType pass_type sf_type =
  case pass_type
  of FunFT param pass_rng ->
       case sf_type
       of FunE {expMParam = binder, expRange = sf_rng} ->
            convertPassTypeParam param binder $ \core_binder -> do
              eff <- range_effect pass_rng
              liftM (arrCT core_binder eff) $
                convertFunctionType pass_rng sf_rng
          _ -> internalError "convertFunctionType"
     RetFT _ pass_rng -> do
       core_rng <- convertMonoPassType pass_rng sf_type
       return $ retCT $ make_return core_rng
  where
    range_effect (FunFT _ _) = return emptyEffectType
    range_effect (RetFT eff _) = convertEffect eff

    make_return (pc, ty) =
      case pc
      of ByValue  -> ValRT ::: ty
         Owned    -> OwnRT ::: ty
         Borrowed -> WriteRT ::: ty

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

-- | Create the type of a 'store' function.  The types follow the schema
-- @val t -> bor t@
-- for some type @t@.
storeFunctionType :: RCType -> RCType
storeFunctionType value_type =
  funCT $
  pureArrCT (ValPT Nothing ::: value_type) $
  retCT (WriteRT ::: value_type)

-- | Create the type of a 'load' function.  The types follow the schema
-- @read t@a -> val t@
-- for some type @t@.
loadFunctionType :: RCType -> EffEnv RCType
loadFunctionType value_type = do
  addr <- newAnonymousVariable ObjectLevel
  let eff = readEffectType (mkInternalVarE addr) value_type
  return $ funCT $ arrCT (ReadPT addr ::: value_type) eff $
    retCT (ValRT ::: value_type)

-- | Create a return binder for the given type and passing convention
createReturnBinder :: PassConv -> RCType -> EffEnv (CBind CReturn Rec)
createReturnBinder pc ty =
  case pc
  of ByValue  -> return $ ValR ::: ty
     Owned    -> return $ OwnR ::: ty
     Borrowed -> do
       -- Create parameters for the return pointer
       ret_addr <- newAnonymousVariable ObjectLevel
       ret_ptr <- newAnonymousVariable ObjectLevel
       return $ WriteR ret_addr ret_ptr ::: ty

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
  of ValRT ::: ty ->
       -- Call a store function based on the given type
       let pos = getSourcePos $ flattenedExp fexp
           fn = genStoreFunction pos ty
           return_arg = ValCE { cexpInfo = mkSynInfo pos ObjectLevel
                              , cexpVal = WriteVarV (mkInternalVarE dst_addr) dst_ptr
                              }
           exp = AppCE { cexpInfo = mkSynInfo pos ObjectLevel
                       , cexpOper = flattenedExp fn
                       , cexpArgs = [flattenedExp fexp]
                       , cexpReturnArg = Just return_arg
                       }
       in FlatExp exp (WriteRT ::: ty) (Just (dst_addr, dst_ptr))
     WriteRT ::: _ ->
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

-- | Store the expression's result into a new location.  The destination
-- address and pointer are put into the returned 'flattenedDst' field.
genNewStore :: FlatExp -> EffEnv FlatExp
genNewStore e = do
  addr_var <- newAnonymousVariable ObjectLevel
  ptr_var <- newAnonymousVariable ObjectLevel
  return $ genStore addr_var ptr_var e

-- | Load the result of another expression.  The given expression must return
-- by reference.
genLoad :: FlatExp -> EffEnv FlatExp
genLoad fexp = do
  -- Save the expression's result in a temporary variable, unless 
  -- it's a plain value
  (ctx, fexp') <-
    if is_plain_value fexp
    then return (idContext, fexp)
    else genLet fexp
  
  let (addr, ptr) = case flattenedExp fexp'
                    of ValCE {cexpVal = ReadVarV addr ptr} -> (addr, ptr)
                       _ -> internalError "genLoadResult"
      addr_var = case addr
                 of VarE {expVar = v} -> v
                    _ -> internalError "genLoadResult"
      pos = getSourcePos $ flattenedExp fexp'
      ty = cbindType $ flattenedReturn fexp'

  -- Now load the value
  load_fun <- genLoadFunction pos addr_var ptr ty

  let load_exp = AppCE { cexpInfo = mkSynInfo pos ObjectLevel
                       , cexpOper = flattenedExp load_fun
                       , cexpArgs = [flattenedExp fexp']
                       , cexpReturnArg = Nothing
                       }
      load_fexp = FlatExp load_exp (ValRT ::: ty) Nothing

  return $ applyContextFlat ctx load_fexp
  where
    is_plain_value fexp =
      case flattenedExp fexp 
      of ValCE {cexpVal = ReadVarV addr _} ->
           case addr
           of VarE {} -> True
              _ -> False
         _ -> False

-- | Generate a statement that copies the expression's result into the given
-- destination.  The expression should return a borrowed reference to an
-- existing variable.
genCopy :: FlatExp -> AddrVar -> PtrVar -> FlatExp
genCopy src dst_addr dst_ptr =
  let rt = case flattenedReturn src
           of ReadRT _ ::: ty -> WriteRT ::: ty
  in trace "FIXME: genCopy " $
     FlatExp (flattenedExp src) rt (Just (dst_addr, dst_ptr))

-- | Create the value of the 'store' function of the given type.
genStoreFunction :: SourcePos -> RCType -> FlatExp
genStoreFunction pos ty =
  let exp = ValCE { cexpInfo = mkSynInfo pos ObjectLevel
                  , cexpVal = OwnedConV store_function
                  }
  in FlatExp exp (OwnRT ::: store_type) Nothing
  where
    -- Pick a function to use to store 'ty'.
    store_function =
      case ty
      of ExpCT {ctValue = ConE {expCon = c}}
           | c `isPyonBuiltin` the_int -> pyonBuiltin the_fun_store_int
           | c `isPyonBuiltin` the_float -> pyonBuiltin the_fun_store_float
           | c `isPyonBuiltin` the_bool -> pyonBuiltin the_fun_store_bool
         _ -> traceShow (pprType ty) $ internalError "genStore: Don't know how to store value"

    store_type = storeFunctionType ty

-- | Create the value of the 'load' function of the given type.
genLoadFunction :: SourcePos -> AddrVar -> PtrVar -> RCType -> EffEnv FlatExp
genLoadFunction pos src_addr src_ptr ty = do
  load_type <- loadFunctionType ty
  let exp = ValCE { cexpInfo = mkSynInfo pos ObjectLevel
                  , cexpVal = OwnedConV load_function
                  }
  return $ FlatExp exp (ValRT ::: load_type) Nothing
  where
    load_function =
      case ty
      of ExpCT {ctValue = ConE {expCon = c}}
           | c `isPyonBuiltin` the_int -> pyonBuiltin the_fun_load_int
           | c `isPyonBuiltin` the_float -> pyonBuiltin the_fun_load_float
           | c `isPyonBuiltin` the_bool -> pyonBuiltin the_fun_load_bool
         _ -> internalError "genLoad: Don't know how to load value"

-- | Create a return parameter and address information for a function call,
-- depending on the function's return type.
makeReturnArgument :: CBind CReturnT Rec
                   -> EffEnv (Maybe RCExp, Maybe (AddrVar, PtrVar))
makeReturnArgument (rt ::: ty) =
  case rt
  of ValRT -> return (Nothing, Nothing)
     OwnRT -> return (Nothing, Nothing)
     WriteRT -> do
       addr <- newAnonymousVariable ObjectLevel
       ptr <- newAnonymousVariable ObjectLevel
       return (Just $ writePointerRV noSourcePos (mkInternalVarE addr) ptr,
               Just (addr, ptr))

-------------------------------------------------------------------------------

type ContextExp = (Context, FlatExp)

-- | Determine whether the expected and actual types are compatible.  Ignore side effects when
-- comparing types.
--
-- If the given variance is 'Covariant', the actual type must be no greater
-- than the expected type.
-- If 'Invariant', it must be equal.
-- If 'Contravariant', it must be no smaller.
checkCompatibility :: Variance        -- ^ Comparison direction
                   -> RCType          -- ^ Expected type
                   -> RCType          -- ^ Actual type
                   -> EffEnv Bool
checkCompatibility variance t1 t2 = do
  t1' <- coreToGluonTypeWithoutEffects $ verbatim t1
  t2' <- coreToGluonTypeWithoutEffects $ verbatim t2

  runPureInEffEnv $
    case variance
    of Covariant -> testSubtyping (verbatim t2') (verbatim t1') 
       Invariant -> testEquality (verbatim t1') (verbatim t2')
       Contravariant -> testEquality (verbatim t1') (verbatim t2')

requireCompatibility variance expected actual =
  checkCompatibility variance expected actual >>= check
  where
    check True  = return ()
    check False = internalError "Unexpected type mismatch during GenCore phase"

coerce :: Variance
       -> CBind CReturn Rec     -- ^ Target type and passing convention
       -> FlatExp               -- ^ Expression to coerce
       -> EffEnv FlatExp        -- ^ Returns a coerced expression
coerce variance (expect_return ::: expect_type) val =
  case expect_return
  of ValR -> do
       -- We can't coerce value types; they need to match exactly
       requireCompatibility variance expect_type (cbindType $ flattenedReturn val)
       case fromCBind $ flattenedReturn val of
         ValRT -> no_change
         ReadRT _ -> debug $ genLoad val
         WriteRT -> debug $ genLoad val
         _ -> not_implemented
     OwnR ->
       case flattenedReturn val
       of OwnRT ::: given_type ->
            coerceOwnedValue variance expect_type given_type val
          _ -> not_implemented
     WriteR expect_addr expect_ptr -> debug $ do
       -- Ensure that the expression writes into the given destination
       let given_type = cbindType $ flattenedReturn val
       requireCompatibility variance expect_type given_type
       return $ genStore expect_addr expect_ptr val
  where
    no_change = return val
    not_implemented = internalError "coerce: not implemented"
    
    debug x
      | printCoercions =
          let return_doc = pprReturn (expect_return ::: expect_type) 
              given_doc  = pprReturnT (flattenedReturn val)
              msg = text "coerce value" $$
                    (text "from" <+> given_doc $$ text "  to" <+> return_doc)
          in traceShow msg x 
      | otherwise = x

-- | Coerce a value that will be passed as a parameter to a function call.
--
-- If passing by reference, the generated expression will pass a convenient
-- pointer and address (not necessarily the expected address).  The caller
-- should accept whatever pointer and address are given.
--
-- Variables bound by the expected parameter are ignored.
coerceParameter :: CBind CParamT Rec
                -> FlatExp
                -> EffEnv ContextExp
coerceParameter (expect_param ::: expect_type) val =
  case expect_param
  of ValPT _ -> do
       -- We can't coerce value types; they need to match exactly
       requireCompatibility Covariant expect_type (cbindType $ flattenedReturn val)
       case fromCBind $ flattenedReturn val of
         ValRT -> no_change
         ReadRT _ -> debug $ do cexp <- genLoad val
                                return (idContext, cexp)
         WriteRT -> debug $ do cexp <- genLoad val
                               return (idContext, cexp)
     OwnPT ->
       case flattenedReturn val
       of OwnRT ::: given_type -> do
            val' <- coerceOwnedValue Covariant expect_type given_type val
            return (idContext, val')
          _ -> not_implemented
     ReadPT _ -> debug $
       case flattenedReturn val
       of ValRT ::: given_type -> do
            requireCompatibility Covariant expect_type given_type
            coerceValueToBorrowed val expect_type
          WriteRT ::: given_type -> do
            requireCompatibility Covariant expect_type given_type
            -- Write into a temporary variable and return the variable
            genLet val
          ReadRT _ ::: given_type -> do
            requireCompatibility Covariant expect_type given_type
            -- Pass this borrowed reference
            return (idContext, val)
          _ -> not_implemented
  where
    no_change = return (idContext, val)
    not_implemented = internalError "coerceParameter: not implemented"
    
    debug x
      | printCoercions =
          let return_doc = pprParamT (expect_param ::: expect_type) 
              given_doc  = pprReturnT (flattenedReturn val)
              msg = text "coerce parameter" $$
                    (text "from" <+> given_doc $$ text "  to" <+> return_doc)
          in traceShow msg x 
      | otherwise = x


-- | Make a value variable available as a borrowed variable.
-- This generates a @let@ expression that stores the value into a locally
-- allocated variable.
coerceValueToBorrowed val ty = do
  -- Store the value into a new location 
  store_val <- genNewStore val
  let Just (addr_var, ptr_var) = flattenedDst store_val
  
  -- Build a let-expression
  let let_binder = LocalB addr_var ptr_var
      let_stm body =
        LetCE { cexpInfo = mkSynInfo (getSourcePos $ cexpInfo body) ObjectLevel
              , cexpBinder = let_binder ::: ty
              , cexpRhs = flattenedExp store_val
              , cexpBody = body
              }
        
  -- Build the borrowed value
  let inf = mkSynInfo (getSourcePos $ cexpInfo $ flattenedExp val) ObjectLevel
      local_value = ValCE { cexpInfo = inf
                          , cexpVal = letBinderValue let_binder
                          }
      local_exp =
        FlatExp local_value (ReadRT (mkInternalVarE addr_var) ::: ty) Nothing
  return (context let_stm, local_exp)

-- | Coerce an owned value to an owned value of another type.
coerceOwnedValue variance expect_type given_type val = do
  -- Check whether types are already compatible
  compatible <- checkCompatibility variance expect_type given_type
  if compatible
    then return val             -- No change
    else case (expect_type, given_type)
         of (FunCT expect_ft, FunCT given_ft) ->
              let val_exp = flattenedExp val
              in coerceFunction expect_ft given_ft val_exp
            (_, _) -> internalError "coerceOwnedValue: not implemented"

-- | Coerce a function from one type to another by wrapping it with a lambda
-- function.
-- 
-- The parameter must be an owned function.
coerceFunction :: RCFunType     -- ^ Expected function type
               -> RCFunType     -- ^ Given function type
               -> RCExp         -- ^ Given function
               -> EffEnv FlatExp -- ^ Returns a function matching expected type
coerceFunction expected_ft given_ft given_function = debug $ do
  lam_exp <- coerceFunctionParameters (verbatim expected_ft) (verbatim given_ft) (verbatim emptyEffectType) $
    createFunctionCoercion given_function
  return $ FlatExp lam_exp (OwnRT ::: FunCT expected_ft) Nothing
  where
    debug x
      | printCoercions =
          let return_doc = pprType (FunCT expected_ft)
              given_doc  = pprType (FunCT given_ft)
              msg = text "coerce function" $$
                    (text "from" <+> given_doc $$ text "  to" <+> return_doc)
          in traceShow msg x 
      | otherwise = x

-- | Coerces function parameters for 'coerceFunction'.
--
-- Each recursive call coerces one function parameter.  When all parameters 
-- are coerced, the continuation is called to process the return value and
-- do other required actions.
--
-- The @expected_effect@ parameter is ignored and should be the empty effect,
-- except when processing the return type.  An effect should only occur when
-- the last function parameter is passed.
coerceFunctionParameters :: forall a.
                            RecCFunType SubstRec
                         -> RecCFunType SubstRec
                         -> RecCType SubstRec
                         -> ([CBind CParam Rec] -> [ContextExp] -> RCType ->
                             CBind CReturnT Rec -> CBind CReturnT Rec ->
                             EffEnv a)
                         -> EffEnv a
coerceFunctionParameters expected_ft given_ft expected_effect finish = do
  expected_ft' <- freshenHead expected_ft
  given_ft' <- freshenHead given_ft
  case (expected_ft', given_ft') of
    (ArrCT {ctParam = e_param, ctEffect = e_effect, ctRange = e_range},
     ArrCT {ctParam = g_param, ctRange = g_range}) ->
      -- Unify bound variables and create a function parameter.  Add dependent
      -- variables to environment.
      unify_parameters e_param g_param $ \src_param e_renaming g_renaming ->
        -- Rename the rest of the expression
        let e_range' = joinSubst e_renaming e_range
            g_range' = joinSubst g_renaming g_range
            
            g_param' = substituteCBind substituteCParamT substFully g_param

           -- Coerce from expected to given type, and continue
        in coerce_and_continue g_param' src_param e_effect e_range' g_range'

    (RetCT e_ret, RetCT g_ret) ->
      let eff    = substFully expected_effect
          e_ret' = substituteCBind substituteCReturnT substFully e_ret
          g_ret' = substituteCBind substituteCReturnT substFully g_ret
      in finish [] [] eff e_ret' g_ret'
  where
    -- Rename dependent parameter variables so that they have the same name.
    -- Given the expected and given type parameters, create substitutions for 
    -- the expected and given range types, respectively.
    -- 
    -- Also, a function parameter is created to hold the expected value.
    unify_parameters :: CBind CParamT SubstRec
                     -> CBind CParamT SubstRec
                     -> (CBind CParam Rec -> Substitution ->
                         Substitution -> EffEnv b)
                     -> EffEnv b
  
    -- Unify dependent parameter variables
    unify_parameters (ValPT e_mv ::: e_type) (ValPT g_mv ::: _) k = do
      -- Create a parameter variable
      let name = (varName =<< e_mv) `mplus` (varName =<< g_mv)
          level = pred $ getLevel $ substFully e_type
      param_var <- newVar name level

      -- Rename the types so that they use the same variable
      let make_subst Nothing  = mempty
          make_subst (Just v) = renaming v param_var

      -- Create a source parameter
      let src_param = ValP param_var ::: substFully e_type
          
      -- Add the parameter variable to the environment and continue
      gluon_param_type <- coreToGluonTypeWithoutEffects e_type
      assumePure param_var gluon_param_type $
        k src_param (make_subst e_mv) (make_subst g_mv)
      
    -- Unify parameter addresses
    unify_parameters (ReadPT e_addr ::: e_type) (ReadPT g_addr ::: _) k = do
      -- Create a parameter variable
      let name = varName e_addr `mplus` varName g_addr
      addr_var <- newVar name ObjectLevel
      ptr_var <- newVar name ObjectLevel
      
      -- Create a source parameter
      let src_param = ReadP addr_var ptr_var ::: substFully e_type
          
      -- Add the address variable to the environment
      assumePure addr_var addressType $
        k src_param (renaming e_addr addr_var) (renaming g_addr addr_var)
      
    -- The remaining cases do not involve unification
    unify_parameters (expected_bind ::: expected_type) given_param k =
      case expected_bind
      of ValPT mv -> do
           v <- case mv
                of Just v -> return v
                   Nothing -> newAnonymousVariable level
           gluon_param_type <- coreToGluonTypeWithoutEffects expected_type
           assumePure v gluon_param_type $ continue (ValP v)
         OwnPT -> do
           v <- newAnonymousVariable level
           continue (OwnP v)
         ReadPT addr -> do
           ptr <- newAnonymousVariable ObjectLevel
           assumePure addr addressType $ continue (ReadP addr ptr)
      where
        -- Parameter's level
        level = pred $ getLevel $ substFully expected_type

        -- Run continuation after constructing the function parameter and
        -- adding parameter variables to the environment
        continue binder = k (binder ::: substFully expected_type) mempty mempty
    
    coerce_and_continue :: CBind CParamT Rec
                        -> CBind CParam Rec
                        -> RecCType SubstRec
                        -> RecCFunType SubstRec
                        -> RecCFunType SubstRec
                        -> EffEnv a
    coerce_and_continue g_param src_param e_effect e_range g_range = do
      -- Coerce from expected to given parameter
      let src_bind ::: src_type = src_param
          param_level = pred $ getLevel src_type
          param_value = paramValue src_bind
          param_exp = ValCE (internalSynInfo param_level) param_value
          param_fexp = FlatExp { flattenedExp = param_exp 
                               , flattenedReturn = paramReturnType src_bind ::: src_type 
                               , flattenedDst = Nothing
                               }
      param_coercion <- coerceParameter g_param param_fexp
      
      -- Process remaining parameters
      coerceFunctionParameters e_range g_range e_effect $
        \params coercions e_eff e_ret g_ret ->
        finish (src_param : params) (param_coercion : coercions) e_eff e_ret g_ret

createFunctionCoercion :: RCExp              -- ^ Function to coerce
                       -> [CBind CParam Rec] -- ^ Parameter value binders
                       -> [ContextExp]       -- ^ Parameter coercions
                       -> RCType             -- ^ Expected effect type
                       -> CBind CReturnT Rec -- ^ Expected return type
                       -> CBind CReturnT Rec -- ^ Given return type
                       -> EffEnv RCExp       -- ^ Return a lambda expression
createFunctionCoercion original_function param_binders coercions expect_eff
                       expect_rt given_rt = do
  -- Call the original function with the converted parameters
  (return_arg, return_dst) <- makeReturnArgument given_rt
  let call_exp =
        AppCE { cexpInfo = internalSynInfo ObjectLevel
              , cexpOper = original_function
              , cexpArgs = map (flattenedExp . snd) coercions
              , cexpReturnArg = return_arg
              }
      call_fexp = FlatExp call_exp given_rt return_dst
  
  -- Coerce the return value to match the expected return
  return_binder <- make_return_binder expect_rt
  call_fexp' <- coerce Covariant return_binder call_fexp
  
  -- Wrap expression with context required for parameters
  let call_fexp'' = applyContextFlat (mconcat $ map fst coercions) call_fexp'
  
  -- Create a lambda function
  let wrapper_fun = CFun { cfunInfo = internalSynInfo ObjectLevel
                         , cfunParams = param_binders
                         , cfunReturn = return_binder
                         , cfunEffect = expect_eff
                         , cfunBody = flattenedExp call_fexp'' 
                         }
      lam_exp = LamCE (internalSynInfo ObjectLevel) wrapper_fun
  return lam_exp
  where
    -- From the expected the return type, create a return binder.
    -- It's not permitted to return a reference to an existing variable.
    make_return_binder (rbind ::: rtype) =
      case rbind
      of ValRT -> return (ValR ::: rtype)
         OwnRT -> return (OwnR ::: rtype)
         WriteRT -> do
           addr <- newAnonymousVariable ObjectLevel
           ptr <- newAnonymousVariable ObjectLevel
           return $ WriteR addr ptr ::: rtype
         ReadRT _ -> internalError "createFunctionCoercion"

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

  in do fexp <- coerce Covariant callable_type expr
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
      (return_arg, dst) <- makeReturnArgument ret_type
      let inf = mkSynInfo pos ObjectLevel
          exp = applyContext context $ AppCE inf op arg_exps return_arg
      return $ FlatExp exp ret_type dst

-- | Apply a function to some arguments.  Translate the arguments,
-- compute the return type, and return any un-processed arguments.
applyCallOperands :: RecCFunType SubstRec
                  -> [Effect.EIExp]
                  -> EffEnv (CBind CReturnT SubstRec, [(Context, RCExp)], [Effect.EIExp])
applyCallOperands op_type oprds = debug $ do
  op_type' <- freshenHead op_type
  go op_type' oprds id 
  where
    go (ArrCT {ctParam = param, ctRange = rng}) (oprd:oprds) hd = do
      (oprd', oprd_addr, oprd_type) <- applyCallOperand param oprd
      
      -- If the function is dependently typed, substitute the operand's type.
      -- If the function takes a pass-by-reference parameter, substitute the
      -- actual address that will be passed.
      rng' <- freshenHead $
              substitute_range (fromCBind param) (snd oprd') oprd_addr rng
      go rng' oprds (hd . (oprd':))

    go t@(ArrCT {}) [] hd = return (OwnRT ::: verbatim (funCT (substFullyUnder t)), hd [], [])

    go (RetCT rt) oprds hd = return (rt, hd [], oprds)
    
    substitute_range param oprd_exp oprd_addr rng =
      case param
      of ValPT (Just param_var) -> 
           -- Dependent type; operand must be a type
           case oprd_exp
           of ValCE {cexpVal = TypeV ty} ->
                verbatim $ assignTypeFun param_var ty rng
              _ -> internalError "applyCallOperands"

         ValPT Nothing -> rng   -- Non-dependent type
         OwnPT -> rng           -- Non-dependent
         ReadPT addr_var ->
           -- Borrowed parameter
           case oprd_addr
           of Just a_exp ->
                verbatim $ assignTypeFun addr_var (expCT a_exp) rng

    debug x
      | printCalls =
          let msg = text "applyCallOperands" $$
                    nest 4 (pprType $ FunCT $ substFully op_type) $$
                    nest 4 (vcat $ map Effect.pprExp oprds)
          in traceShow msg x
      | otherwise = x

-- | Flatten an operand of a function call and compute the call's side effect
-- and result type.
applyCallOperand :: CBind CParamT SubstRec
                 -> Effect.EIExp 
                 -> EffEnv ((Context, RCExp), Maybe (AddrExp Rec), RCType)
applyCallOperand param_type operand = do
  -- Flatten and coerce the operand
  arg_val <- flattenExp operand
  (arg_context, arg_val2) <-
    coerceParameter (substituteCBind substituteCParamT substFully param_type) arg_val
    
  let arg_type = cbindType $ flattenedReturn arg_val2
      arg_addr = case fromCBind $ flattenedReturn arg_val2 
                 of ReadRT e -> Just e
                    _ -> Nothing
  return ((arg_context, flattenedExp arg_val2), arg_addr, arg_type)

flattenDo expression ty pc body = do
  -- Create the type and passing convention arguments
  let type_value = ValCE type_info $ TypeV $ convertType ty
  pc_value <- flattenExp pc

  -- Flatten the body
  body_fun <- flattenDoBody body
  let body_exp = LamCE value_info body_fun
  
  -- Create a function call that builds a stream object
  let effect_value = ValCE type_info $ TypeV (cfunEffect body_fun)
      
  let oper = ValCE value_info $ OwnedConV $ pyonBuiltin the_fun_return

  let exp = AppCE { cexpInfo = value_info
                  , cexpOper = oper
                  , cexpArgs = [effect_value, type_value,
                                flattenedExp pc_value, body_exp]
                  , cexpReturnArg = Nothing
                  }
      
  -- The result has type (stream effect ty) 
  let stream_type = appCT (conCT $ pyonBuiltin the_LazyStream)
                    [cfunEffect body_fun, convertType ty]
  let flat_exp = FlatExp exp (OwnRT ::: stream_type) Nothing
  
  return flat_exp
  where
    type_info = mkSynInfo (getSourcePos expression) TypeLevel
    value_info = mkSynInfo (getSourcePos expression) ObjectLevel

-- | Flatten the body of a 'do' expression.  Creates a lambda function that
-- takes no regular parameters and has one return parameter.
flattenDoBody body = do
  -- Get the expression's return and effect types
  (return_conv, return_type) <-
    convertPassType (Effect.eiReturnType body) (Effect.eiType body)
  fun_effect <- convertEffect $ Effect.eiEffect body
  
  -- Create a binder for the return value.  Return values are always
  -- passed using the 'borrowed' convention.
  rbinder <- createReturnBinder Borrowed return_type
  
  -- Flatten the expression and coerce its result to 'borrowed'
  body_exp <- flattenExp body 
  body_exp' <- coerce Contravariant rbinder body_exp
  
  -- Create an unused parameter so that the function has one
  param_var <- newAnonymousVariable ObjectLevel
  let param_binder = ValP param_var ::: conCT (pyonBuiltin the_NoneType)
  
  -- Create the lambda function
  let new_fun = CFun { cfunInfo = mkSynInfo (getSourcePos body) ObjectLevel
                     , cfunParams = [param_binder]
                     , cfunReturn = rbinder
                     , cfunEffect = fun_effect
                     , cfunBody = flattenedExp body_exp'
                     }
  return new_fun

flattenLet expression b rhs body = do
  rhs' <- flattenExp rhs
  convertLetBinder b $ \b' -> do
    rhs'' <- coerce Covariant (letBinderReturn b') rhs'
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
          alt_bodies' <- mapM (coerce Contravariant return_binder) alt_bodies
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
           -> EffEnv ((Con, [RCType], [CBind CParam Rec]), FlatExp)
flattenAlt pos alt = do
  -- Convert type arguments
  let ty_arg_info = mkSynInfo pos TypeLevel
  let ty_args = map convertType $ Effect.eialtTyArgs alt

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
  withMany convertParameter (Effect.funParams fun) $ \binders -> do
  
  -- Convert the return type and create a return binder
    (return_conv, return_type) <-
      convertMonoPassType
      (Effect.funReturnPassType fun)
      (Effect.fromEIType $ Effect.funReturnType fun)
    ret_binder <- createReturnBinder return_conv return_type
    
    -- Flatten the function body
    body_exp <- flattenExp $ Effect.funBody fun
    body_exp' <- coerce Contravariant ret_binder body_exp
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

flattenDef (Effect.Def v fun) = do
  fun' <- flattenFun fun
  return $ CDef v fun'

flattenExport (Effect.Export pos spec f) = do
  f' <- flattenFun f
  return $ CExport (mkSynInfo pos ObjectLevel) spec f'

flattenModule defss exports = do
  defss' <- mapM (mapM flattenDef) defss
  exports' <- mapM flattenExport exports
  return (defss', exports')

flatten :: SystemF.Module SystemF.TypedRec -> IO (CModule Rec)
flatten mod = do
  -- Run effect inference
  (mname, effect_defss, effect_exports) <- Effect.runEffectInference mod
  
  -- Run flattening
  (flattened_defs, flattened_exports) <-
    withTheVarIdentSupply $ \var_supply ->
    let env = cleanEnv var_supply
    in runReaderT (runEffEnv $ flattenModule effect_defss effect_exports) env
  let flattened_module = CModule mname flattened_defs flattened_exports

  -- DEBUG: print flattened code
  putStrLn "Flattened"
  print $ pprCModule flattened_module
  
  return flattened_module
