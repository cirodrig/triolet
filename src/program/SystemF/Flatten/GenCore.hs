
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances, ViewPatterns #-}
module SystemF.Flatten.GenCore(mkGlobalRegions, generateCore)
where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.ST
import Control.Monad.Trans

import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import Data.Maybe
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.Label
import Gluon.Common.MonadLogic
import Gluon.Common.SourcePos
import Gluon.Common.Supply
import Gluon.Core.Level
import Gluon.Core(SynInfo, Var, Con, conID, Rec)
import qualified Gluon.Core.Builtins as Gluon
import qualified Gluon.Core as Gluon
import qualified Gluon.Eval.Environment as Gluon
import qualified Gluon.Eval.Equality as Gluon
import qualified SystemF.Builtins as SF
import SystemF.Flatten.Effect
import SystemF.Flatten.EffectType
import SystemF.Flatten.EffectExp
import qualified Core.Print as Core
import qualified Core.Syntax as Core
import qualified Core.BuiltinTypes as Core
import qualified Core.Gluon as Core
import Core.Syntax(Representation(..), CBind((:::)))
import Globals

-- | Create an effect expression representing reading a value of type @ty@
-- at address @addr@.
mkReadEffect ty addr =
  Core.appCT (Core.conCT $ Gluon.builtin Gluon.the_AtE) [ty, addr]

mkEmptyEffect = Core.conCT (Gluon.builtin Gluon.the_EmpE)

mkPairEffect :: Core.RCType -> Core.RCType -> Core.RCType
mkPairEffect x y =
  Core.appCT (Core.conCT $ Gluon.builtin Gluon.the_SconjE) [x, y]

-- | Each effect variable that is bound as a parameter somewhere 
-- is mapped to a corresponding Core variable.
type EffectVarMap = Map.Map EVar Var

-- | Each region variable that is bound as a parameter somewhere 
-- is mapped to an address variable and type.
type RegionVarMap = Map.Map RVar RegionVarBinding

data RegionVarBinding = RVB !Var !Var !Core.RCType

data GenCoreEnv =
  GenCoreEnv
  { envFresh     :: {-# UNPACK #-} !(IdentSupply Var)
  , envEffectMap :: EffectVarMap
  , envRegionMap :: RegionVarMap
  , envTypes     :: Map.Map Var VarBinding
    -- | A list of types that are in scope, from most recently bound to least 
    --   recently bound.  Only Value variables are put into this list, since 
    --   those are the only ones that can appear inside another type.
    --   This list is used to construct a 'Gluon.PureTC' environment.
  , envTypeList  :: [(Var, Core.RCType)]
  }

-- | Regions for global variables.  Global variables are constructors in
-- System F and they become variables in Core.
--
-- Returns the region variable map (used in GenCore) and the region inhabited
-- by each constructor (used in EffectInference).
--
-- This function is kind of a hack because we don't have proper support for
-- global variables.
mkGlobalRegions :: RegionMonad m => m (RegionVarMap, IntMap.IntMap RVar)
mkGlobalRegions = do 
  (r_assocs, c_assocs) <- mapAndUnzipM mk_entry globals
  return (Map.fromList r_assocs, IntMap.fromList c_assocs)
  where
    mk_entry (con, addr_var, ptr_var) = do
      rvar <- newRegionVar False
      return ((rvar, RVB addr_var ptr_var (Core.conCoreType con)),
              (fromIdent $ conID con, rvar))
    
    globals = [ (SF.pyonBuiltin SF.the_passConv_int,
                 SF.pyonBuiltin SF.the_passConv_int_addr,
                 SF.pyonBuiltin SF.the_passConv_int_ptr)
              ]

setupGenCoreEnv :: IdentSupply Var -> RegionVarMap -> IO GenCoreEnv
setupGenCoreEnv var_supply rvmap = do
  return (GenCoreEnv var_supply Map.empty rvmap Map.empty [])

data VarBinding = ValVB !Core.RCType 
                | OwnVB !Core.RCType 
                | ReadVB !(Core.AddrExp Rec) !Core.PtrVar !Core.RCType

varBindingType :: VarBinding -> Core.RCType
varBindingType (ValVB t) = t
varBindingType (OwnVB t) = t
varBindingType (ReadVB a _ t) = t

varBindingReturnType :: VarBinding -> Core.CBind Core.CReturnT Rec
varBindingReturnType binding = return_repr ::: varBindingType binding 
  where
    return_repr =
      case binding
      of ValVB _      -> Core.ValRT
         OwnVB _      -> Core.OwnRT
         ReadVB a _ _ -> Core.ReadRT a

varBindingValue :: Var -> VarBinding -> Core.Value Rec
varBindingValue v binding =
  case binding
  of ValVB _ -> Core.ValueVarV v
     OwnVB _ -> Core.OwnedVarV v
     ReadVB a p t -> Core.ReadVarV a p

-- | A description of what variables to use when creating return variables 
data RetBinding = ValRB Core.RCType
                | OwnRB Core.RCType
                | ReadRB !Core.AddrVar !Core.PtrVar Core.RCType
                | WriteRB !Core.AddrVar !Core.PtrVar Core.RCType

retBindingType :: RetBinding -> Core.RCType
retBindingType (ValRB t) = t
retBindingType (OwnRB t) = t
retBindingType (ReadRB _ _ t) = t
retBindingType (WriteRB _ _ t) = t

retBindingVarBinding :: RetBinding -> VarBinding
retBindingVarBinding (ValRB t) = ValVB t
retBindingVarBinding (OwnRB t) = OwnVB t
retBindingVarBinding (ReadRB a p t) = ReadVB (Gluon.mkInternalVarE a) p t 
retBindingVarBinding (WriteRB a p t) = ReadVB (Gluon.mkInternalVarE a) p t

retBindingLetBinder :: Var -> RetBinding -> Core.CBind Core.LetBinder Rec
retBindingLetBinder v (ValRB t) = Core.ValB v ::: t
retBindingLetBinder v (OwnRB t) = Core.OwnB v ::: t
retBindingLetBinder _ (ReadRB a p t) = Core.RefB (Gluon.mkInternalVarE a) p ::: t
retBindingLetBinder _ (WriteRB a p t) = Core.LocalB a p ::: t

-- | Create the function argument corresponding to this return binding
retBindingArgument :: RetBinding -> Maybe Core.RCExp
retBindingArgument (ValRB _) = Nothing
retBindingArgument (OwnRB _) = Nothing
retBindingArgument (ReadRB a p _) = Nothing
retBindingArgument (WriteRB a p _) =
  Just (Core.writePointerRV noSourcePos (Gluon.mkInternalVarE a) p)

assignEffect :: EVar -> Var -> GenCoreEnv -> GenCoreEnv
assignEffect v v' e =
  e {envEffectMap = Map.insert v v' $ envEffectMap e}

assignRegion :: RVar -> Var -> Var -> Core.RCType -> GenCoreEnv -> GenCoreEnv
assignRegion v addr_var ptr_var t e =
  e {envRegionMap = Map.insert v (RVB addr_var ptr_var t) $ envRegionMap e}

-- | Assign a type, address, and representation to a variable
assignType :: Var -> VarBinding -> GenCoreEnv -> GenCoreEnv
assignType v rt e =
  e { envTypes = Map.insert v rt $ envTypes e
    , envTypeList = case rt
                    of ValVB core_type -> (v, core_type) : envTypeList e
                       _ -> envTypeList e}

newtype GenCore a = GenCore {runGenCore :: ReaderT GenCoreEnv IO a}

doGenCore :: GenCoreEnv -> GenCore a -> IO a
doGenCore env (GenCore m) = runReaderT m env

instance Functor GenCore where
  fmap f (GenCore m) = GenCore (fmap f m)

instance Monad GenCore where
  return x = GenCore (return x)
  GenCore m >>= k = GenCore (m >>= runGenCore . k)

instance MonadIO GenCore where
  liftIO m = GenCore (liftIO m)

instance Supplies GenCore (Ident Var) where
  fresh = GenCore $ ReaderT $ \env -> supplyValue (envFresh env)
  supplyToST m = GenCore $ ReaderT $ \env ->
    let get_fresh = unsafeIOToST (supplyValue (envFresh env))
    in stToIO (m get_fresh)

instance Gluon.EvalMonad GenCore where
  liftEvaluation m = GenCore $ ReaderT $ \env -> do
    case Gluon.runEval (envFresh env) m of
      Just x -> return x
      Nothing -> internalError "GenCore: Evaluation failed"

-- | Embed a PureTC computation into the Core monad
doPureTC :: Gluon.PureTC a -> GenCore a
doPureTC m = GenCore $ ReaderT $ \env -> do
  case Gluon.runPureTC (envFresh env) $
       foldl add_to_environment m (envTypeList env) of
    Right x -> return x
    Left errs -> fail "GenCore: Evaluation failed"
  where
    add_to_environment m (v, ty) = do
      ty' <- Core.coreToGluonType $ Gluon.verbatim ty
      Gluon.assumePure v ty' m
  
-- | Create a translation for an effect variable.  The variable is translated
-- to a core variable representing an effect.
withEVar :: EVar -> (Var -> GenCore a) -> GenCore a
withEVar v k = do
  v' <- liftIO $ evalEVar v              -- Look through unification
  core_v <- Gluon.newAnonymousVariable TypeLevel
  GenCore $ local (assignEffect v' core_v) $ runGenCore (k core_v)

-- | Create a translation for a region variable.  The variable is translated
-- to a core variable representing an address.  The corresponding effect is
-- to read the variable.
withRVar :: Maybe Label -> RVar -> Core.RCType
         -> (Var -> Var -> GenCore a) -> GenCore a
withRVar mname v ty k = do
  v' <- liftIO $ evalRVar v              -- Look through unification
  core_addr <- Gluon.newVar mname ObjectLevel
  core_ptr <- Gluon.newVar mname ObjectLevel
  GenCore $ local (assignRegion v' core_addr core_ptr ty) $
    runGenCore (k core_addr core_ptr)

-- | Look up a region variable's translation
lookupRegion rv = do 
  rv' <- liftIO $ evalRVar rv
  GenCore $ asks $ \env -> fromEntry $ Map.lookup rv' $ envRegionMap env
  where
    fromEntry (Just (RVB addr_var ptr_var t)) = (addr_var, ptr_var, t)
    fromEntry Nothing = internalError $ "lookupRegion: not found: " ++ show (pprEffectVar rv)

-- | Look up an effect variable's translation
lookupEffect ev = do
  ev' <- liftIO $ evalEVar ev
  GenCore $ asks $ \env -> fromEntry $ Map.lookup ev' $ envEffectMap env
  where
    fromEntry (Just v) = v
    fromEntry Nothing = internalError $ "lookupEffect: not found " ++ show (pprEffectVar ev)

withType v ty m = GenCore $ local (assignType v ty) (runGenCore m)

lookupType :: Var -> GenCore VarBinding
lookupType v = GenCore $ asks $ \env -> fromEntry $ Map.lookup v $ envTypes env
  where
    fromEntry (Just v) = v
    fromEntry Nothing  = internalError "lookupType: not found"

-- | Get a list of all variables that are in scope
getAllVariables :: GenCore [(Var, VarBinding)]
getAllVariables = GenCore $ asks (Map.toList . envTypes)

-- | Print the environment
dumpEnvironment :: GenCore ()
dumpEnvironment = GenCore $ ReaderT $ \env -> do
  print (show_effect_map $ envEffectMap env)
  print (show_region_map $ envRegionMap env)
  print (show_types $ envTypes env)
  where
    show_effect_map m =
      text "Effects:" $$
      nest 4 (vcat [pprEffectVar e <+> Gluon.pprVar v | (e, v) <- Map.toList m])

    show_region_map m =
      text "Regions:" $$
      nest 4 (vcat [pprEffectVar r <+> Gluon.pprVar v <+> text ":" <+> Core.pprType t
                   | (r, RVB v _ t) <- Map.toList m])

    show_types m =
      text "Types:" $$
      nest 4 (vcat [Gluon.pprVar v | (v, _) <- Map.toList m])

-------------------------------------------------------------------------------
-- Conversion from effect types to core types

etypeToCoreType :: EType -> GenCore Core.RCType
etypeToCoreType ty =
  case ty
  of AppT op args ->
       liftM2 Core.appCT (etypeToCoreType op) (mapM etypeToCoreType args)
     InstT varcon effs ->
       let op = case varcon
                of Left v -> Core.ExpCT (Gluon.mkInternalVarE v)
                   Right c -> Core.ExpCT (Gluon.mkInternalConE c)
       in liftM (Core.appCT op) (mapM effectToCoreEffect effs)
     FunT {} -> fmap Core.funCT $ etypeToCoreFunType ty
     VarT v -> return (Core.varCT v)
     ConT c -> return (Core.conCT c)
     LitT l -> return (Core.litCT l)

etypeToCoreFunType ty =
  case ty
  of FunT param eff rng -> to_fun_type param eff rng
     _ -> internalError "etypeToCoreFunType: Not a function type"
  where
    to_fun_type param eff rng =
      eParamTypeToCoreType param $ \param' -> do
        eff' <- effectToCoreEffect eff 
        rng' <- to_return_type rng
        return $ Core.ArrCT param' eff' rng'

    to_return_type rt =
      case rt
      of OwnRT (FunT param eff rng) -> to_fun_type param eff rng
         _ -> fmap Core.RetCT $ eReturnTypeToCoreType rt

eParamTypeToCoreType :: EParamType
                     -> (Core.CBind Core.CParamT Rec -> GenCore a)
                     -> GenCore a
eParamTypeToCoreType pt k = do
  t' <- etypeToCoreType $ paramTypeType pt
  case pt of
    ValPT mv _ -> k (Core.ValPT mv ::: t')
    OwnPT _    -> k (Core.OwnPT ::: t')
    ReadPT r _ -> withRVar Nothing r t' $ \addr ptr ->
      k (Core.ReadPT addr ::: t')

withReturnType :: EReturnType
               -> (RetBinding -> GenCore a)
               -> GenCore a
withReturnType rt k = do
  t <- etypeToCoreType $ returnTypeType rt
  case rt of
    ValRT _       -> k (ValRB t)
    OwnRT _       -> k (OwnRB t)
    ReadRT rgn _  -> do
      (addr, ptr, ty) <- lookupRegion rgn
      k (ReadRB addr ptr ty)
    WriteRT rgn _ -> withRVar Nothing rgn t $ \addr ptr ->
      k (WriteRB addr ptr t)

-- | Convert a return type to a core type
eReturnTypeToCoreType :: EReturnType
                      -> GenCore (Core.CBind Core.CReturnT Rec)
eReturnTypeToCoreType rt = withReturnType rt (return . make_return_type)
  where
    make_return_type (ValRB t) = Core.ValRT ::: t
    make_return_type (OwnRB t) = Core.OwnRT ::: t
    make_return_type (ReadRB a _ t) =
      Core.ReadRT (Gluon.mkInternalVarE a) ::: t
    make_return_type (WriteRB _ _ t) =
      Core.WriteRT ::: t

lookupReturnType :: EReturnType
                 -> GenCore (Core.CBind Core.CReturn Rec)
lookupReturnType rt = do                        
  t <- etypeToCoreType $ returnTypeType rt
  case rt of
    ValRT _ -> return (Core.ValR ::: t)
    OwnRT _ -> return (Core.OwnR ::: t)
    ReadRT rgn _ -> do
      (addr, ptr, _) <- lookupRegion rgn
      return (Core.ReadR (Gluon.mkInternalVarE addr) ptr ::: t) 
    WriteRT rgn _ -> do
      (addr, ptr, _) <- lookupRegion rgn
      return (Core.WriteR addr ptr ::: t)

-- | Construct the Core side effect expression corresponding to an
-- effect variable.  Unifications are evaluated.
effectVarEffect :: EffectVar -> GenCore Core.RCType
effectVarEffect v
  | isEVar v = as_effect . fromEffect =<< liftIO (evalEffectVar v)
  | otherwise = as_effect [v]
  where
    as_effect [] = return mkEmptyEffect
    as_effect vs = fmap (foldr1 mkPairEffect) $ mapM as_effect_variable vs

    as_effect_variable v
      | isEVar v = do core_v <- lookupEffect v
                      return $ Core.varCT core_v
      | isRVar v = do (addr, _, ty) <- lookupRegion v
                      return $ mkReadEffect ty (Core.varCT addr)

-- | Construct the Core side effect expression corresponding to an effect
effectToCoreEffect :: Effect -> GenCore Core.RCType
effectToCoreEffect effect = do
  effects <- mapM effectVarEffect =<< liftIO (effectMembers effect)
  return $ foldr mkPairEffect mkEmptyEffect effects

-------------------------------------------------------------------------------
-- Conversion from effect inference expressions to core expressions

-- The conversion functions create new region and pointer variables for
-- System F variables and temporary values that were deemed pass-by-reference. 
-- The code is structured carefully so that each variable gets renamed only
-- once.

-- | Find the parameter-passing convention of this type
findPassConv :: Core.RCType -> GenCore (Maybe (Core.Value Rec))
findPassConv ty = do 
  gl_ty <- Core.coreToGluonTypeWithoutEffects (Gluon.verbatim ty)
  match <- doPureTC . findM (match_type gl_ty) =<< getAllVariables
  return $! case match
            of Nothing -> Nothing
               Just (v, b) -> Just (varBindingValue v b)
  where
    match_type gl_ty (v, binding@(ReadVB _ _ v_type))
      | Just (con, [dict_type]) <- Core.unpackConAppCT v_type,
        con `SF.isPyonBuiltin` SF.the_PassConv = do

          -- This is a PassConv dictionary.  Does it have the right type?
          gl_dict_type <- Core.coreToGluonType (Gluon.verbatim dict_type)
          Gluon.testSubtyping (Gluon.verbatim gl_ty) (Gluon.verbatim gl_dict_type)

      | otherwise = return False
    match_type _ (_, _) = return False


withEffectParameter :: EVar -> (Core.CBind Core.CParam Rec -> GenCore a)
                    -> GenCore a
withEffectParameter ev f = withEVar ev $ \v ->
  f (Core.ValP v ::: Core.expCT Gluon.effectKindE)

withEffectParameters = withMany withEffectParameter

withParameter :: EParam -> (Core.CBind Core.CParam Rec -> GenCore a)
              -> GenCore a
withParameter param f = do
  t <- etypeToCoreType $ paramType param
  case param of
    ValP v _    -> withType v (ValVB t) $ f (Core.ValP v ::: t)
    OwnP v _    -> withType v (OwnVB t) $ f (Core.OwnP v ::: t)
    ReadP v r _ -> withRVar param_name r t $ \addr ptr -> do
      let addr_exp = Gluon.mkInternalVarE addr
      withType v (ReadVB addr_exp ptr t) $ f (Core.ReadP addr ptr ::: t)
  where
    param_name = Gluon.varName $ paramVar param

withParameters = withMany withParameter

-- | Generate core code from an expression that returns a value or owned 
-- result.
toNonReferenceCoreExp :: EExp -> GenCore Core.RCExp
toNonReferenceCoreExp expression
  | valid_return_type =
      withReturnType (expReturn expression) $ \rb -> toCoreExp rb expression
  | otherwise = internalError "toNonReferenceCoreExp"
  where
    valid_return_type =
      case expReturn expression
      of ValRT {} -> True
         OwnRT {} -> True
         _ -> False

-- | Generate core code from an expression.  This function cannot generate code
-- from a coercion expression that allocates temporary storage.
toCoreExp :: RetBinding -> EExp -> GenCore Core.RCExp
toCoreExp rb expression = debug $
  case expExp expression of
    VarE v ->
      convertVarE rb inf v
    ConE c ->
      convertConE rb inf c
    LitE l t ->
      convertLitE rb inf l t
    TypeE ty ->
      convertTypeE rb inf ty
    InstE op effs ->
      convertCall rb inf (Left op) effs []
    CallE (expExp -> InstE op effs) args ->
      convertCall rb inf (Left op) effs args
    CallE op args ->
      convertCall rb inf (Right op) [] args
    FunE f -> do
      f' <- toCoreFun f
      return $ Core.LamCE inf f'
    DoE ty pc body ->
      convertDoE rb inf ty pc body
    LetE lhs lhs_ty rhs body ->
      convertLetE rb inf lhs lhs_ty rhs body
    LetrecE defs body ->
      convertLetrecE rb inf defs body
    CaseE scr alts ->
      convertCaseE rb inf scr alts
    GenLoadValue body -> generate_load body
    GenTempLoadValue _ -> toFreeCoreCoExp expression return
    GenLoadOwned body -> generate_load body
    GenTempLoadOwned _ -> toFreeCoreCoExp expression return
    GenStoreValue body -> generate_store body
    GenStoreOwned body -> generate_store body
    _ -> internalError "toCoreExp: Unexpected expression"
  where
    inf = expInfo expression
    
    debug x =
      traceShow (text "toCoreExp" <+> pprEExp expression) x

    -- Load the value and pass to the continuation
    generate_load body =
      withReturnType (expReturn body) $ \body_rb -> do
        body' <- toCoreExp body_rb body
        genLoad (returnTypeType $ expReturn body) body_rb body'
      
    -- Store the value and pass to the continuation
    generate_store body = do
      body' <- toNonReferenceCoreExp body
      genStore rb (returnTypeType $ expReturn expression) body'

-- | Generate code for an expression, in situations where the return variable
-- is not visible outside of the expression and its consumer.
toFreeCoreCoExp :: EExp  -- ^ Expression possibly involving a coercion
                -> (Core.RCExp -> GenCore Core.RCExp) -- ^ User of the coerced value
                -> GenCore Core.RCExp           -- ^ Code generator
toFreeCoreCoExp e k =
  withReturnType (expReturn e) $ \rb -> toCoreCoExp rb e k

-- | Generate code for any expression.  This may result in inserting code  
--   around the expression's consumer.
--
--   The cases that don't involve generating code around the consumer are 
--   handled by 'toCoreExp'.
toCoreCoExp :: RetBinding
            -> EExp             -- ^ Expression possibly involving a coercion
            -> (Core.RCExp -> GenCore Core.RCExp) -- ^ User of the coerced value
            -> GenCore Core.RCExp           -- ^ Code generator
toCoreCoExp rb expression k =
  case expExp expression
  of GenTempLoadValue body -> generate_load_from_temporary body
     GenTempLoadOwned body -> generate_load_from_temporary body
     GenTempStoreValue body -> generate_store_to_temporary body
     GenTempStoreOwned body -> generate_store_to_temporary body
     _ | WriteRB a p t <- rb -> do
       core_expr <- toCoreExp rb expression

       -- Create a let expression for storing the intermediate result
       -- Make a load expression to read the temporary variable
       let use_value = Core.ValCE (expInfo expression) $
                       Core.ReadVarV (Gluon.mkInternalVarE a) p
       user <- k use_value
       
       let binder = Core.LocalB a p ::: t
       return $ Core.LetCE (Core.cexpInfo user) binder core_expr user

     _ -> k =<< toCoreExp rb expression -- Not a coercion
  where
    -- Create an expression:
    -- > let x = (...)
    -- > in ... (load x)
    generate_load_from_temporary body =
      -- Translate the expression's return address
      withReturnType (expReturn body) $ \body_rb -> do
        -- Translate the expression and assign to a temporary variable
        body' <- toCoreExp body_rb body
        let_var <- Gluon.newAnonymousVariable ObjectLevel
        let let_binder = retBindingLetBinder let_var body_rb
            
        -- Make a load expression to read the temporary variable
        use_var <- case expReturn body
                   of WriteRT rgn _ -> do
                        (addr, ptr, _) <- lookupRegion rgn
                        return $ Core.ReadVarV (Gluon.mkInternalVarE addr) ptr
        use_value <- genLoad (returnTypeType $ expReturn expression) rb $ 
                     Core.ValCE (expInfo expression) use_var

        -- Generate the code that uses this value 
        user_exp <- k use_value

        -- Wrap in a let binding
        let let_expr = Core.LetCE { Core.cexpInfo = expInfo expression
                                  , Core.cexpBinder = let_binder
                                  , Core.cexpRhs = body'
                                  , Core.cexpBody = user_exp}
        return let_expr
      
    generate_store_to_temporary body =
      let store_dest = case expReturn expression
                       of ReadRT a t -> WriteRT a t
                          x@(WriteRT {}) -> x
      in withReturnType store_dest $ \body_rb -> do
        -- Translate the expression and store it
        body' <- toNonReferenceCoreExp body
        body'' <- genStore body_rb (returnTypeType $ expReturn expression) body'
    
        -- Translate the user of the expression
        let_var <- Gluon.newAnonymousVariable ObjectLevel
        let let_binder = retBindingLetBinder let_var body_rb
            use_value = case body_rb
                        of WriteRB a p t ->
                             Core.ReadVarV (Gluon.mkInternalVarE a) p
        user_exp <- k (Core.ValCE (expInfo expression) use_value)

        -- Wrap in a let binding
        let let_expr = Core.LetCE { Core.cexpInfo = expInfo expression
                                  , Core.cexpBinder = let_binder
                                  , Core.cexpRhs = body''
                                  , Core.cexpBody = user_exp}
        return let_expr

-- | Generate code to load the expression's return value.  The return value
-- must be a 'ReadRT' value.
genLoad :: EType -> RetBinding -> Core.RCExp -> GenCore Core.RCExp
genLoad ty expr_rb expr =
  let oper = Core.ValCE { Core.cexpInfo = inf
                        , Core.cexpVal = Core.OwnedConV load_function
                        }
      load_expr = Core.AppCE { Core.cexpInfo = inf
                             , Core.cexpOper = oper
                             , Core.cexpArgs = [expr]
                             , Core.cexpReturnArg = retBindingArgument expr_rb
                             }
  in return load_expr
  where
    inf = Gluon.mkSynInfo pos ObjectLevel
    pos = getSourcePos expr
    
    load_function =
      case ty
      of ConT c
           | c `SF.isPyonBuiltin` SF.the_int -> SF.pyonBuiltin SF.the_fun_load_int
           | c `SF.isPyonBuiltin` SF.the_float -> SF.pyonBuiltin SF.the_fun_load_float
           | c `SF.isPyonBuiltin` SF.the_bool -> SF.pyonBuiltin SF.the_fun_load_bool
           | c `SF.isPyonBuiltin` SF.the_NoneType -> SF.pyonBuiltin SF.the_fun_load_NoneType
         _ -> internalError "genLoad: Cannot load values of this type"

genStore :: RetBinding -> EType -> Core.RCExp -> GenCore Core.RCExp 
genStore rb ty expr =
  let oper = Core.ValCE { Core.cexpInfo = inf
                        , Core.cexpVal = Core.OwnedConV store_function
                        }
      store_expr = Core.AppCE inf oper [expr] (retBindingArgument rb)
  in return store_expr
  where
    inf = Gluon.mkSynInfo pos ObjectLevel
    pos = getSourcePos expr
    
    store_function =
      case ty
      of ConT c
           | c `SF.isPyonBuiltin` SF.the_int -> SF.pyonBuiltin SF.the_fun_store_int
           | c `SF.isPyonBuiltin` SF.the_float -> SF.pyonBuiltin SF.the_fun_store_float
           | c `SF.isPyonBuiltin` SF.the_bool -> SF.pyonBuiltin SF.the_fun_store_bool
           | c `SF.isPyonBuiltin` SF.the_NoneType -> SF.pyonBuiltin SF.the_fun_store_NoneType
         _ -> internalError "genStore: Cannot store values of this type"

-- | Copy data from one place to another.  The source must be a read reference
-- and the destination must be a write reference.
genCopy :: RetBinding -> Core.RCExp -> GenCore Core.RCExp
genCopy rb@(WriteRB a p ty) source = do
  mpass_conv <- findPassConv ty
  case mpass_conv of
    Just pass_conv -> do
      return $ copy_expr ty pass_conv
    Nothing -> internalError "genCopy: Cannot generate copying code"
  where
    copy_expr ty pass_conv =
      let type_expr =
            Core.ValCE (Gluon.internalSynInfo TypeLevel) $ Core.TypeV ty
          pc_expr =
            Core.ValCE (Gluon.internalSynInfo ObjectLevel) pass_conv
      in Core.AppCE (Core.cexpInfo source) copy_oper [type_expr, pc_expr, source] (retBindingArgument rb)
         
    copy_oper =
      Core.ValCE (Gluon.internalSynInfo ObjectLevel) $
      Core.OwnedConV (SF.pyonBuiltin SF.the_fun_copy)

convertVarE :: RetBinding -> SynInfo -> Var -> GenCore Core.RCExp
convertVarE rb inf v =
  case rb
  of ValRB _ -> return_value $ Core.ValueVarV v
     OwnRB _ -> return_value $ Core.OwnedVarV v
     ReadRB a p _ -> return_value $ Core.ReadVarV (Gluon.mkInternalVarE a) p
     WriteRB _ _ _ -> do
       var_binding <- lookupType v
       case var_binding of
         ReadVB src_a src_p _ ->
           let source_expr = Core.ValCE inf $ Core.ReadVarV src_a src_p
           in genCopy rb source_expr
  where
    return_value x = return $ Core.ValCE inf x

convertConE rb inf c = do
  let rt = Core.conCoreReturnType c
  let value = case Core.fromCBind rt
              of Core.ValRT -> Core.ValueConV c
                 Core.OwnRT -> Core.OwnedConV c
                 Core.ReadRT {}
                   | c `SF.isPyonBuiltin` SF.the_passConv_int ->
                       Core.ReadVarV (Gluon.mkInternalVarE (SF.pyonBuiltin SF.the_passConv_int_addr)) (SF.pyonBuiltin SF.the_passConv_int_ptr)

                 _ -> internalError "convertConE"
  return (Core.ValCE inf value)

convertLitE rb inf l t = 
  return (Core.ValCE inf (Core.LitV l))

convertTypeE rb inf ty = do
  core_ty <- etypeToCoreType ty
  return (Core.ValCE inf (Core.TypeV core_ty))

convertCall :: RetBinding                   -- ^ Return binding
            -> SynInfo                      -- ^ Source information
            -> Either (Either Var Con) EExp -- ^ Operator
            -> [Effect]                     -- ^ Effect arguments
            -> [EExp]                       -- ^ Other arguments
            -> GenCore Core.RCExp
convertCall rb inf op effs args =
  with_operator $ \op' -> do
    effs' <- mapM make_effect_param effs
    withMany toFreeCoreCoExp args $ \args' ->
      let expr = Core.AppCE { Core.cexpInfo = inf
                            , Core.cexpOper = op'
                            , Core.cexpArgs = effs' ++ args'
                            , Core.cexpReturnArg = retBindingArgument rb
                            }
      in return expr
  where
    with_operator k =
       case op
       of Left (Left v)  -> k =<< convertVarE (OwnRB undefined) inf v
          Left (Right c) -> k =<< convertConE (OwnRB undefined) inf c
          Right op_exp   -> toFreeCoreCoExp op_exp k

    make_effect_param effect = do
      effect_type <- effectToCoreEffect effect
      return $ Core.ValCE inf (Core.TypeV effect_type)

convertDoE rb inf ty_arg pass_conv body =
  toFreeCoreCoExp pass_conv $ \pass_conv' -> do
    ty_arg' <- toNonReferenceCoreExp ty_arg

    -- Look up the effect type from the returned stream's type
    let eff =
          case rb
          of OwnRB (Core.unpackConAppCT -> Just (con, eff : _))
               | con `SF.isPyonBuiltin` SF.the_LazyStream -> eff
             _ -> internalError "convertDoE: Unexpected return type"
    
    -- Create a lambda function for the body
    body_exp <- withReturnType (expReturn body) $ \body_rb -> do
      body' <- toCoreExp body_rb body
      return_binder <- lookupReturnType $ expReturn body
      
      let fun = Core.CFun { Core.cfunInfo = expInfo body
                          , Core.cfunParams = []
                          , Core.cfunEffect = eff
                          , Core.cfunReturn = return_binder
                          , Core.cfunBody = body'
                          }
          lam = Core.LamCE (expInfo body) fun
      return lam

    -- Construct the stream expression
    let stream_exp = Core.AppCE (expInfo body) stream_op
                     [Core.ValCE inf (Core.TypeV eff), ty_arg', pass_conv',
                      body_exp]
                     Nothing
    return stream_exp
  where
    stream_op = Core.ValCE inf (Core.OwnedConV (SF.pyonBuiltin SF.the_fun_return))

convertLetE body_rb inf lhs lhs_type rhs body =
  withReturnType (expReturn rhs) $ \rhs_rb -> do
    rhs' <- toCoreExp rhs_rb rhs
    withType lhs (retBindingVarBinding rhs_rb) $ do
      body' <- toCoreExp body_rb body
      return $ Core.LetCE inf (retBindingLetBinder lhs rhs_rb) rhs' body'

convertLetrecE rb inf defs body = convertDefGroup defs $ \defs' -> do
  body' <- toCoreExp rb body
  return $ Core.LetrecCE inf defs' body'

convertCaseE rb inf scr alts =
  toFreeCoreCoExp scr $ \scr' -> do
    -- Convert alternatives
    alts' <- mapM (convertAlt rb inf) alts
    
    -- Create case statement
    return $ Core.CaseCE { Core.cexpInfo = inf
                         , Core.cexpScrutinee = scr'
                         , Core.cexpAlternatives = alts'}

convertAlt :: RetBinding -> SynInfo -> EAlt -> GenCore Core.RCAlt
convertAlt rb inf alt = do 
  types <- mapM etypeToCoreType $ ealtTyArgs alt 
  withParameters (ealtParams alt) $ \params -> do
    body <- toCoreExp rb $ ealtBody alt
    
    return $ Core.CAlt { Core.caltInfo = inf
                       , Core.caltConstructor = ealtCon alt
                       , Core.caltTyArgs = types
                       , Core.caltParams = params
                       , Core.caltBody = body
                       }

toCoreFun :: EFun -> GenCore Core.RCFun
toCoreFun efun =
  withEffectParameters (funEffectParams efun) $ \e_params ->
  withParameters (funParams efun) $ \params ->
  withReturnType (funReturnType efun) $ \rb -> do
    dumpEnvironment
    return_binder <- lookupReturnType $ funReturnType efun
    et <- effectToCoreEffect $ funEffect efun
    body <- toCoreExp rb $ funBody efun
    return $ Core.CFun { Core.cfunInfo = funInfo efun 
                       , Core.cfunParams = e_params ++ params
                       , Core.cfunReturn = return_binder
                       , Core.cfunEffect = et
                       , Core.cfunBody = body
                       }

getCoreFunType :: EFun -> GenCore Core.RCFunType
getCoreFunType efun =
  withEffectParameters (funEffectParams efun) $ \e_params ->
  withParameters (funParams efun) $ \params -> do
    rt <- eReturnTypeToCoreType $ funReturnType efun
    et <- effectToCoreEffect $ funEffect efun
    
    let mk_fun_type [last_param] =
          let check_dependence probe_var =
                Core.cbindType rt `Core.cTypeMentions` probe_var ||
                et `Core.cTypeMentions` probe_var
              fun_param = type_param check_dependence last_param
          in Core.arrCT fun_param et (Core.retCT rt)

        mk_fun_type (param:params) =
          let range = mk_fun_type params
              check_dependence probe_var =
                Core.funCT range `Core.cTypeMentions` probe_var
              fun_param = type_param check_dependence param
          in Core.pureArrCT fun_param range 

    return $ mk_fun_type (e_params ++ params)
  where
    -- Convert a value parameter to a type parameter
    type_param check_dependence value_param =
      case Core.fromCBind value_param
      of Core.ValP pv
           | check_dependence pv -> Core.ValPT (Just pv) ::: ty
           | otherwise           -> Core.ValPT Nothing ::: ty
         Core.OwnP _             -> Core.OwnPT ::: ty
         Core.ReadP a _          -> Core.ReadPT a ::: ty
      where
        ty = Core.cbindType value_param

toCoreDef (EDef v f) = do 
  f' <- toCoreFun f
  return (Core.CDef v f')

assumeDef (EDef v f) m = do
  ftype <- getCoreFunType f
  withType v (OwnVB (Core.funCT ftype)) m

assumeDefs defs m = foldr assumeDef m defs

-- | Convert a definition group.  Put the definitions in scope over the body
-- expression.
convertDefGroup :: EDefGroup -> ([Core.CDef Rec] -> GenCore a) -> GenCore a
convertDefGroup group k = assumeDefs group $ k =<< mapM toCoreDef group

convertExport :: EExport -> GenCore (Core.CExport Rec)
convertExport (EExport inf spec f) = do
  f' <- toCoreFun f
  return $ Core.CExport inf spec f'

convertTopLevel :: [EDefGroup] -> [EExport]
                -> GenCore ([[Core.CDef Rec]], [Core.CExport Rec])
convertTopLevel groups exports = go groups
  where
    go (group:groups) = convertDefGroup group $ \group' -> do
      (groups', exports') <- go groups
      return (group' : groups', exports')
    
    go [] = do
      exports' <- mapM convertExport exports
      return ([], exports')

convertModule :: ModuleName -> [EDefGroup] -> [EExport]
              -> GenCore (Core.CModule Rec)
convertModule mod_name groups exports = do
  (core_groups, core_exports) <- convertTopLevel groups exports
  return $ Core.CModule mod_name core_groups core_exports

generateCore :: RegionVarMap -> ModuleName -> [EDefGroup] -> [EExport]
             -> IO (Core.CModule Rec)
generateCore rvmap mod_name groups exports =
  withTheVarIdentSupply $ \var_supply -> do
    env <- setupGenCoreEnv var_supply rvmap
    doGenCore env $ convertModule mod_name groups exports
 