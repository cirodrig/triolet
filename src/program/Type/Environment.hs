{-| Type environments.

Type environments map variable names to types, data types, and type functions.

The type environment changes depending on the stage of compilation.
Type descriptions are read in as a \"specification\" type environment.  The 
specifications do not directly describe intermediate code, but instead are
converted to two different forms that do describe intermediate code.  The 
\"pure\" type environment generated from the specification describes System F
code before representation inference.  The \"mem\" type environment describes
System F code after representation inference.
-}

{-# LANGUAGE FlexibleContexts, FlexibleInstances, Rank2Types #-}
{-# OPTIONS_GHC -no-auto #-}
module Type.Environment
       (BoxingMode(builtinTypeFunctionForEval),
        FullyBoxedMode, fullyBoxedMode, 
        UnboxedMode, unboxedMode,
        SpecMode,
        TypeEnvMonad(..),
        TypeEnvM,
        runTypeEnvM,
        assume,
        assumeWithProperties,
        assumeBinder,
        assumeBinders,
        EvalMonad(..),
        getBoxingMode,
        TypeEvalM(..),
        BoxedTypeEvalM,
        UnboxedTypeEvalM,
        ITypeEnvBase,
        freezeTypeEnv,
        thawTypeEnv,
        MTypeEnvBase,
        TypeEnv,
        BoxedTypeEnv,
        DataType(..),
        dataTypeFullKind,
        DataConType(..),
        dataConTyParams,
        dataConTyCon,
        dataConFieldTypes,
        dataConFieldKinds,
        dataConPatternRange,
        DataTypeDescr(..),
        DataConDescr(..),
        TypeFunction,
        BuiltinTypeFunction(..),
        typeFunction,
        typeFunctionArity,
        applyTypeFunction,
        lookupType,
        lookupTypeWithProperties,
        lookupDataType,
        lookupDataCon,
        lookupDataConWithType,
        lookupTypeFunction,
        getAllDataConstructors,
        getAllDataTypeConstructors,
        getAllKinds,
        getAllTypes,
        pprTypeEnv,
        mkEmptyTypeEnv,
        mkWiredInTypeEnv,
        --insertTypeWithProperties,
        insertGlobalType,
        insertGlobalTypeWithProperties,
        locallyModifyTypeEnv,
        locallyInsertType,
        insertDataType,
        insertTypeFunction,
        setSizeParameters,
       
        -- * New conversion routines
        isAdapterCon,
        specializeTypeEnv
       )
where

import Prelude hiding(mapM)

import Control.Applicative
import Control.Monad hiding(mapM)
import Control.Monad.Reader hiding(mapM)
import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import qualified Data.HashTable as HT
import qualified Data.IntMap as IntMap
import Data.Maybe
import Data.Traversable
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import Common.Supply
import Builtins.Builtins
import Type.Type

hashVar v = HT.hashInt $ fromIdent $ varID v

-------------------------------------------------------------------------------
-- Support for type-level computation

-- | The boxing mode to use for reduction.  Type functions are reduced
--   differently depending on the mode.
class BoxingMode m where
  -- | Get the implementation of a builtin type function to use during
  --   evaluation.
  --   Gets either 'builtinPureTypeFunction' or 'builtinMemTypeFunction'.
  --   The first argument is not used and may be 'undefined'.
  builtinTypeFunctionForEval :: m -> BuiltinTypeFunction -> TypeFunction

data FullyBoxedMode

-- | This is used as a dummy parameter
fullyBoxedMode :: FullyBoxedMode
fullyBoxedMode = error "fullyBoxedMode"

instance BoxingMode FullyBoxedMode where
  builtinTypeFunctionForEval _ = builtinPureTypeFunction

data UnboxedMode

-- | This is used as a dummy parameter
unboxedMode :: UnboxedMode
unboxedMode = error "unboxedMode"

instance BoxingMode UnboxedMode where
  builtinTypeFunctionForEval _ = builtinMemTypeFunction

-- | The specification type environment, with initializer types.
data SpecMode

instance BoxingMode SpecMode where
  -- This should never be called
  builtinTypeFunctionForEval _ = builtinSpecTypeFunction

-- | A monad that keeps track of the current type environment
class (MonadIO m, Applicative m, BoxingMode (EvalBoxingMode m)) =>
      TypeEnvMonad m where
  type EvalBoxingMode m

  -- | Get the current type environment
  getTypeEnv :: m (MTypeEnvBase (EvalBoxingMode m))

  -- | Run a type environment computation
  liftTypeEnvM :: TypeEnvM (EvalBoxingMode m) a -> m a

  {- -- | Query the current type environment
  askTypeEnv :: (TypeEnvBase (EvalBoxingMode m) -> a) -> m a
  askTypeEnv f = liftM f getTypeEnv

  -- | Add a variable to the type environment
  assumeWithProperties :: Var -> Type -> Bool -> m a -> m a
  -}

-- | Add a variable to the type environment
assume :: TypeEnvMonad m => Var -> Type -> m a -> m a
assume v t m = assumeWithProperties v t False m

-- | Add a variable to the type environment with extra flags
assumeWithProperties :: TypeEnvMonad m => Var -> Type -> Bool -> m a -> m a
assumeWithProperties v t b m = do
  env <- getTypeEnv
  locallyModifyTypeEnv env v (insertTypeWithProperties env v t b) m

assumeBinder :: TypeEnvMonad m => Binder -> m a -> m a
assumeBinder (v ::: t) m = assume v t m

assumeBinders :: TypeEnvMonad m => [Binder] -> m a -> m a
assumeBinders bs m = foldr assumeBinder m bs

instance TypeEnvMonad m => TypeEnvMonad (MaybeT m) where
  type EvalBoxingMode (MaybeT m) = EvalBoxingMode m
  getTypeEnv = lift getTypeEnv
  liftTypeEnvM m = lift (liftTypeEnvM m)
  --askTypeEnv f = lift (askTypeEnv f)
  --assumeWithProperties v t b (MaybeT m) = MaybeT (assumeWithProperties v t b m)

-- | A simple model of TypeEnvMonad
newtype TypeEnvM b a = TypeEnvM (ReaderT (MTypeEnvBase b) IO a)

runTypeEnvM e (TypeEnvM m) = runReaderT m e

instance Functor (TypeEnvM b) where fmap f (TypeEnvM r) = TypeEnvM (fmap f r)

instance Applicative (TypeEnvM b) where
  pure x = TypeEnvM (pure x)
  TypeEnvM f <*> TypeEnvM x = TypeEnvM (f <*> x)

instance Monad (TypeEnvM b) where
  return x = TypeEnvM (return x)
  TypeEnvM m >>= k = TypeEnvM (m >>= \x -> case k x of TypeEnvM m' -> m')

instance MonadIO (TypeEnvM b) where
  liftIO m = TypeEnvM $ liftIO m

instance BoxingMode b => TypeEnvMonad (TypeEnvM b) where
  type EvalBoxingMode (TypeEnvM b) = b
  getTypeEnv = TypeEnvM ask
  liftTypeEnvM m = m
  --assumeWithProperties v t b m =
  --  localType v (insertTypeWithProperties v t b) m

-- | A monad supporting type-level computation
class (MonadIO m, Supplies m (Ident Var), TypeEnvMonad m) => EvalMonad m where
  liftTypeEvalM :: TypeEvalM (EvalBoxingMode m) a -> m a

instance Supplies m (Ident Var) => Supplies (MaybeT m) (Ident Var) where
  fresh = lift fresh

instance EvalMonad m => EvalMonad (MaybeT m) where
  liftTypeEvalM = lift . liftTypeEvalM

-- | A simple monad supporting type-level computation
newtype TypeEvalM boxing_mode a =
  TypeEvalM {runTypeEvalM :: IdentSupply Var -> MTypeEnvBase boxing_mode -> IO a}

type BoxedTypeEvalM = TypeEvalM FullyBoxedMode
type UnboxedTypeEvalM = TypeEvalM UnboxedMode

instance Functor (TypeEvalM boxing_mode) where
  {-# INLINE fmap #-}
  fmap f m = TypeEvalM $ \supply env -> fmap f (runTypeEvalM m supply env)

instance Applicative (TypeEvalM boxing_mode) where
  {-# INLINE pure #-}
  {-# INLINE (<*>) #-}
  pure = return
  (<*>) = ap

instance Monad (TypeEvalM boxing_mode) where
  {-# INLINE return #-}
  {-# INLINE (>>=) #-}
  return x = TypeEvalM (\_ _ -> return x)
  m >>= k = TypeEvalM $ \supply env -> do
    x <- runTypeEvalM m supply env
    runTypeEvalM (k x) supply env

instance MonadIO (TypeEvalM boxing_mode) where
  {-# INLINE liftIO #-}
  liftIO m = TypeEvalM (\_ _ -> m)

instance Supplies (TypeEvalM boxing_mode) (Ident Var) where
  {-# INLINE fresh #-}
  fresh = TypeEvalM (\supply _ -> supplyValue supply)

instance BoxingMode boxing_mode => TypeEnvMonad (TypeEvalM boxing_mode) where
  type EvalBoxingMode (TypeEvalM boxing_mode) = boxing_mode
  {-# INLINE getTypeEnv #-}
  getTypeEnv = TypeEvalM (\_ tenv -> return tenv)

instance BoxingMode boxing_mode => EvalMonad (TypeEvalM boxing_mode) where
  liftTypeEvalM m = m

-- | This computation's return value is used as a dummy parameter
getBoxingMode :: forall m. EvalMonad m => m (EvalBoxingMode m)
getBoxingMode =
  return (internalError "getBoxingMode" :: forall. EvalBoxingMode m)

-------------------------------------------------------------------------------

-- | A type assigned to a 'Var'.
--
--   The type_function parameter is 'BuiltinTypeFunction' in the specification
--   type environment and 'TypeFunction' in other type environments.
data TypeAssignment =
    -- | Type of a variable
    VarTypeAssignment
    { varType :: !Type

      -- | 'True' if an application of the variable is cheap to re-evaluate.
      --   Always 'False' for non-function-typed variables and for
      --   type variables.
      --   The default is 'False'.
      --
      --   If a function is conlike, it is a hint that the function can be
      --   inlined even if it causes the function to be executed more often.
    , varIsConlike :: !Bool
    }
    -- | Type of a type constructor
  | TyConTypeAssignment !DataType

    -- | Type of a data constructor.
    --   The actual type signature is computed on demand.
  | DataConTypeAssignment !DataConType

    -- | Type and definition of a type function
  | TyFunTypeAssignment
    { varType :: !Type
    , tyFunType :: !BuiltinTypeFunction
    }

-- | Create a 'VarTypeAssignment' with default properties.
varTypeAssignment :: Type -> TypeAssignment
varTypeAssignment t = VarTypeAssignment t False

-- | Get the level of the variable described by a type assignment
typeAssignmentLevel :: TypeAssignment -> Level
typeAssignmentLevel (VarTypeAssignment ty _)  = pred $ getLevel ty 
typeAssignmentLevel (TyConTypeAssignment _)   = TypeLevel
typeAssignmentLevel (DataConTypeAssignment _) = ObjectLevel
typeAssignmentLevel (TyFunTypeAssignment _ _) = TypeLevel

data DataType =
  DataType
  { -- | This data type's type constructor
    dataTypeCon :: !Var

    -- | Type parameters.  Type parameters are passed as arguments when 
    --   constructing a value and when deconstructing it.
  , dataTypeParams :: [Binder]

    -- | Size parameter types along with their kinds.
    --   This list holds the type itself, not the type of its size
    --   (e.g., @int@ rather than @SizeAlignVal int@).
    --   A 'Nothing' value means the size parameter types have not been 
    --   computed yet.
  , dataTypeSizeParamTypes :: !(Maybe [KindedType])

    -- | The kind of a value whose type is a
    --   fully applied instance of this data type.
  , dataTypeKind :: !BaseKind
    
    -- | Abstractness of the data type.
    --   If a data type is abstract, then the compiler should not introduce
    --   data constructor expressions or case expressions for this type.
    --   It is still permissible to optimize such expressions if they are
    --   already present in the code.
  , dataTypeIsAbstract :: !Bool

    -- | Whether the data type is algebraic.
    --
    --   Most data type are algebraic.  However, a few (int, float, array)
    --   have a built-in, nonalgebraic definition.
  , dataTypeIsAlgebraic :: !Bool

    -- | Data constructors of this data type
  , dataTypeDataConstructors :: [Var]

  }

-- | Get the kind of a data type constructor
dataTypeFullKind :: DataType -> Kind
dataTypeFullKind dtype =
  let domain_kinds = map binderType $ dataTypeParams dtype 
      range_kind = fromBaseKind $ dataTypeKind dtype
  in funType domain_kinds range_kind

-- | Describes a data constructor.
--
--   The type of a constructed value is determined by its type parameters.
--   If the type parameters are @a1 ... aN@ and the type constructor is @T@,
--   then the type of the constructed value is @T a1 ... aN@.
data DataConType =
  DataConType
  { dataConCon :: !Var          -- ^ This data constructor
    -- | Existential types.  These are passed
    --   as arguments when constructing a value, and matched as paramters
    --   when deconstructing it.  They have no run-time representation.
    --   These must be dependent value patterns (@ValPT (Just _)@).
  , dataConExTypes :: [Binder]

    -- | Fields.  These are passed as arguments when constructing a value,
    -- and matched as parameters when deconstructing it.
    -- The field type are annotated with their kinds.
  , dataConFields :: [(Type, BaseKind)]
    
    -- | The data type constructor of this data constructor.
    --   This field must be lazy.
  , dataConType :: DataType
  }

dataConTyParams :: DataConType -> [Binder]
dataConTyParams t = dataTypeParams $ dataConType t

dataConTyCon :: DataConType -> Var
dataConTyCon t = dataTypeCon $ dataConType t

dataConFieldTypes :: DataConType -> [Type]
dataConFieldTypes t = map fst $ dataConFields t

dataConFieldKinds :: DataConType -> [BaseKind]
dataConFieldKinds t = map snd $ dataConFields t

-- | The type of a 'DataConType' value.
dataConPatternRange :: DataConType -> Type
dataConPatternRange dcon_type =
  let args = [VarT a | (a ::: _) <- dataConTyParams dcon_type]
  in varApp (dataConTyCon dcon_type) args

-- | A function on types.  Type functions are evaluated during type checking.
--   Type functions should /not/ operate on function types, because they are
--   currently not converted correctly by 'convertToPureTypeEnv' or
--   'convertToMemTypeEnv'.
data TypeFunction =
  TypeFunction
  { _tyfunArity     :: !Int

    -- | How to evaluate a type function.  The length of the argument list
    --   is exactly the size given by _tyfunArity.  The arguments are not
    --   reduced.  The returned type should be in weak head-normal form.
  , _tyfunReduction :: !(forall b. BoxingMode b => [Type] -> TypeEvalM b Type)
  }

-- | Create a type function
typeFunction :: Int
             -> (forall b. BoxingMode b => [Type] -> TypeEvalM b Type)
             -> TypeFunction
typeFunction = TypeFunction

typeFunctionArity :: TypeFunction -> Int
typeFunctionArity = _tyfunArity

applyTypeFunction :: EvalMonad m => TypeFunction -> [Type] -> m Type
{-# INLINE applyTypeFunction #-}
applyTypeFunction f ts = do
  x <- liftTypeEvalM $ _tyfunReduction f ts
  return $! x                   -- Ensure that result is evaluated

-- | A built-in type function has two implementations, depending on whether
--   it's being evaluated in the pure or mem variant of the type system
data BuiltinTypeFunction =
  BuiltinTypeFunction
  { builtinPureTypeFunction :: !TypeFunction
  , builtinSpecTypeFunction :: !TypeFunction
  , builtinMemTypeFunction :: !TypeFunction
  }

-- | An immutable type environment
newtype ITypeEnvBase boxing_mode =
  ITypeEnv [(Var, TypeAssignment)]

freezeTypeEnv :: TypeEnvMonad m => m (ITypeEnvBase (EvalBoxingMode m))
freezeTypeEnv = do
  MTypeEnv e <- getTypeEnv
  assocs <- liftIO $ HT.toList e
  return $ ITypeEnv assocs

thawTypeEnv :: BoxingMode b => ITypeEnvBase b -> IO (MTypeEnvBase b)
thawTypeEnv (ITypeEnv env) = MTypeEnv `liftM` HT.fromList hashVar env

-- | A mutable type environment mapping variables to types
newtype MTypeEnvBase boxing_mode =
  MTypeEnv (HT.HashTable Var TypeAssignment)

type TypeEnv = MTypeEnvBase UnboxedMode
type BoxedTypeEnv = MTypeEnvBase FullyBoxedMode

mkEmptyTypeEnv :: IO (MTypeEnvBase b)
mkEmptyTypeEnv = do ht <- HT.new (==) hashVar
                    return $ MTypeEnv ht

-- | A Type environment containing the variables defined in "Type.Type"
mkWiredInTypeEnv :: IO (MTypeEnvBase UnboxedMode)
mkWiredInTypeEnv = do
  env@(MTypeEnv ht) <- mkEmptyTypeEnv
  mapM (uncurry (HT.insert ht)) entries
  return env
  where
    entries = [(intindexV, varTypeAssignment kindT),
               (valV, varTypeAssignment kindT),
               (boxV, varTypeAssignment kindT),
               (bareV, varTypeAssignment kindT),
               (outV, varTypeAssignment kindT),
               -- (initV, varTypeAssignment kindT),
               -- (initConV, varTypeAssignment (bareT `FunT` initT)),
               (outPtrV, varTypeAssignment (bareT `FunT` outT)),
               (storeV, TyConTypeAssignment store_data_type),
               (posInftyV, varTypeAssignment intindexT),
               (negInftyV, varTypeAssignment intindexT),
               (arrV, TyConTypeAssignment arr_data_type),
               (intV, TyConTypeAssignment int_data_type),
               (uintV, TyConTypeAssignment uint_data_type),
               (floatV, TyConTypeAssignment float_data_type)]

    store_data_type =
      DataType { dataTypeCon = storeV
               , dataTypeParams = []
               , dataTypeSizeParamTypes = Just []
               , dataTypeKind = ValK
               , dataTypeIsAbstract = True
               , dataTypeIsAlgebraic = False
               , dataTypeDataConstructors = []}

    arr_data_type =
      DataType { dataTypeCon = arrV
               , dataTypeParams = [(arrTypeParameter1 ::: intindexT),
                                   (arrTypeParameter2 ::: bareT)]
               , dataTypeSizeParamTypes = Just [KindedType IntIndexK
                                                (VarT arrTypeParameter1),
                                                KindedType BareK
                                                (VarT arrTypeParameter2)]
               , dataTypeKind = BareK
               , dataTypeIsAbstract = True
               , dataTypeIsAlgebraic = False
               , dataTypeDataConstructors = []}

    int_data_type =
      DataType { dataTypeCon = intV
               , dataTypeParams = []
               , dataTypeSizeParamTypes = Just []
               , dataTypeKind = ValK
               , dataTypeIsAbstract = True
               , dataTypeIsAlgebraic = False
               , dataTypeDataConstructors = []}

    uint_data_type =
      DataType { dataTypeCon = uintV
               , dataTypeParams = []
               , dataTypeSizeParamTypes = Just []
               , dataTypeKind = ValK
               , dataTypeIsAbstract = True
               , dataTypeIsAlgebraic = False
               , dataTypeDataConstructors = []}

    float_data_type =
      DataType { dataTypeCon = floatV
               , dataTypeParams = []
               , dataTypeSizeParamTypes = Just []
               , dataTypeKind = ValK
               , dataTypeIsAbstract = True
               , dataTypeIsAlgebraic = False
               , dataTypeDataConstructors = []}

locallyInsertType :: MonadIO m =>
                     MTypeEnvBase b -- ^ Type environment
                  -> Var     -- ^ Variable that is inserted
                  -> Type    -- ^ Type to insert
                  -> m a     -- ^ Action to run
                  -> m a     -- ^ Action that does not modify environment
{-# INLINE locallyInsertType #-}
locallyInsertType tenv v t m =
  locallyModifyTypeEnv tenv v (insertTypeWithProperties tenv v t False) m

-- | Insert a type temporarily in the environment
locallyModifyTypeEnv :: MonadIO m =>
                        MTypeEnvBase b -- ^ Type environment
                     -> Var     -- ^ Variable that is inserted
                     -> IO ()   -- ^ Insert into type environment
                     -> m a     -- ^ Action to run
                     -> m a     -- ^ Action that does not modify environment
{-# INLINE locallyModifyTypeEnv #-}
locallyModifyTypeEnv (MTypeEnv env) v insert m = do
  old <- liftIO $ HT.lookup env v -- Sanity check: type not in environment
  liftIO insert                   -- Insert type
  x <- m                          -- Run computation
  liftIO $ HT.delete env v        -- Delete type
  liftIO $ case old
           of Just x -> HT.insert env v x
              Nothing -> return ()
  return x

-- | Insert a variable type assignment for a global variable.
--   For local variables, use 'assume' instead.
--   The variable must not be in the environment prior to insertion.
insertGlobalType :: MTypeEnvBase b -> Var -> Type -> IO ()
insertGlobalType e v t = insertGlobalTypeWithProperties e v t False

-- | Insert a variable type assignment for a global variable.
--   The variable must not be in the environment prior to insertion.
insertGlobalTypeWithProperties :: MTypeEnvBase b
                               -> Var
                               -> Type -- ^ Type of the variable
                               -> Bool -- ^ Whether the variable is conlike
                               -> IO ()
insertGlobalTypeWithProperties = insertTypeWithProperties

-- | Insert a variable type assignment.
--   The variable must not be in the environment prior to insertion.
insertTypeWithProperties :: MTypeEnvBase b
                         -> Var
                         -> Type -- ^ Type of the variable
                         -> Bool -- ^ Whether the variable is conlike
                         -> IO ()
insertTypeWithProperties (MTypeEnv ht) v t conlike =
  let type_ass = VarTypeAssignment t conlike
  in HT.insert ht v type_ass

-- | A description of a data type that will be added to a type environment.
data DataTypeDescr =
  DataTypeDescr
    Var                         -- Data type name
    [Binder]                    -- Data type's parameters
    BaseKind                    -- Result kind
    [DataConDescr]              -- Constructors
    !Bool                       -- Is abstract
    !Bool                       -- Is algebraic

data DataConDescr =
  DataConDescr 
    Var                         -- Constructor
    [Binder]                    -- Existential types
    [(Type, BaseKind)]          -- Field types and their kinds

insertDataType :: MTypeEnvBase b -> DataTypeDescr -> IO ()
insertDataType (MTypeEnv ht) (DataTypeDescr ty_con u_args range ctors is_abstract is_algebraic) = do
  uncurry (HT.insert ht) ty_con_assignment
  mapM_ (uncurry (HT.insert ht)) data_con_assignments
  where
    insert (v, a) env = IntMap.insert (fromIdent $ varID v) a env
    
    data_cons = [dtor | DataConDescr dtor _ _ <- ctors]
    data_type = DataType ty_con u_args Nothing range
                is_abstract is_algebraic data_cons
    ty_con_assignment = (ty_con, TyConTypeAssignment data_type)

    data_con (DataConDescr v bs fs) = DataConType v bs fs data_type
    data_con_assignments =
      [ (v, DataConTypeAssignment (data_con dtor))
      | dtor@(DataConDescr v _ _) <- ctors]
    
insertTypeFunction :: MTypeEnvBase b ->
                      Var -> Type -> BuiltinTypeFunction -> IO ()
insertTypeFunction (MTypeEnv ht) v ty f = do 
  HT.insert ht v (TyFunTypeAssignment ty f)

-- | Set a data type's size parameters
setSizeParameters :: TypeEnvMonad m => Var -> [KindedType] -> m ()
setSizeParameters v size_params = do 
  MTypeEnv ht <- getTypeEnv
  liftIO $ do
    Just (TyConTypeAssignment dtype) <- HT.lookup ht v
    let dtype' = dtype {dataTypeSizeParamTypes = Just size_params}
    HT.insert ht v (TyConTypeAssignment dtype')

lookupAndExtract :: TypeEnvMonad m =>
                    (TypeAssignment -> Maybe b) -> Var -> m (Maybe b)
lookupAndExtract f v = do
  MTypeEnv ht <- getTypeEnv
  liftIO $ do m_ass <- HT.lookup ht v
              return $! f =<< m_ass

lookupDataCon :: TypeEnvMonad m => Var -> m (Maybe DataConType)
{-# INLINE lookupDataCon #-}
lookupDataCon v = lookupAndExtract extract v
  where
    extract (DataConTypeAssignment dtor) = Just dtor
    extract _ = Nothing

lookupDataType :: TypeEnvMonad m => Var -> m (Maybe DataType)
{-# INLINE lookupDataType #-}
lookupDataType v = lookupAndExtract extract v
  where
    extract (TyConTypeAssignment tc) = Just tc
    extract _ = Nothing

lookupDataConWithType :: TypeEnvMonad m =>
                         Var -> m (Maybe (DataType, DataConType))
{-# INLINE lookupDataConWithType #-}
lookupDataConWithType v = do
  m_dcon <- lookupDataCon v
  case m_dcon of
    Nothing -> return Nothing
    Just dcon -> do
      m_dtype <- lookupDataType (dataConTyCon dcon)
      return $! case m_dtype of Just dtype -> Just (dtype, dcon)
                                Nothing    -> Nothing

lookupTypeFunction :: TypeEnvMonad m => Var -> m (Maybe BuiltinTypeFunction)
{-# INLINE lookupTypeFunction #-}
lookupTypeFunction v = lookupAndExtract extract v
  where
    extract (TyFunTypeAssignment _ tf) = Just tf
    extract _ = Nothing

-- | Look up the type of a variable
lookupType :: TypeEnvMonad m => Var -> m (Maybe Type)
{-# INLINE lookupType #-}
lookupType v = lookupAndExtract extract v
  where
    extract (VarTypeAssignment t _)   = Just t
    extract (TyConTypeAssignment tc)  = Just $ dataTypeFullKind tc
    extract (TyFunTypeAssignment t _) = Just t
    extract (DataConTypeAssignment _) =
      internalError "lookupType: Unexpected data constructor"

{-
-- | Look up the mem type of a data constructor as it is used in a
--   data constructor expression.  Normally, 'instantiateDataConType'
--   would be used instead.
--
--   Some builtin types are used to construct the type.
lookupDataConType :: Var -> TypeEnvBase type_function -> Maybe Type
{-# INLINE lookupDataConType #-}
lookupDataConType v tenv =
  case lookupDataConWithType v tenv
  of Just (dtype, dcon_type) -> Just $ makeDataConType dtype dcon_type
     Nothing                 -> Nothing

-- used by lookupDataConType
makeDataConType dtype dcon_type =
  let arg_types = zipWith init_type
                  (dataConPatternArgs dcon_type)
                  (dataConPatternArgKinds dcon_type)
      ret_type = init_type
                 (varApp (dataTypeCon dtype) $
                  map (VarT . binderVar) (dataConTyParams dcon_type))
                 (dataTypeKind dtype)

  -- Create the type
  -- forall as. forall bs. ps -> T as
  in forallType (dataConTyParams dcon_type) $
     forallType (dataConExTypes dcon_type) $
     funType arg_types ret_type
  where
    init_type t ValK  = t
    init_type t BoxK  = t
    init_type t BareK = initializerType t
-}

-- | Look up the type and other properties of an ordinary variable
lookupTypeWithProperties :: TypeEnvMonad m =>
                            Var -> m (Maybe (Type, Bool))
{-# INLINE lookupTypeWithProperties #-}
lookupTypeWithProperties v = lookupAndExtract extract v 
  where
    extract (VarTypeAssignment ty conlike) = Just (ty, conlike) 
    extract _ = Nothing

-- | Get all data constructors in the type environment
getAllDataConstructors :: ITypeEnvBase b -> IntMap.IntMap DataConType
getAllDataConstructors (ITypeEnv assocs) =
  IntMap.fromList $ mapMaybe get_data_con assocs
  where
    get_data_con (v, DataConTypeAssignment dcon) = Just (fromIdent $ varID v, dcon)
    get_data_con _ = Nothing

-- | Get all algebraic data type constructors in the type environment
getAllDataTypeConstructors :: ITypeEnvBase b -> IntMap.IntMap DataType
getAllDataTypeConstructors (ITypeEnv assocs) =
  IntMap.fromList $ mapMaybe get_data_con assocs
  where
    get_data_con (v, TyConTypeAssignment dtype) = Just (fromIdent $ varID v, dtype)
    get_data_con _ = Nothing

-- | Get kind of all types in the type environment
getAllKinds :: ITypeEnvBase b -> IntMap.IntMap Kind
getAllKinds (ITypeEnv assocs) =
  IntMap.fromList $ mapMaybe get_type assocs
  where
    get_type (v, VarTypeAssignment ty _)  
      | getLevel ty >= KindLevel       = Just (fromIdent $ varID v, ty)
      | otherwise                      = Nothing
    get_type (v, TyConTypeAssignment dtype) = Just (fromIdent $ varID v, dataTypeFullKind dtype)
    get_type (_, DataConTypeAssignment _) = Nothing
    get_type (v, TyFunTypeAssignment k _) = Just (fromIdent $ varID v, k)

-- | Get kinds of all types and types of all variables in the type
--   environment.  Data constructors are not included in the result.
getAllTypes :: ITypeEnvBase b -> IntMap.IntMap Type
getAllTypes (ITypeEnv assocs) =
  IntMap.fromList $ mapMaybe get_type assocs
  where
    get_type (v, VarTypeAssignment ty _)  = Just (fromIdent $ varID v, ty)
    get_type (v, TyConTypeAssignment dtype) = Just (fromIdent $ varID v, dataTypeFullKind dtype)
    get_type (_, DataConTypeAssignment _) = Nothing
    get_type (v, TyFunTypeAssignment k _) = Just (fromIdent $ varID v, k)

-- | Create a docstring showing all types in the type environment
pprTypeEnv :: ITypeEnvBase b -> Doc
pprTypeEnv (ITypeEnv assocs) =
  vcat [ hang (pprVar v <+> text "|->") 8 (pprTypeAssignment t)
       | (v, t) <- assocs]

pprTypeAssignment :: TypeAssignment -> Doc
pprTypeAssignment (VarTypeAssignment ty _) = pprType ty
pprTypeAssignment (TyConTypeAssignment dtype) = pprType $ dataTypeFullKind dtype
pprTypeAssignment (DataConTypeAssignment c) = pprDataConType c
pprTypeAssignment (TyFunTypeAssignment k _) = pprType k

pprDataConType c =
  let constructed_type =
        varApp (dataConTyCon c) [VarT v | v ::: _ <- dataConTyParams c]
      fo_type = funType (dataConFieldTypes c) constructed_type
  in pprType $ forallType (dataConTyParams c) $
               forallType (dataConExTypes c) fo_type

-------------------------------------------------------------------------------

-- | True if the variable is an adapter type constructor or function.
--
--   Adapter types are inserted to convert data between representations
--   without changing the values.
isAdapterCon :: Var -> Bool
isAdapterCon v = v `elem` adapters
  where
    adapters = [initConV,       -- Init
                coreBuiltin The_Stored,
                coreBuiltin The_Ref,
                coreBuiltin The_Boxed,
                coreBuiltin The_AsBox,
                coreBuiltin The_AsBare]

initializerType t = typeApp outPtrT [t] `FunT` storeT

-------------------------------------------------------------------------------

{-forgetTypeFunctions :: TypeEnvBase b -> TypeEnvBase b
forgetTypeFunctions (TypeEnv m) = TypeEnv $ IntMap.map forget_type_function m
  where
    forget_type_function (TyFunTypeAssignment k _) = VarTypeAssignment k False
    forget_type_function ass = ass
-}

-- | Transform the contents of a type environment.
--   Return a new type environment.
specializeTypeEnv :: forall b1 b2. BoxingMode b2 =>
                     (BaseKind -> Maybe BaseKind)
                     -- ^ Transformation on base kinds
                  -> (Kind -> Maybe Kind)
                     -- ^ Transformation on kinds
                  -> (Type -> Maybe Type)
                     -- ^ Transformation on types in data constructors
                  -> (Type -> Maybe Type)
                     -- ^ Transformation on types in type bindings
                  -> MTypeEnvBase b1 -> IO (MTypeEnvBase b2)
specializeTypeEnv basekind_f kind_f type_f tybind_f (MTypeEnv m) = do
  assocs <- HT.toList m
  -- Create type-level entities
  let type_entries = mapMaybe type_assoc assocs
  kind_env <- MTypeEnv `liftM` HT.fromList hashVar type_entries
  
  -- Create value-level entities
  value_entries <- mapM (value_assoc kind_env) assocs
  value_m <- HT.fromList hashVar (type_entries ++ catMaybes value_entries)
  return $ MTypeEnv value_m
  where
    type_assoc (v, t) = (,) v <$> kind_assignment t

    -- Process everything at type level and above
    kind_assignment (VarTypeAssignment t conlike) =
      let t' = case getLevel t
               of SortLevel -> Just t
                  KindLevel -> kind_f t
                  TypeLevel -> Nothing
                  ObjectLevel -> internalError "specializeTypeEnv"
      in VarTypeAssignment <$> t' <*> pure conlike

    kind_assignment (TyConTypeAssignment dtype) =
      TyConTypeAssignment <$> data_type dtype

    kind_assignment (TyFunTypeAssignment t f) =
      TyFunTypeAssignment <$> kind_f t <*> pure f

    kind_assignment (DataConTypeAssignment _) = Nothing

    data_type (DataType con params size_params k
               is_abstract is_algebraic ctors) = do
      params' <- specializeBinders kind_f params
      size_params' <- mapM (mapM size_parameter) size_params
      k' <- basekind_f k
      return $ DataType con params' size_params' k'
        is_abstract is_algebraic ctors

    size_parameter (KindedType k t) = KindedType <$> basekind_f k <*> type_f t

    -- Process everything at value level.
    -- The kind environment has already been translated, and it is used
    -- for looking up data types
    value_assoc :: forall. MTypeEnvBase b2 -> (Var, TypeAssignment)
                -> IO (Maybe (Var, TypeAssignment))
    value_assoc tenv (v, t) = do 
      t' <- type_assignment tenv t
      return $! case t' of { Just x -> Just (v, x); Nothing -> Nothing }

    type_assignment _ (VarTypeAssignment t conlike) =
      let t' = case getLevel t
               of SortLevel -> Nothing
                  KindLevel -> Nothing
                  TypeLevel -> tybind_f t
                  ObjectLevel -> internalError "specializeTypeEnv"
      in return $ VarTypeAssignment <$> t' <*> pure conlike

    type_assignment tenv (DataConTypeAssignment dcon) = do
      m_dcon <- data_con tenv dcon
      return $ DataConTypeAssignment <$> m_dcon
      
    type_assignment _ (TyConTypeAssignment _) = return Nothing
    type_assignment _ (TyFunTypeAssignment _ _) = return Nothing

    data_con kenv (DataConType con ex_types fields data_type) = do
      Just new_data_type <-
        runTypeEnvM kenv $ lookupDataType $ dataTypeCon data_type
      return $ DataConType con <$>
               (specializeBinders kind_f ex_types) <*>
               (mapM field_type fields) <*>
               pure new_data_type 
      where
        field_type (t, k) = (,) <$> type_f t <*> basekind_f k

specializeBinders f bs = mapM (specializeBinder f) bs
specializeBinder f (v ::: k) = do {k' <- f k; return (v ::: k')}

