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
       (TypeEnvMonad(..),
        assume,
        assumeBinder,
        assumeBinders,
        EvalMonad(..),
        TypeEvalM(..),
        TypeEnvBase,
        TypeEnv,
        SpecTypeEnv,
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
        emptyTypeEnv,
        wiredInTypeEnv,
        insertType,
        insertTypeWithProperties,
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
import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import qualified Data.IntMap as IntMap
import Data.Traversable
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import Common.Supply
import Builtins.Builtins
import Type.Type

-------------------------------------------------------------------------------
-- Support for type-level computation

type MonadTypeEnv m = TypeEnvBase (TypeFunctionInfo m)

-- | A monad that keeps track of the current type environment
class Monad m => TypeEnvMonad m where
  type TypeFunctionInfo m

  -- | Get the current type environment
  getTypeEnv :: m (MonadTypeEnv m)
  getTypeEnv = askTypeEnv id
  
  -- | Query the current type environment
  askTypeEnv :: (MonadTypeEnv m -> a) -> m a
  askTypeEnv f = liftM f getTypeEnv

  -- | Add a variable to the type environment
  assumeWithProperties :: Var -> Type -> Bool -> m a -> m a

-- | Add a variable to the type environment
assume :: TypeEnvMonad m => Var -> Type -> m a -> m a
assume v t m = assumeWithProperties v t False m

assumeBinder :: TypeEnvMonad m => Binder -> m a -> m a
assumeBinder (v ::: t) m = assume v t m

assumeBinders :: TypeEnvMonad m => [Binder] -> m a -> m a
assumeBinders bs m = foldr assumeBinder m bs

instance TypeEnvMonad m => TypeEnvMonad (MaybeT m) where
  type TypeFunctionInfo (MaybeT m) = TypeFunctionInfo m
  getTypeEnv = lift getTypeEnv
  askTypeEnv f = lift (askTypeEnv f)
  assumeWithProperties v t b (MaybeT m) = MaybeT (assumeWithProperties v t b m)

-- | A monad supporting type-level computation
class (MonadIO m, Supplies m (Ident Var), TypeEnvMonad m,
       TypeFunctionInfo m ~ TypeFunction) => EvalMonad m where
  liftTypeEvalM :: TypeEvalM a -> m a

instance Supplies m (Ident Var) => Supplies (MaybeT m) (Ident Var) where
  fresh = lift fresh

instance EvalMonad m => EvalMonad (MaybeT m) where
  liftTypeEvalM = lift . liftTypeEvalM

-- | A simple monad supporting type-level computation
newtype TypeEvalM a =
  TypeEvalM {runTypeEvalM :: IdentSupply Var -> TypeEnv -> IO a}

instance Functor TypeEvalM where
  {-# INLINE fmap #-}
  fmap f m = TypeEvalM $ \supply env -> fmap f (runTypeEvalM m supply env)

instance Applicative TypeEvalM where
  {-# INLINE pure #-}
  {-# INLINE (<*>) #-}
  pure = return
  (<*>) = ap

instance Monad TypeEvalM where
  {-# INLINE return #-}
  {-# INLINE (>>=) #-}
  return x = TypeEvalM (\_ _ -> return x)
  m >>= k = TypeEvalM $ \supply env -> do
    x <- runTypeEvalM m supply env
    runTypeEvalM (k x) supply env

instance MonadIO TypeEvalM where
  {-# INLINE liftIO #-}
  liftIO m = TypeEvalM (\_ _ -> m)

instance Supplies TypeEvalM (Ident Var) where
  {-# INLINE fresh #-}
  fresh = TypeEvalM (\supply _ -> supplyValue supply)

instance TypeEnvMonad TypeEvalM where
  type TypeFunctionInfo TypeEvalM = TypeFunction

  {-# INLINE getTypeEnv #-}
  getTypeEnv = TypeEvalM (\_ tenv -> return tenv)
  
  assumeWithProperties v t b m =
    TypeEvalM $ \supply tenv ->
    runTypeEvalM m supply (insertTypeWithProperties v t b tenv)

instance EvalMonad TypeEvalM where
  liftTypeEvalM m = m

-------------------------------------------------------------------------------

-- | A type assigned to a 'Var'.
--
--   The type_function parameter is 'BuiltinTypeFunction' in the specification
--   type environment and 'TypeFunction' in other type environments.
data TypeAssignment type_function =
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
    , tyFunType :: !type_function
    }

-- | Create a 'VarTypeAssignment' with default properties.
varTypeAssignment :: Type -> TypeAssignment a
varTypeAssignment t = VarTypeAssignment t False

-- | Get the level of the variable described by a type assignment
typeAssignmentLevel :: TypeAssignment a -> Level
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
  , _tyfunReduction :: !([Type] -> TypeEvalM Type)
  }

-- | Create a type function
typeFunction :: Int -> ([Type] -> TypeEvalM Type) -> TypeFunction
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
  , builtinMemTypeFunction :: !TypeFunction
  }


-- | A type environment maps variables to types
newtype TypeEnvBase type_function =
  TypeEnv (IntMap.IntMap (TypeAssignment type_function))

type TypeEnv = TypeEnvBase TypeFunction
type SpecTypeEnv = TypeEnvBase BuiltinTypeFunction

type PureTypeAssignment = TypeAssignment TypeFunction
type MemTypeAssignment = TypeAssignment TypeFunction
type SpecTypeAssignment = TypeAssignment BuiltinTypeFunction

emptyTypeEnv :: TypeEnvBase type_function
emptyTypeEnv = TypeEnv IntMap.empty

-- | A Type environment containing the variables defined in "Type.Type"
wiredInTypeEnv :: TypeEnvBase type_function
wiredInTypeEnv =
  TypeEnv $ IntMap.fromList [(fromIdent $ varID v, t) | (v, t) <- entries]
  where
    entries = [(intindexV, varTypeAssignment kindT),
               (valV, varTypeAssignment kindT),
               (boxV, varTypeAssignment kindT),
               (bareV, varTypeAssignment kindT),
               (outV, varTypeAssignment kindT),
               (initV, varTypeAssignment kindT),
               (initConV, varTypeAssignment (bareT `FunT` initT)),
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

-- | Insert a variable type assignment
insertType :: Var -> Type
           -> TypeEnvBase type_function -> TypeEnvBase type_function
insertType v t (TypeEnv env) =
  TypeEnv (IntMap.insert (fromIdent $ varID v) (varTypeAssignment t) env)

-- | Insert a variable type assignment 
insertTypeWithProperties :: Var
                         -> Type -- ^ Type of the variable
                         -> Bool -- ^ Whether the variable is conlike
                         -> TypeEnvBase type_function
                         -> TypeEnvBase type_function
insertTypeWithProperties v t conlike (TypeEnv env) =
  let type_ass = VarTypeAssignment t conlike
  in TypeEnv (IntMap.insert (fromIdent $ varID v) type_ass env)

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

insertDataType :: DataTypeDescr
               -> TypeEnvBase type_function -> TypeEnvBase type_function
insertDataType (DataTypeDescr ty_con u_args range ctors is_abstract is_algebraic)
               (TypeEnv env) =
  TypeEnv $ foldr insert env (ty_con_assignment : data_con_assignments)
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
    
insertTypeFunction :: Var -> Type -> type_function
                   -> TypeEnvBase type_function -> TypeEnvBase type_function
insertTypeFunction v ty f (TypeEnv env) =
  TypeEnv $ IntMap.insert (fromIdent $ varID v) (TyFunTypeAssignment ty f) env

-- | Set a data type's size parameters
setSizeParameters :: Var -> [KindedType]
                  -> TypeEnvBase type_function -> TypeEnvBase type_function
setSizeParameters v size_params (TypeEnv env) =
  case IntMap.lookup (fromIdent $ varID v) env
  of Just (TyConTypeAssignment dtype) ->
       let dtype' = dtype {dataTypeSizeParamTypes = Just size_params}
       in TypeEnv $ IntMap.insert (fromIdent $ varID v) (TyConTypeAssignment dtype') env
     _ -> internalError "setSizeParameters: Not a data type constructor"

lookupDataCon :: Var -> TypeEnvBase type_function -> Maybe DataConType
{-# INLINE lookupDataCon #-}
lookupDataCon v (TypeEnv env) =
  case IntMap.lookup (fromIdent $ varID v) env
  of Just (DataConTypeAssignment dtor) -> Just dtor
     _ -> Nothing

lookupDataType :: Var -> TypeEnvBase type_function -> Maybe DataType
{-# INLINE lookupDataType #-}
lookupDataType v (TypeEnv env) =
  case IntMap.lookup (fromIdent $ varID v) env
  of Just (TyConTypeAssignment tc) -> Just tc
     _ -> Nothing

lookupDataConWithType :: Var -> TypeEnvBase type_function
                      -> Maybe (DataType, DataConType)
{-# INLINE lookupDataConWithType #-}
lookupDataConWithType v env = do
  dcon <- lookupDataCon v env
  dtype <- lookupDataType (dataConTyCon dcon) env
  return (dtype, dcon)

lookupTypeFunction :: Var -> TypeEnv -> Maybe TypeFunction
{-# INLINE lookupTypeFunction #-}
lookupTypeFunction v (TypeEnv env) =
  case IntMap.lookup (fromIdent $ varID v) env
  of Just (TyFunTypeAssignment _ tf) -> Just tf
     _ -> Nothing

-- | Look up the type of a variable
lookupType :: Var -> TypeEnvBase type_function -> Maybe Type
{-# INLINE lookupType #-}
lookupType v (TypeEnv env) =
  case IntMap.lookup (fromIdent $ varID v) env
  of Nothing -> Nothing
     Just (VarTypeAssignment t _)   -> Just t
     Just (TyConTypeAssignment tc)  -> Just $ dataTypeFullKind tc
     Just (TyFunTypeAssignment t _) -> Just t
     Just (DataConTypeAssignment _) ->
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
lookupTypeWithProperties :: Var -> TypeEnvBase type_function
                         -> Maybe (Type, Bool)
{-# INLINE lookupTypeWithProperties #-}
lookupTypeWithProperties v (TypeEnv env) = do
  VarTypeAssignment ty conlike <- IntMap.lookup (fromIdent $ varID v) env
  return (ty, conlike)

-- | Get all data constructors in the type environment
getAllDataConstructors :: TypeEnv -> IntMap.IntMap DataConType
getAllDataConstructors (TypeEnv env) = IntMap.mapMaybe get_data_con env 
  where
    get_data_con (DataConTypeAssignment dcon) = Just dcon 
    get_data_con _ = Nothing

-- | Get all algebraic data type constructors in the type environment
getAllDataTypeConstructors :: TypeEnv -> IntMap.IntMap DataType
getAllDataTypeConstructors (TypeEnv env) = IntMap.mapMaybe get_data_con env 
  where
    get_data_con (TyConTypeAssignment dtype) = Just dtype
    get_data_con _ = Nothing

-- | Get kind of all types in the type environment
getAllKinds :: TypeEnvBase type_function -> IntMap.IntMap Kind
getAllKinds (TypeEnv env) = IntMap.mapMaybe get_type env
  where
    get_type (VarTypeAssignment ty _)  
      | getLevel ty >= KindLevel       = Just ty
      | otherwise                      = Nothing
    get_type (TyConTypeAssignment dtype) = Just $ dataTypeFullKind dtype
    get_type (DataConTypeAssignment _) = Nothing
    get_type (TyFunTypeAssignment k _) = Just k

-- | Get kinds of all types and types of all variables in the type
--   environment.  Data constructors are not included in the result.
getAllTypes :: TypeEnvBase type_function -> IntMap.IntMap Type
getAllTypes (TypeEnv env) = IntMap.mapMaybe get_type env
  where
    get_type (VarTypeAssignment ty _)  = Just ty
    get_type (TyConTypeAssignment dtype) = Just $ dataTypeFullKind dtype
    get_type (DataConTypeAssignment _) = Nothing
    get_type (TyFunTypeAssignment k _) = Just k

-- | Create a docstring showing all types in the type environment
pprTypeEnv :: TypeEnvBase type_function -> Doc
pprTypeEnv (TypeEnv tenv) =
  vcat [ hang (text (show n) <+> text "|->") 8 (pprTypeAssignment t)
       | (n, t) <- IntMap.toList tenv]

pprTypeAssignment :: TypeAssignment type_function -> Doc
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

-- | Specialize a specification type environment for a particular use case.
specializeTypeEnv :: (BuiltinTypeFunction -> a)
                     -- ^ Choice of type function implementation
                  -> (BaseKind -> Maybe BaseKind)
                     -- ^ Transformation on base kinds
                  -> (Kind -> Maybe Kind)
                     -- ^ Transformation on kinds
                  -> (Type -> Maybe Type)
                     -- ^ Transformation on types
                  -> SpecTypeEnv -> TypeEnvBase a
specializeTypeEnv tyfun_f basekind_f kind_f type_f (TypeEnv m) = new_type_env
  where
    -- Data type constructors are looked up in the new type environment
    new_type_env = TypeEnv (IntMap.mapMaybe type_assignment m)

    type_assignment (VarTypeAssignment t conlike) =
      let t' = case getLevel t
               of SortLevel -> Just t
                  KindLevel -> kind_f t
                  TypeLevel -> type_f t
                  ObjectLevel -> internalError "specializeTypeEnv"
      in VarTypeAssignment <$> t' <*> pure conlike

    type_assignment (TyConTypeAssignment dtype) =
      TyConTypeAssignment <$> data_type dtype

    type_assignment (DataConTypeAssignment dcon) =
      DataConTypeAssignment <$> data_con dcon

    type_assignment (TyFunTypeAssignment t f) =
      TyFunTypeAssignment <$> kind_f t <*> pure (tyfun_f f)

    data_type (DataType con params size_params k
               is_abstract is_algebraic ctors) = do
      params' <- specializeBinders kind_f params
      size_params' <- mapM (mapM size_parameter) size_params
      k' <- basekind_f k
      return $ DataType con params' size_params' k'
        is_abstract is_algebraic ctors

    size_parameter (KindedType k t) = KindedType <$> basekind_f k <*> type_f t

    data_con (DataConType con ex_types fields data_type) =
      DataConType con <$>
      (specializeBinders kind_f ex_types) <*>
      (mapM field_type fields) <*>
      pure new_data_type 
      where
        new_data_type =
          case lookupDataType (dataTypeCon data_type) new_type_env
          of Just t -> t

        field_type (t, k) = (,) <$> type_f t <*> basekind_f k

specializeBinders f bs = mapM (specializeBinder f) bs
specializeBinder f (v ::: k) = do {k' <- f k; return (v ::: k')}

