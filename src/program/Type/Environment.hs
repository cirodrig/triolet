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
        DataConType(..),
        dataConPatternRange,
        DataTypeDescr(..),
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
        getAllTypes,
        pprTypeEnv,
        emptyTypeEnv,
        wiredInTypeEnv,
        insertType,
        insertTypeWithProperties,
        insertDataType,
        insertTypeFunction,
       
        -- * New conversion routines
        isAdapterCon,
        specToPureTypeEnv,
        specToMemTypeEnv,
        specToMemType,
        specToTypeEnv
       )
where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import qualified Data.IntMap as IntMap
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import Common.Supply
import Builtins.Builtins
import Type.Type

-------------------------------------------------------------------------------
-- Support for type-level computation

-- | A monad that keeps track of the current type environment
class Monad m => TypeEnvMonad m where
  -- | Get the current type environment
  getTypeEnv :: m TypeEnv
  getTypeEnv = askTypeEnv id
  
  -- | Query the current type environment
  askTypeEnv :: (TypeEnv -> a) -> m a
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
  getTypeEnv = lift getTypeEnv
  askTypeEnv f = lift (askTypeEnv f)
  assumeWithProperties v t b (MaybeT m) = MaybeT (assumeWithProperties v t b m)

-- | A monad supporting type-level computation
class (MonadIO m, Supplies m (Ident Var), TypeEnvMonad m) => EvalMonad m where
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
  | TyConTypeAssignment
    { varType :: !Type
      
    , dataType :: !DataType
    }
    -- | Type of a data constructor
  | DataConTypeAssignment
    { -- | Type of the data constructor when used as an operator.
      --   This field will eventually be removed, and the type computed
      --   on demand instead.
      varType :: Type

    , dataConType :: !DataConType
    }
    -- | Type and definition of a type function
  | TyFunTypeAssignment
    { varType :: !Type
    , tyFunType :: !type_function
    }

-- | Create a 'VarTypeAssignment' with default properties.
varTypeAssignment :: Type -> TypeAssignment a
varTypeAssignment t = VarTypeAssignment t False

data DataType =
  DataType
  { -- | The kind of a value whose type is a
    --   fully applied instance of this data type.
    dataTypeKind :: BaseKind
    
    -- | Abstractness of the data type.
    --   If a data type is abstract, then the compiler should not introduce
    --   data constructor expressions or case expressions for this type.
    --   It is still permissible to optimize such expressions if they are
    --   already present in the code.
  , dataTypeIsAbstract :: !Bool
    
    -- | Data constructors of this data type
  , dataTypeDataConstructors :: [Var]
  }

-- | Describes a data constructor.
--
--   The type of a constructed value is determined by its type parameters.
--   If the type parameters are @a1 ... aN@ and the type constructor is @T@,
--   then the type of the constructed value is @T a1 ... aN@.
data DataConType =
  DataConType
  { -- | Type parameters.  Type parameters are passed as arguments when 
    --   constructing a value and when deconstructing it.
    dataConPatternParams :: [Binder]

    -- | Existential types.  These are passed
    --   as arguments when constructing a value, and matched as paramters
    --   when deconstructing it.  They have no run-time representation.
    --   These must be dependent value patterns (@ValPT (Just _)@).
  , dataConPatternExTypes :: [Binder]

    -- | Fields.  These are passed as arguments when constructing a value,
    -- and matched as parameters when deconstructing it.
  , dataConPatternArgs :: [Type]

  , dataConCon :: Var           -- ^ This data constructor
  , dataConTyCon :: Var         -- ^ The type inhabited by constructed values
  }

-- | The type of a 'DataConType' value.
dataConPatternRange :: DataConType -> Type
dataConPatternRange dcon_type =
  let args = [VarT a | (a ::: _) <- dataConPatternParams dcon_type]
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

-- | A built-in type function has two implementations, depending on whether
--   it's being evaluated in the pure or mem variant of the type system
data BuiltinTypeFunction =
  BuiltinTypeFunction
  { builtinPureTypeFunction :: !TypeFunction
  , builtinMemTypeFunction :: !TypeFunction
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
               (sideeffectV, varTypeAssignment kindT),
               (writeV, varTypeAssignment kindT),
               (posInftyV, varTypeAssignment intindexT),
               (negInftyV, varTypeAssignment intindexT)]

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
  DataTypeDescr Var Type [(Type, DataConType)] Bool

insertDataType :: DataTypeDescr
               -> TypeEnvBase type_function -> TypeEnvBase type_function
insertDataType (DataTypeDescr ty_con kind ctors abstract) (TypeEnv env) =
  TypeEnv $ foldr insert env (ty_con_assignment : data_con_assignments)
  where
    insert (v, a) env = IntMap.insert (fromIdent $ varID v) a env
    data_cons = [dataConCon dtor | (_, dtor) <- ctors]
    data_con_assignments =
      [(dataConCon dtor, DataConTypeAssignment ty dtor)
      | (ty, dtor) <- ctors]
    data_type = DataType (result_kind kind) abstract data_cons
    ty_con_assignment = (ty_con, TyConTypeAssignment kind data_type)
    
    -- The kind of a fully applied instance of the data constructor
    result_kind k = case k
                    of FunT _ k2 -> result_kind k2
                       VarT {}   -> toBaseKind k

insertTypeFunction :: Var -> Type -> type_function
                   -> TypeEnvBase type_function -> TypeEnvBase type_function
insertTypeFunction v ty f (TypeEnv env) =
  TypeEnv $ IntMap.insert (fromIdent $ varID v) (TyFunTypeAssignment ty f) env

lookupDataCon :: Var -> TypeEnvBase type_function -> Maybe DataConType
{-# INLINE lookupDataCon #-}
lookupDataCon v (TypeEnv env) =
  case IntMap.lookup (fromIdent $ varID v) env
  of Just (DataConTypeAssignment _ dtor) -> Just dtor
     _ -> Nothing

lookupDataType :: Var -> TypeEnvBase type_function -> Maybe DataType
{-# INLINE lookupDataType #-}
lookupDataType v (TypeEnv env) =
  case IntMap.lookup (fromIdent $ varID v) env
  of Just (TyConTypeAssignment _ tc) -> Just tc
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
  fmap varType $ IntMap.lookup (fromIdent $ varID v) env

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
    get_data_con (DataConTypeAssignment _ dcon) = Just dcon 
    get_data_con _ = Nothing

-- | Get all types in the type environment
getAllTypes :: TypeEnvBase type_function -> IntMap.IntMap Type
getAllTypes (TypeEnv env) = IntMap.map varType env

-- | Create a docstring showing all types in the type environment
pprTypeEnv :: TypeEnvBase type_function -> Doc
pprTypeEnv tenv =
  vcat [ hang (text (show n) <+> text "|->") 8 (pprType t)
       | (n, t) <- IntMap.toList $ getAllTypes tenv]

{-
-------------------------------------------------------------------------------

-- | Convert an ordinary type environment to a pure type environment
convertToPureTypeEnv :: TypeEnv -> TypeEnv
convertToPureTypeEnv (TypeEnv m) =
  TypeEnv (IntMap.map convertToPureTypeAssignment m)

convertToPureTypeAssignment ass =
  case ass
  of VarTypeAssignment rt ->
       VarTypeAssignment (convertToPureReturnType rt)
     TyConTypeAssignment rt cons ->
       TyConTypeAssignment (convertToPureReturnType rt) cons
     DataConTypeAssignment rt con_type ->
       DataConTypeAssignment (convertToPureReturnType rt) (convertToPureDataConType con_type)
     TyFunTypeAssignment rt f ->
       TyFunTypeAssignment (convertToPureReturnType rt) f

convertToPureParamType (param ::: ty) =
  let param' = case param
               of ValPT (Just v) -> param
                  _ -> ValPT Nothing
  in param' ::: convertToPureType ty

convertToPureReturnType (_ ::: ty) = ValRT ::: convertToPureType ty

convertToPureType ty =
  case ty
  of VarT t -> ty
     AppT op arg -> AppT (convertToPureType op) (convertToPureType arg)
     FunT arg ret -> FunT (convertToPureParamType arg) (convertToPureReturnType ret)
     AnyT _ -> ty
     IntT _ -> ty

convertToPureDataConType (DataConType params eparams args range con ty_con) =
  DataConType (map convertToPureParamType params)
              (map convertToPureParamType eparams)
              (map convertToPureReturnType args)
              (convertToPureReturnType range)
              con
              ty_con

-------------------------------------------------------------------------------

-- | Convert an ordinary type environment to an explicit memory passing
--   type environment
convertToMemTypeEnv :: TypeEnv -> TypeEnv
convertToMemTypeEnv (TypeEnv m) =
  TypeEnv (IntMap.map convertToMemTypeAssignment m)
  
convertToMemTypeAssignment ass =
  case ass
  of VarTypeAssignment rt ->
       VarTypeAssignment (convertToMemReturnType rt)
     TyConTypeAssignment rt cons ->
       TyConTypeAssignment (convertToMemReturnType rt) cons
     DataConTypeAssignment rt con_type ->
       DataConTypeAssignment (convertToMemReturnType rt) (convertToMemDataConType con_type)
     TyFunTypeAssignment rt f ->
       TyFunTypeAssignment (convertToMemReturnType rt) f

convertToMemParamType (repr ::: ty) 
  | getLevel ty == TypeLevel =
    case repr
    of WritePT ->
         -- Convert to a function type (output_pointer -> sideeffect)
         BoxPT ::: FunT (OutPT ::: convertToMemType ty) (SideEffectRT ::: convertToMemType ty)
       _ -> repr ::: convertToMemType ty
  | otherwise =
    repr ::: convertToMemType ty

convertToMemReturnType (repr ::: ty)
  | getLevel ty == TypeLevel =
    case repr
    of WriteRT ->
         BoxRT ::: FunT (OutPT ::: convertToMemType ty) (SideEffectRT ::: convertToMemType ty)
       _ -> repr ::: convertToMemType ty
  | otherwise =
      repr ::: convertToMemType ty

convertToMemType ty =
  case ty
  of VarT t -> ty
     AppT op arg -> AppT (convertToMemType op) (convertToMemType arg)
     FunT arg ret -> FunT (convertToMemParamType arg) (convertToMemReturnType ret)
     AnyT _ -> ty
     IntT _ -> ty

convertToMemDataConType (DataConType params eparams args range con ty_con) =
  DataConType (map convertToMemParamType params)
              (map convertToMemParamType eparams)
              (map convertToMemReturnType args)
              (convertToMemReturnType range)
              con
              ty_con
-}              
-------------------------------------------------------------------------------

-- | True if the variable is an adapter type constructor or function.
--
--   Adapter types are inserted to convert data between representations
--   without changing the values.
isAdapterCon :: Var -> Bool
isAdapterCon v = v `elem` adapters
  where
    adapters = [pyonBuiltin The_Writer,
                pyonBuiltin The_Stored,
                pyonBuiltin The_StoredBox,
                pyonBuiltin The_Boxed,
                pyonBuiltin The_BoxedType,
                pyonBuiltin The_BareType]

specToPureTypeEnv :: SpecTypeEnv -> TypeEnv
specToPureTypeEnv (TypeEnv m) =
  TypeEnv (IntMap.mapMaybe specToPureTypeAssignment m)

specToPureTypeAssignment :: SpecTypeAssignment -> Maybe PureTypeAssignment
specToPureTypeAssignment ass =
  case ass
  of VarTypeAssignment rt conlike ->
       VarTypeAssignment <$> specToPureTypeOrKind rt <*> pure conlike
     TyConTypeAssignment rt cons ->
       TyConTypeAssignment <$> specToPureKind rt <*> pure cons
     DataConTypeAssignment rt con_type ->
       DataConTypeAssignment <$> specToPureType rt
                             <*> specToPureDataConType con_type
     TyFunTypeAssignment rt f ->
       TyFunTypeAssignment <$>
       specToPureKind rt <*>
       pure (builtinPureTypeFunction f)

specToPureTypeOrKind e =
  case getLevel e
  of TypeLevel -> specToPureType e
     KindLevel -> specToPureKind e
     SortLevel -> Just e        -- Sorts are unchanged
     _ -> internalError "specToPureTypeOrKind: Not a type, kind, or sort"

specToPureType ty =
  case fromVarApp ty
  of Just (con, [arg])
       -- Adapter types are ignored in the pure representation. 
       | isAdapterCon con ->
           specToPureType arg
       
     -- Recurse on other types
     _ -> case ty
          of VarT _ -> pure ty
             AppT op arg -> AppT <$> specToPureType op <*> specToPureType arg
             LamT (x ::: dom) body -> do
               dom' <- specToPureKind dom
               body' <- specToPureType body
               return $ LamT (x ::: dom') body'
             FunT arg ret -> FunT <$> specToPureType arg <*> specToPureType ret
             AllT (x ::: dom) rng -> do
               dom' <- specToPureKind dom
               rng' <- specToPureType rng
               return $ AllT (x ::: dom') rng'
             AnyT _ -> pure ty
             IntT _ -> pure ty
             UTupleT _ -> Nothing
             CoT _ -> pure ty

-- Every value is represented in boxed form, so they all have kind 'box'.
-- Types that do not describe values (such as intindexT) can still have
-- distinct kinds.
--
-- The kinds 'out' and 'sideeffect' have no equivalent pure term.  If
-- they appear in a type, then 'Nothing' is returned.  The type environment
-- entry that mentions this kind will be removed from the environment.
specToPureKind :: Kind -> Maybe Kind
specToPureKind k =
  case k
  of VarT kind_var
       | kind_var == boxV      -> Just boxT
       | kind_var == bareV     -> Just boxT
       | kind_var == valV      -> Just boxT
       | kind_var == intindexV -> Just intindexT
       | otherwise             -> Nothing
     dom `FunT` rng -> liftM2 FunT (specToPureKind dom) (specToPureKind rng)
     _ -> internalError "specToPureKind: Unexpected kind"

specToPureDataConType dcon_type = do
  ty_params <- mapM type_param $ dataConPatternParams dcon_type
  ex_types <- mapM type_param $ dataConPatternExTypes dcon_type
  args <- mapM specToPureType $ dataConPatternArgs dcon_type
  return $ DataConType
           { dataConPatternParams  = ty_params
           , dataConPatternExTypes = ex_types
           , dataConPatternArgs    = args
           , dataConCon            = dataConCon dcon_type
           , dataConTyCon          = dataConTyCon dcon_type
           }
  where
    type_param (v ::: t) = fmap (v :::) $ specToPureKind t

specToMemTypeEnv :: SpecTypeEnv -> TypeEnv
specToMemTypeEnv (TypeEnv m) =
  TypeEnv (IntMap.map specToMemTypeAssignment m)

specToMemTypeAssignment ass =
  case ass
  of VarTypeAssignment rt conlike ->
       VarTypeAssignment (specToMemType rt) conlike
     TyConTypeAssignment rt cons ->
       TyConTypeAssignment (specToMemType rt) cons
     DataConTypeAssignment rt con_type ->
       DataConTypeAssignment (specToMemType rt) (specToMemDataConType con_type)
     TyFunTypeAssignment rt f ->
       TyFunTypeAssignment (specToMemType rt) (builtinMemTypeFunction f)

specToMemType ty =
  case fromVarApp ty
  of Just (con, [arg])
       -- Replace applications of 'Writer' by initializer functions.
       | con `isPyonBuiltin` The_Writer ->
           let mem_arg = specToMemType arg
           in initializerType mem_arg
       
     -- Recurse on other types
     _ -> case ty
          of VarT _ -> ty
             AppT op arg -> AppT (specToMemType op) (specToMemType arg)
             FunT arg ret -> FunT (specToMemType arg) (specToMemType ret)
             AnyT _ -> ty
             IntT _ -> ty
             AllT (x ::: dom) rng ->
               AllT (x ::: specToMemType dom) (specToMemType rng)
             LamT (x ::: dom) body ->
               LamT (x ::: specToMemType dom) (specToMemType body)
             UTupleT ks -> UTupleT ks
             CoT _ -> ty

specToMemDataConType dcon_type =
  DataConType
  { dataConPatternParams  = map type_param $ dataConPatternParams dcon_type
  , dataConPatternExTypes = map type_param $ dataConPatternExTypes dcon_type
  , dataConPatternArgs    = map specToMemType $ dataConPatternArgs dcon_type
  , dataConCon            = dataConCon dcon_type
  , dataConTyCon          = dataConTyCon dcon_type
  }
  where
    type_param (v ::: t) = v ::: specToMemType t

initializerType t =
  FunT (varApp (pyonBuiltin The_OutPtr) [t])
       (varApp (pyonBuiltin The_IEffect) [t])

-------------------------------------------------------------------------------

-- | Convert a specification type environment to one where types can be
--   compared.  The 'mem' variant of type functions is selected.  All types
--   remain unchanged.
specToTypeEnv :: SpecTypeEnv -> TypeEnv
specToTypeEnv (TypeEnv m) =
  TypeEnv (IntMap.map specToTypeAssignment m)

specToTypeAssignment ass =
  case ass
  of VarTypeAssignment t conlike -> VarTypeAssignment t conlike
     TyConTypeAssignment t cons -> TyConTypeAssignment t cons
     DataConTypeAssignment t con_type -> DataConTypeAssignment t con_type
     TyFunTypeAssignment t f -> TyFunTypeAssignment t (builtinMemTypeFunction f)
