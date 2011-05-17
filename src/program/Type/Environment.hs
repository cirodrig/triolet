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
        assumeBinder,
        EvalMonad,
        TypeEvalM(..),
        TypeEnv,
        DataType(..),
        DataConType(..),
        DataTypeDescr(..),
        TypeFunction,
        typeFunction,
        typeFunctionArity,
        applyTypeFunction,
        lookupType,
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
        insertDataType,
        insertTypeFunction,
       
        -- * New conversion routines
        specToPureTypeEnv,
        specToMemTypeEnv,
       )
where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans
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
  
  -- | Query the current type environment
  askTypeEnv :: (TypeEnv -> a) -> m a
  askTypeEnv f = liftM f getTypeEnv

  -- | Add a variable to the type environment
  assume :: Var -> Type -> m a -> m a

assumeBinder :: TypeEnvMonad m => Binder -> m a -> m a
assumeBinder (v ::: t) m = assume v t m

-- | A monad supporting type-level computation
class (MonadIO m, Supplies m (Ident Var), TypeEnvMonad m) => EvalMonad m

-- | A simple monad supporting type-level computation
newtype TypeEvalM a =
  TypeEvalM {runTypeEvalM :: IdentSupply Var -> TypeEnv -> IO a}

instance Functor TypeEvalM where
  {-# INLINE fmap #-}
  fmap f m = TypeEvalM $ \supply env -> fmap f (runTypeEvalM m supply env)

instance Applicative TypeEvalM where
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
  
  assume v t m =
    TypeEvalM $ \supply tenv -> runTypeEvalM m supply (insertType v t tenv)

instance EvalMonad TypeEvalM

-------------------------------------------------------------------------------

-- | A type assigned to a Var
data TypeAssignment =
    -- | Type of a variable
    VarTypeAssignment
    { varType :: !Type
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
    , tyFunType :: !TypeFunction
    }

data DataType =
  DataType
  { -- | The kind of a value whose type is a
    --   fully applied instance of this data type.
    dataTypeKind :: BaseKind
    
    -- | Data constructors of this data type
  , dataTypeDataConstructors :: [Var]
  }

-- | Describes how a data constructor behaves in a pattern matchi
data DataConType =
  DataConType
  { -- | Type parameters.  Type parameters are passed as arguments when 
    --   constructing a value and when deconstructing it.
    --   These must be value patterns (@ValPT _@).
    dataConPatternParams :: [Binder]

    -- | Existential types.  These are passed
    --   as arguments when constructing a value, and matched as paramters
    --   when deconstructing it.  They have no run-time representation.
    --   These must be dependent value patterns (@ValPT (Just _)@).
  , dataConPatternExTypes :: [Binder]

    -- | Fields.  These are passed as arguments when constructing a value,
    -- and matched as parameters when deconstructing it.
  , dataConPatternArgs :: [Type]

    -- | Type of the constructed value.
    -- May mention the pattern parameters.
  , dataConPatternRange :: Type

  , dataConCon :: Var           -- ^ This data constructor
  , dataConTyCon :: Var         -- ^ The type inhabited by constructed values
  }

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
  , _tyfunReduction :: !(EvalMonad m => [Type] -> m Type)
  }

-- | Create a type function
typeFunction :: Int -> (forall m. EvalMonad m => [Type] -> m Type) -> TypeFunction
typeFunction = TypeFunction

typeFunctionArity :: TypeFunction -> Int
typeFunctionArity = _tyfunArity

applyTypeFunction :: EvalMonad m => TypeFunction -> [Type] -> m Type
applyTypeFunction = _tyfunReduction

-- | A type environment maps variables to types
newtype TypeEnv = TypeEnv (IntMap.IntMap TypeAssignment)

emptyTypeEnv :: TypeEnv
emptyTypeEnv = TypeEnv IntMap.empty

-- | A Type environment containing the variables defined in "Type.Type"
wiredInTypeEnv :: TypeEnv
wiredInTypeEnv =
  TypeEnv $ IntMap.fromList [(fromIdent $ varID v, t) | (v, t) <- entries]
  where
    entries = [(intindexV, VarTypeAssignment kindT),
               (valV, VarTypeAssignment kindT),
               (boxV, VarTypeAssignment kindT),
               (bareV, VarTypeAssignment kindT),
               (outV, VarTypeAssignment kindT),
               (sideeffectV, VarTypeAssignment kindT),
               (writeV, VarTypeAssignment kindT),
               (posInftyV, VarTypeAssignment intindexT)]

-- | Insert a variable type assignment
insertType :: Var -> Type -> TypeEnv -> TypeEnv
insertType v t (TypeEnv env) =
  TypeEnv (IntMap.insert (fromIdent $ varID v) (VarTypeAssignment t) env)

-- | A description of a data type that will be added to a type environment.
data DataTypeDescr =
  DataTypeDescr Var Type [(Type, DataConType)]

insertDataType :: DataTypeDescr -> TypeEnv -> TypeEnv
insertDataType (DataTypeDescr ty_con kind ctors) (TypeEnv env) =
  TypeEnv $ foldr insert env (ty_con_assignment : data_con_assignments)
  where
    insert (v, a) env = IntMap.insert (fromIdent $ varID v) a env
    ty_con_assignment =
      (ty_con, TyConTypeAssignment kind (DataType (result_kind kind) data_cons))
    data_con_assignments =
      [(dataConCon dtor, DataConTypeAssignment ty dtor)
      | (ty, dtor) <- ctors]
    data_cons = [dataConCon dtor | (_, dtor) <- ctors]
    
    -- The kind of a fully applied instance of the data constructor
    result_kind k = case k
                    of FunT _ k2 -> result_kind k2
                       VarT {}   -> toBaseKind k

insertTypeFunction :: Var -> Type -> TypeFunction -> TypeEnv -> TypeEnv
insertTypeFunction v ty f (TypeEnv env) =
  TypeEnv $ IntMap.insert (fromIdent $ varID v) (TyFunTypeAssignment ty f) env

lookupDataCon :: Var -> TypeEnv -> Maybe DataConType
{-# INLINE lookupDataCon #-}
lookupDataCon v (TypeEnv env) =
  case IntMap.lookup (fromIdent $ varID v) env
  of Just (DataConTypeAssignment _ dtor) -> Just dtor
     _ -> Nothing

lookupDataType :: Var -> TypeEnv -> Maybe DataType
{-# INLINE lookupDataType #-}
lookupDataType v (TypeEnv env) =
  case IntMap.lookup (fromIdent $ varID v) env
  of Just (TyConTypeAssignment _ tc) -> Just tc
     _ -> Nothing

lookupDataConWithType :: Var -> TypeEnv -> Maybe (DataType, DataConType)
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
lookupType :: Var -> TypeEnv -> Maybe Type
{-# INLINE lookupType #-}
lookupType v (TypeEnv env) =
  fmap varType $ IntMap.lookup (fromIdent $ varID v) env

-- | Get all data constructors in the type environment
getAllDataConstructors :: TypeEnv -> IntMap.IntMap DataConType
getAllDataConstructors (TypeEnv env) = IntMap.mapMaybe get_data_con env 
  where
    get_data_con (DataConTypeAssignment _ dcon) = Just dcon 
    get_data_con _ = Nothing

-- | Get all types in the type environment
getAllTypes :: TypeEnv -> IntMap.IntMap Type
getAllTypes (TypeEnv env) = IntMap.map varType env

-- | Create a docstring showing all types in the type environment
pprTypeEnv :: TypeEnv -> Doc
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

specToPureTypeEnv :: TypeEnv -> TypeEnv
specToPureTypeEnv (TypeEnv m) =
  TypeEnv (IntMap.mapMaybe specToPureTypeAssignment m)

specToPureTypeAssignment :: TypeAssignment -> Maybe TypeAssignment
specToPureTypeAssignment ass =
  case ass
  of VarTypeAssignment rt ->
       VarTypeAssignment <$> specToPureTypeOrKind rt
     TyConTypeAssignment rt cons ->
       TyConTypeAssignment <$> specToPureKind rt <*> pure cons
     DataConTypeAssignment rt con_type ->
       DataConTypeAssignment <$> specToPureType rt
                             <*> specToPureDataConType con_type
     TyFunTypeAssignment rt f ->
       TyFunTypeAssignment <$> specToPureKind rt <*> pure f

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
       -- Remove applications of 'Writer', 'Stored', and 'Boxed'.
       | con `isPyonBuiltin` the_Writer || 
         con `isPyonBuiltin` the_Stored ||
         con `isPyonBuiltin` the_Boxed ->
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
  range <- specToPureType $ dataConPatternRange dcon_type
  return $ DataConType
           { dataConPatternParams  = ty_params
           , dataConPatternExTypes = ex_types
           , dataConPatternArgs    = args
           , dataConPatternRange   = range
           , dataConCon            = dataConCon dcon_type
           , dataConTyCon          = dataConTyCon dcon_type
           }
  where
    type_param (v ::: t) = fmap (v :::) $ specToPureKind t

specToMemTypeEnv :: TypeEnv -> TypeEnv
specToMemTypeEnv (TypeEnv m) =
  TypeEnv (IntMap.map specToMemTypeAssignment m)

specToMemTypeAssignment ass =
  case ass
  of VarTypeAssignment rt ->
       VarTypeAssignment (specToMemType rt)
     TyConTypeAssignment rt cons ->
       TyConTypeAssignment (specToMemType rt) cons
     DataConTypeAssignment rt con_type ->
       DataConTypeAssignment (specToMemType rt) (specToMemDataConType con_type)
     TyFunTypeAssignment rt f ->
       TyFunTypeAssignment (specToMemType rt) f

specToMemType ty =
  case fromVarApp ty
  of Just (con, [arg])
       -- Replace applications of 'Writer' by initializer functions.
       | con `isPyonBuiltin` the_Writer ->
           let mem_arg = specToMemType arg
           in initializerType mem_arg
       
     -- Recurse on other types
     _ -> case ty
          of VarT _ -> ty
             AppT op arg -> AppT (specToMemType op) (specToMemType arg)
             FunT arg ret -> FunT (specToMemType arg) (specToMemType ret)
             AllT (x ::: dom) rng ->
               AllT (x ::: specToMemType dom) (specToMemType rng)
             AnyT _ -> ty
             IntT _ -> ty
             LamT (x ::: dom) body ->
               LamT (x ::: specToMemType dom) (specToMemType body)
             AllT (x ::: dom) rng ->
               LamT (x ::: specToMemType dom) (specToMemType rng)

specToMemDataConType dcon_type =
  DataConType
  { dataConPatternParams  = map type_param $ dataConPatternParams dcon_type
  , dataConPatternExTypes = map type_param $ dataConPatternExTypes dcon_type
  , dataConPatternArgs    = map specToMemType $ dataConPatternArgs dcon_type
  , dataConPatternRange   = specToMemType $ dataConPatternRange dcon_type
  , dataConCon            = dataConCon dcon_type
  , dataConTyCon          = dataConTyCon dcon_type
  }
  where
    type_param (v ::: t) = v ::: specToMemType t

initializerType t =
  FunT (varApp (pyonBuiltin the_OutPtr) [t])
       (varApp (pyonBuiltin the_IEffect) [t])