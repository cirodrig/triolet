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

{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
module Type.Environment
       (TypeEnvMonad(..),
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
        emptyTypeEnv,
        wiredInTypeEnv,
        insertType,
        insertDataType,
        insertTypeFunction,
        convertToPureTypeEnv,
        convertToMemTypeEnv,
        convertToMemParamType,
        convertToMemReturnType,
        convertToMemType,
       )
where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import qualified Data.IntMap as IntMap

import Common.Error
import Common.Identifier
import Common.Supply
import Type.Type

-------------------------------------------------------------------------------
-- Support for type-level computation

-- | A monad that keeps track of the current type environment
class Monad m => TypeEnvMonad m where
  getTypeEnv :: m TypeEnv

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

instance EvalMonad TypeEvalM

-------------------------------------------------------------------------------

-- | A type assigned to a Var
data TypeAssignment =
    -- | Type of a variable
    VarTypeAssignment
    { varType :: !ReturnType
    }
    -- | Type of a type constructor
  | TyConTypeAssignment
    { varType :: !ReturnType
      
    , dataType :: !DataType
    }
    -- | Type of a data constructor
  | DataConTypeAssignment
    { -- | Type of the data constructor when used as an operator 
      varType :: !ReturnType

    , dataConType :: !DataConType
    }
    -- | Type and definition of a type function
  | TyFunTypeAssignment
    { varType :: !ReturnType
    , tyFunType :: !TypeFunction
    }

data DataType =
  DataType
  { -- | The default representation used for values that are instances of
    --   this type constructor
    dataTypeRepresentation :: !Repr
    
    -- | Data constructors of this data type
  , dataTypeDataConstructors :: [Var]
  }

-- | Describes how a data constructor behaves in a pattern matchi
data DataConType =
  DataConType
  { -- | Type parameters.  Type parameters are passed as arguments when 
    --   constructing a value and when deconstructing it.
    --   These must be value patterns (@ValPT _@).
    dataConPatternParams :: [ParamType]

    -- | Existential types.  These are passed
    --   as arguments when constructing a value, and matched as paramters
    --   when deconstructing it.  They have no run-time representation.
    --   These must be dependent value patterns (@ValPT (Just _)@).
  , dataConPatternExTypes :: [ParamType]

    -- | Fields.  These are passed as arguments when constructing a value,
    -- and matched as parameters when deconstructing it.
  , dataConPatternArgs :: [ReturnType]

    -- | Type of the constructed value.
    -- May mention the pattern parameters.
  , dataConPatternRange :: ReturnType

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
  , _tyfunReduction :: !([Type] -> TypeEvalM Type)
  }

-- | Create a type function
typeFunction :: Int -> ([Type] -> TypeEvalM Type) -> TypeFunction
typeFunction = TypeFunction

typeFunctionArity :: TypeFunction -> Int
typeFunctionArity = _tyfunArity

applyTypeFunction :: TypeFunction -> [Type] -> TypeEvalM Type
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
    entries = [(pureV, VarTypeAssignment (ValRT ::: VarT kindV))]

-- | Insert a variable type assignment
insertType :: Var -> ReturnRepr ::: Type -> TypeEnv -> TypeEnv
insertType v t (TypeEnv env) =
  TypeEnv (IntMap.insert (fromIdent $ varID v) (VarTypeAssignment t) env)

data DataTypeDescr =
  DataTypeDescr Var ReturnType Repr [(ReturnType, DataConType)]

insertDataType :: DataTypeDescr -> TypeEnv -> TypeEnv
insertDataType (DataTypeDescr ty_con kind repr ctors) (TypeEnv env) =
  TypeEnv $ foldr insert env (ty_con_assignment : data_con_assignments)
  where
    insert (v, a) env = IntMap.insert (fromIdent $ varID v) a env
    ty_con_assignment =
      (ty_con, TyConTypeAssignment kind (DataType repr data_cons))
    data_con_assignments =
      [(dataConCon dtor, DataConTypeAssignment ty dtor)
      | (ty, dtor) <- ctors]
    data_cons = [dataConCon dtor | (_, dtor) <- ctors]

insertTypeFunction :: Var -> ReturnType -> TypeFunction
                   -> TypeEnv -> TypeEnv
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
lookupType :: Var -> TypeEnv -> Maybe ReturnType
{-# INLINE lookupType #-}
lookupType v (TypeEnv env) =
  fmap varType $ IntMap.lookup (fromIdent $ varID v) env

-- | Get all data constructors in the type environment
getAllDataConstructors :: TypeEnv -> IntMap.IntMap DataConType
getAllDataConstructors (TypeEnv env) = IntMap.mapMaybe get_data_con env 
  where
    get_data_con (DataConTypeAssignment _ dcon) = Just dcon 
    get_data_con _ = Nothing

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

convertToMemDataConType (DataConType params eparams args range con ty_con) =
  DataConType (map convertToMemParamType params)
              (map convertToMemParamType eparams)
              (map convertToMemReturnType args)
              (convertToMemReturnType range)
              con
              ty_con