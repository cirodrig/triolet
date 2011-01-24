
module Type.Environment
       (TypeEnv,
        DataType(..),
        DataConType(..),
        DataTypeDescr(..),
        lookupType,
        lookupDataType,
        lookupDataCon,
        emptyTypeEnv,
        wiredInTypeEnv,
        insertType,
        insertDataType,
        convertToPureTypeEnv,
        convertToMemTypeEnv,
        convertToMemParamType,
        convertToMemReturnType,
        convertToMemType,
       )
where

import qualified Data.IntMap as IntMap

import Common.Error
import Common.Identifier
import Type.Type

-- | A type assigned to a Var
data TypeAssignment =
    -- | Type of a variable
    VarTypeAssignment
    { varType :: !(ReturnRepr ::: Type)
    }
    -- | Type of a type constructor
  | TyConTypeAssignment
    { varType :: !(ReturnRepr ::: Type)
      
    , dataType :: !DataType
    }
    -- | Type of a data constructor
  | DataConTypeAssignment
    { -- | Type of the data constructor when used as an operator 
      varType :: !(ReturnRepr ::: Type)

    , dataConType :: !DataConType
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
  { -- | Parameters (passed as arguments)
    dataConPatternParams :: [ParamRepr ::: Type]

    -- | Arguments (bound to variables)
  , dataConPatternArgs :: [ReturnRepr ::: Type]

    -- | Type of the constructed value.
    -- May mention the pattern parameters.
  , dataConPatternRange :: ReturnRepr ::: Type

  , dataConTyCon :: Var
  }

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
  DataTypeDescr Var (ReturnRepr ::: Type) Repr [(Var, (ReturnRepr ::: Type), DataConType)]

insertDataType :: DataTypeDescr -> TypeEnv -> TypeEnv
insertDataType (DataTypeDescr ty_con kind repr ctors) (TypeEnv env) =
  TypeEnv $ foldr insert env (ty_con_assignment : data_con_assignments)
  where
    insert (v, a) env = IntMap.insert (fromIdent $ varID v) a env
    ty_con_assignment =
      (ty_con, TyConTypeAssignment kind (DataType repr data_cons))
    data_con_assignments =
      [(data_con, DataConTypeAssignment ty dtor)
      | (data_con, ty, dtor) <- ctors]
    data_cons = [v | (v, _, _) <- ctors]

lookupDataCon :: Var -> TypeEnv -> Maybe DataConType
lookupDataCon v (TypeEnv env) =
  case IntMap.lookup (fromIdent $ varID v) env
  of Just (DataConTypeAssignment _ dtor) -> Just dtor
     _ -> Nothing

lookupDataType :: Var -> TypeEnv -> Maybe DataType
lookupDataType v (TypeEnv env) =
  case IntMap.lookup (fromIdent $ varID v) env
  of Just (TyConTypeAssignment _ tc) -> Just tc
     _ -> Nothing

-- | Look up the type of a variable
lookupType :: Var -> TypeEnv -> Maybe (ReturnRepr ::: Type)
lookupType v (TypeEnv env) =
  fmap varType $ IntMap.lookup (fromIdent $ varID v) env

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

convertToPureDataConType (DataConType params args range ty_con) =
  DataConType (map convertToPureParamType params)
              (map convertToPureReturnType args)
              (convertToPureReturnType range)
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

convertToMemDataConType (DataConType params args range ty_con) =
  DataConType (map convertToMemParamType params)
              (map convertToMemReturnType args)
              (convertToMemReturnType range)
              ty_con