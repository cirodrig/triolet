
module Type.Environment
       (TypeEnv,
        DataType(..),
        DataConType(..),
        DataTypeDescr(..),
        lookupType,
        lookupDataType,
        lookupDataCon,
        getAllDataConstructors,
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
lookupType :: Var -> TypeEnv -> Maybe ReturnType
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

convertToMemDataConType (DataConType params eparams args range con ty_con) =
  DataConType (map convertToMemParamType params)
              (map convertToMemParamType eparams)
              (map convertToMemReturnType args)
              (convertToMemReturnType range)
              con
              ty_con