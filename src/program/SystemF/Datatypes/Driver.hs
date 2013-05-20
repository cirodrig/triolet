
module SystemF.Datatypes.Driver
       (computeDataTypeInfo, addLayoutVariablesToTypeEnvironment)
where

import Control.DeepSeq
import Control.Monad
import Control.Monad.Trans
import qualified Data.IntMap as IntMap
import Data.Maybe
import Debug.Trace
import Text.PrettyPrint.HughesPJ
  
import Common.Error
import Common.Identifier
import Common.Label
import Common.Supply
import Common.MonadLogic
import Type.Type
import Type.Environment
import Type.Compare
import Type.Eval
import qualified LowLevel.Syntax as LL
import SystemF.Syntax
import SystemF.MemoryIR

import SystemF.Datatypes.Structure
import SystemF.Datatypes.TypeObject

-- | Primitive value types.  These get special auto-generated definitions.
primitiveValTypes :: [Var]
primitiveValTypes = [intV, uintV, floatV]

-- | Compute layout information for all algebraic data types in the
--   given environment.  The type environment is modified in-place
--   by adding layout information to data types and by adding 
--   global serializer functions to the type environment.
--
--   Returns a list of all data types for which info was created and a
--   list of global variable definitions.
computeDataTypeInfo :: IdentSupply LL.Var
                    -> IdentSupply Var
                    -> TypeEnv
                    -> IO ([Var], [GDef Mem])
computeDataTypeInfo ll_var_supply var_supply type_env =
  runTypeEvalM compute var_supply type_env
  where
    compute = do
      -- Create layout information for each algebraic data type
      -- and update the type environment
      m_dtypes_needing_info <-
        mapM setLayoutInformation =<< get_algebraic_data_types
      let dtypes_needing_info = catMaybes m_dtypes_needing_info

      -- Create and return definitions of the info variables
      defss <-
        assume_info_vars dtypes_needing_info $ sequence
        [ -- Algebraic types
          liftM concat $ mapM define_info_var dtypes_needing_info

          -- Primitive types
        , liftM concat $ mapM define_primitive_info_var primitiveValTypes
        ]
      return (dtypes_needing_info, concat defss)

    define_primitive_info_var data_type_con = do
      Just dtype <- lookupDataType data_type_con
      definePrimitiveValInfo ll_var_supply dtype

    -- Create definitions for the info variables
    define_info_var :: Var -> UnboxedTypeEvalM [GDef Mem]
    define_info_var data_type_con = do
      Just dtype <- lookupDataType data_type_con
      case dataTypeKind dtype of
        ValK  -> valInfoDefinition ll_var_supply dtype
        BareK -> bareInfoDefinition ll_var_supply dtype
        BoxK  -> boxInfoDefinitions ll_var_supply dtype

    -- Given a list of data type constructors, add all their info variables
    -- to the environment
    assume_info_vars :: [Var] -> UnboxedTypeEvalM a -> UnboxedTypeEvalM a
    assume_info_vars data_type_cons m = do
      dtypes <- mapM lookupDataType data_type_cons

      -- For each data type, for each info variable, create a binding
      let bindings :: [Binder]
          bindings = [ v ::: infoConstructorType dtype
                     | m_dtype <- dtypes
                     , let Just dtype = m_dtype
                     , v <- layoutInfoVars $ dataTypeLayout' dtype
                     ]
      assumeBinders bindings m

    get_algebraic_data_types :: UnboxedTypeEvalM [DataType]
    get_algebraic_data_types = do
      i_type_env <- freezeTypeEnv
      return $ filter dataTypeIsAlgebraic $ IntMap.elems $
        getAllDataTypeConstructors i_type_env
 
-- | Compute size parameters for an algebraic data type constructor, and
--   save them in the type environment.
--      
--   Save the types of any newly created serializer and deserializer
--   functions in the type environment.
--   The function definitions are not created until later.
--
--   If a new info variable was created, return the data type constructor.
setLayoutInformation :: DataType -> UnboxedTypeEvalM (Maybe Var)
setLayoutInformation dtype 
  | not $ dataTypeIsAlgebraic dtype = internalError "setLayoutInformation"
  | isJust $ dataTypeLayout dtype =
      -- Information is already set
      return Nothing
  | otherwise = do
      -- Compute the size parameters
      variance <- computeDataSizes dtype
      unless (map binderVar (dtsTyParams variance) ==
              map binderVar (dataTypeParams dtype)) $
        internalError "computeSizeParameters"

      layout <- createLayouts dtype (dtsSizeParamTypes variance) (dtsStaticTypes variance)

      -- Save layout information
      setLayout (dataTypeCon dtype) layout
      return $ Just (dataTypeCon dtype)

createLayouts dtype size_param_types static_types =
  case dataTypeKind dtype
  of BoxK  -> constructor_layouts
     BareK -> unboxed_layout
     ValK  -> unboxed_layout
  where
    -- Create one layout for each data constructor
    constructor_layouts = do
      -- Create an info constructor and field size computation code
      xs <- createConstructorTable createInfoVariable dtype
      sers <- createConstructorTable createSerializerVariable dtype
      dess <- createConstructorTable createDeserializerVariable dtype
      fs <- createConstructorTable createSizeVariable dtype
      return $ boxedDataTypeLayout size_param_types static_types xs sers dess fs

    -- Create one layout for the data type
    unboxed_layout = do
      i <- createInfoVariable (dataTypeCon dtype)
      ser <- createSerializerVariable (dataTypeCon dtype)
      des <- createDeserializerVariable (dataTypeCon dtype)
      fs <- createConstructorTable createSizeVariable dtype
      return $ unboxedDataTypeLayout size_param_types static_types i ser des fs

-- | Create a lookup table indexed by constructors.
createConstructorTable :: (Var -> UnboxedTypeEvalM a) -> DataType
                       -> UnboxedTypeEvalM [(Var, a)]
createConstructorTable f dtype =
  forM (dataTypeDataConstructors dtype) $ \c -> do
    i <- f c
    return (c, i)

-- | Create a new variable whose name consists of the given label
--   extended with some extra string.
createVariable :: String -> Maybe Label -> UnboxedTypeEvalM Var
createVariable str data_label = do
  let info_name =
        case data_label
        of Nothing -> Nothing
           Just lab -> case labelLocalName lab
                       of Left s -> let s' = s ++ str
                                    in Just (lab {labelLocalName = Left s'})
                          Right _ -> Nothing

  newVar info_name ObjectLevel

createInfoVariable = newTaggedVar TypeInfoLabel
createSizeVariable v = createVariable "_size" $ varName v
createSerializerVariable = newTaggedVar SerializerLabel
createDeserializerVariable = newTaggedVar DeserializerLabel

-------------------------------------------------------------------------------

-- | Add the types of layout-related functions to the environment for the
--   given list of data types.  It should be the list that was returned by
--   'computeDataTypeInfo'.
--   The type environment is modified in-place.
addLayoutVariablesToTypeEnvironment :: [Var] -> TypeEnv -> IO ()
addLayoutVariablesToTypeEnvironment vs tenv = do
  mapM_ add_generated_datatype vs
  mapM_ add_primitive_datatype primitiveValTypes
  where
    add_primitive_datatype v = do
      -- Look up the updated data type
      Just dtype <- runTypeEnvM tenv $ lookupDataType v

      -- Compute function types
      let info_type = infoConstructorType dtype
      insertGlobalType tenv (dataTypeUnboxedInfoVar dtype) info_type

    add_generated_datatype v = do
      -- Look up the updated data type
      Just dtype <- runTypeEnvM tenv $ lookupDataType v
          
      -- Compute function types
      let info_type = infoConstructorType dtype
          ser_type = serializerType dtype
          des_type = deserializerType dtype
          data_constructors = dataTypeDataConstructors dtype

      -- Process variables for each constructor of a boxed type
      let constructor_layouts = forM_ data_constructors $ \dcon -> do
            insertGlobalType tenv (dataTypeBoxedInfoVar dtype dcon) info_type
            insertGlobalType tenv (dataTypeBoxedSerializerVar dtype dcon) ser_type
            insertGlobalType tenv (dataTypeBoxedDeserializerVar dtype dcon) des_type

      -- Only one of each variable for a bare type
      let unboxed_layout = do
            insertGlobalType tenv (dataTypeUnboxedInfoVar dtype) info_type
            insertGlobalType tenv (dataTypeUnboxedSerializerVar dtype) ser_type
            insertGlobalType tenv (dataTypeUnboxedDeserializerVar dtype) des_type
          
      case dataTypeKind dtype of
        BoxK  -> constructor_layouts
        BareK -> unboxed_layout
        ValK  -> unboxed_layout
