
module SystemF.Datatypes.Driver(computeDataTypeInfo)
where

import Control.Monad
import Control.Monad.Trans
import qualified Data.IntMap as IntMap
import Data.Maybe
  
import Common.Error
import Common.Identifier
import Common.Label
import Common.Supply
import Common.MonadLogic
import Type.Type
import Type.Environment
import Type.Compare
import Type.Eval
import SystemF.Syntax
import SystemF.MemoryIR

import SystemF.Datatypes.Structure
import SystemF.Datatypes.TypeObject

-- | Compute layout information for all algebraic data types in the
--   given environment.  The type environment is modified in-place
--   by adding size parameter types and type info variables.
--   A list of type info definitions is returned.
computeDataTypeInfo :: IdentSupply Var
                    -> TypeEnv
                    -> IO [GDef Mem]
computeDataTypeInfo var_supply type_env =
  runTypeEvalM compute var_supply type_env
  where
    compute = do
      -- Create layout information for each algebraic data type
      -- and update the type environment
      m_dtypes_needing_info <-
        mapM setLayoutInformation =<< get_algebraic_data_types
      let dtypes_needing_info = catMaybes m_dtypes_needing_info

      -- Create and return definitions of the info variables
      defss <- assume_info_vars dtypes_needing_info $
        mapM define_info_var dtypes_needing_info
      return $ concat defss

    -- Create definitions for the info variables
    define_info_var :: Var -> UnboxedTypeEvalM [GDef Mem]
    define_info_var data_type_con = do
      Just dtype <- lookupDataType data_type_con
      case dataTypeKind dtype of
        ValK  -> return `liftM` valInfoDefinition dtype
        BareK -> return `liftM` bareInfoDefinition dtype
        BoxK  -> boxInfoDefinitions dtype

    -- Given a list of data type constructors, add all their info variables
    -- to the environment
    assume_info_vars :: [Var] -> UnboxedTypeEvalM a -> UnboxedTypeEvalM a
    assume_info_vars data_type_cons m = do
      dtypes <- mapM lookupDataType data_type_cons

      -- For each data type, for each info variable, create a binding
      let bindings :: [Binder]
          bindings = [ v ::: dataTypeInfoType dtype
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
      xs <- forM (dataTypeDataConstructors dtype) $ \c -> do
        i <- createInfoVariable $ varName c
        return (c, i)
      return $ boxedDataTypeLayout size_param_types static_types xs

    -- Create one layout for the data type
    unboxed_layout = do
      i <- createInfoVariable (varName $ dataTypeCon dtype)
      return $ unboxedDataTypeLayout size_param_types static_types i

-- | Create an info variable for this data type, if it doesn't already have
--   one.  Save it in the type environment.
--   If a variable was created, return the data constructor's name.
createInfoVariable :: Maybe Label -> UnboxedTypeEvalM Var
createInfoVariable data_label = do
  -- Name the variable by appending "_info" to the data type constructor name
  let info_name =
        case data_label
        of Nothing -> Nothing
           Just lab -> case labelLocalName lab
                       of Left s -> let s' = s ++ "_info"
                                    in Just (lab {labelLocalName = Left s'})
                          Right _ -> Nothing

  newVar info_name ObjectLevel
