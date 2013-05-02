
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module LowLevel.Cxx.Wrappers(hasCXXExports, cxxHeader)
where

import Control.Monad
import Control.Monad.State
import Control.Monad.Writer
import Data.Maybe

import qualified LowLevel.Syntax as LL
import LowLevel.Cxx.AST
import LowLevel.Cxx.Print
import Export

nameSupply :: [Name]
nameSupply = ["x" ++ show n | n <- [1..]]

-- | Add the "Triolet" namespace qualifier to a name
--
-- > Triolet::QNAME
trioletName :: QName -> QName
trioletName n = Qualified (PlainName "Triolet") n

-- | A boxed object pointer
triBoxPtrT = NameType $ trioletName $ plainQName "TriBoxPtr"

-- | A bare object pointer
triBarePtrT = NameType $ trioletName $ plainQName "TriBarePtr"

-- | Create a tuple type
tupleT :: [Type] -> Type
tupleT ts = NameType $ trioletName $ tmplQName "Tuple" ts

listT t = NameType $ trioletName $ tmplQName "List" [t]
boxedListT t = NameType $ trioletName $ tmplQName "BList" [t]

arrayT n t = NameType $ trioletName $ tmplQName ("Array" ++ show n) [t]
boxedArrayT n t = NameType $ trioletName $ tmplQName ("BArray" ++ show n) [t]

noneType = trioletName $ plainQName "NoneType"
int      = trioletName $ plainQName "Int"
float    = trioletName $ plainQName "Float"
bool     = trioletName $ plainQName "Bool"

trioletNoneTypeT = NameType noneType
trioletIntT = NameType int
trioletFloatT = NameType float
trioletBoolT = NameType bool

-------------------------------------------------------------------------------
-- Type conversions

isBareType :: ExportDataType -> Bool
isBareType (TupleET _)     = True
isBareType (ListET _ _)    = True
isBareType (ArrayET _ _ _) = True
isBareType TrioletIntET    = False
isBareType TrioletFloatET  = False
isBareType TrioletBoolET   = False
isBareType TrioletNoneET   = False

-- | Cursors are passed as a pair of pointer parameters
cursorParamTypes :: [Type]
cursorParamTypes = [triBoxPtrT, triBarePtrT]

boxedReturnType :: Maybe Type
boxedReturnType = Just triBoxPtrT

-- | Determine the C type of a wrapped function parameter.
--   This is the type of arguments to wrapper functions.
wrappedParamType :: ExportDataType -> Type
wrappedParamType (TupleET ts)         = tupleT $ map wrappedParamType ts
wrappedParamType (ListET False ts)    = listT $ wrappedParamType ts
wrappedParamType (ListET True ts)     = boxedListT $ wrappedParamType ts
wrappedParamType (ArrayET n False ts) = arrayT n $ wrappedParamType ts
wrappedParamType (ArrayET n True ts)  = arrayT n $ wrappedParamType ts
wrappedParamType TrioletIntET         = trioletIntT
wrappedParamType TrioletFloatET       = trioletFloatT
wrappedParamType TrioletBoolET        = trioletBoolT
wrappedParamType TrioletNoneET        = trioletNoneTypeT

-- | Determine the C types of an unwrapped function parameter.
--   Some parameters become more than one type.
unwrappedParamType :: ExportDataType -> [Type]
unwrappedParamType t | isBareType t = cursorParamTypes
unwrappedParamType TrioletIntET    = [int32_tT]
unwrappedParamType TrioletFloatET  = [floatT]
unwrappedParamType TrioletBoolET   = [boolT]
unwrappedParamType TrioletNoneET   = []

-- | Convert a signature's type to a wrapper function's return type.
--   The conversion is the same as it is for parameter types.
wrappedReturnType :: ExportDataType -> Type
wrappedReturnType t = wrappedParamType t

-- | Determine the C type of an unwrapped function's return value.
unwrappedReturnType :: ExportDataType -> Maybe Type
unwrappedReturnType t | isBareType t = boxedReturnType
unwrappedReturnType TrioletIntET    = Just int32_tT
unwrappedReturnType TrioletFloatET  = Just floatT
unwrappedReturnType TrioletBoolET   = Just boolT
unwrappedReturnType TrioletNoneET   = Nothing

-------------------------------------------------------------------------------
-- Code generation

newtype Gen a = Gen (State [Name] a) deriving(Monad)

runGen :: Gen a -> a
runGen (Gen m) = evalState m nameSupply

-- | Create a new variable name
newName :: Gen Name
newName = Gen $ do
  (x:xs) <- get
  put xs
  return x

-- | Generate code and create statements in a function body
type GenSuite a = WriterT Suite Gen a

generateSuite :: GenSuite a -> Gen (a, Suite)
generateSuite = runWriterT

-- | Create a new variable declaration.  Return the statement and variable.
defineNewVariable :: Type -> Expression -> GenSuite Var
defineNewVariable ty e = do
  name <- lift newName
  tell [DeclStmt (Decl [] name ty) (Just e)]
  return $ plainQName name

-- | Generate code to unwrap a parameter.  Return the generated statements
--   and the unwrapped values.  The unwrapped values will be passed to the
--   callee.
unwrapParameter :: ExportDataType -> Var -> GenSuite [Expression]
unwrapParameter export_type param_var
  | isBareType export_type =
      -- Get the values by calling 'getBareData' and 'getParent'
      let parent_ref = callMemberExpr param_expr "getParent" []
          object_ref = callMemberExpr param_expr "getBareData" []
      in return [parent_ref, object_ref]

  | TrioletNoneET <- export_type =
      -- No parameters
      return []

  | otherwise =
      -- Cast to the desired type
      let [t] = unwrappedParamType export_type
      in return [CastExpr t param_expr]
  where
    param_expr = IdentExpr param_var

-- | Create an expression that constructs the appropriate return value for
--   this type.  Parameter 'result_var' holds the wrapped function's
--   return value.
wrapReturn :: ExportDataType -> Maybe Var -> GenSuite Expression
wrapReturn export_type m_result_var
  | isBareType export_type =
      -- Call 'unboxBareObject<T>(x)'
      let wrapper_type = wrappedReturnType export_type
          Just result_var = m_result_var
          op = IdentExpr $ trioletName $
               tmplQName "unboxBareObject" [wrapper_type]
      in return $ CallExpr op [IdentExpr result_var]

  | otherwise =
      case export_type
      of TrioletIntET -> construct int
         TrioletFloatET -> construct float
         TrioletBoolET -> construct bool

         -- Construct a new NoneType
         TrioletNoneET -> return $ CallExpr (IdentExpr noneType) []
  where
    -- Construct a new object, of type 'type_name'
    construct type_name =
      let Just result_var = m_result_var
      in return $ callVarExpr type_name [IdentExpr result_var]
      
-- | Create a declaration of the Triolet function
wrappedFunctionDeclaration :: CXXSignature -> String -> Gen Decl
wrappedFunctionDeclaration (CXXSignature _ param_types return_type) name =
  let wrapped_param_types = concatMap unwrappedParamType param_types
      wrapped_return_type = fromMaybe voidT $ unwrappedReturnType return_type
      fun_type = FunType wrapped_param_types wrapped_return_type
  in return $ Decl [ExternCQual] name fun_type

-- | Create a wrapper function that calls the the Triolet function
wrapperDefinition :: CXXSignature -> String -> Gen FunDef
wrapperDefinition (CXXSignature wrapper_name param_types return_type) wrapped_name = do
  -- Create a variable for each parameter
  param_names <- replicateM (length param_types) newName
  let param_decls = [Decl [] n (wrappedParamType t)
                    | (n, t) <- zip param_names param_types]
      params = map plainQName param_names

  -- Create function body
  ((), body) <- generateSuite $ create_body params

  -- Create the function
  return $ FunDef [] (wrappedReturnType return_type) wrapper_name param_decls body
  where
    -- Create the function body, given parameters whose names are 'param_names'
    create_body params = do
      -- Unwrap parameters
      unwrapped_params <-
        liftM concat $ zipWithM unwrapParameter param_types params

      -- Call the wrapped function.  If it returns a value, 
      -- write its result to a new variable.
      let call_expr = callVarExpr (plainQName wrapped_name) unwrapped_params
      unwrapped_result <-
        case unwrappedReturnType return_type of
          Just t  -> liftM Just $ defineNewVariable t call_expr
          Nothing -> tell [ExprStmt call_expr] >> return Nothing

      -- Create the return expression
      return_expr <- wrapReturn return_type unwrapped_result
      tell [ReturnStmt return_expr]

exportedFunctionWrappers :: (LL.Var, CXXSignature) -> Gen (Decl, FunDef)
exportedFunctionWrappers (wrapped_var, sig) = do
  -- Get the name of the Triolet function that the wrapper will call
  let mangled_name = LL.mangledVarName False wrapped_var
  decl <- wrappedFunctionDeclaration sig mangled_name
  def <- wrapperDefinition sig mangled_name
  return (decl, def)

-- | Get the module's exported C++ functions
cxxExports :: LL.Module -> [(LL.Var, CXXSignature)]
cxxExports m = [(v, s) | (v, CXXExportSig s) <- LL.moduleExports m]

hasCXXExports :: LL.Module -> Bool
hasCXXExports m = not $ null $ cxxExports m

-- | Create the text of a C++ header file for a module
cxxHeader :: LL.Module -> String
cxxHeader mod =
  let header_file = runGen $ do
        (decls, defs) <- liftM unzip $
                         mapM exportedFunctionWrappers $ cxxExports mod
        return $ HeaderFile decls defs
  in prettyPrintHeaderFile header_file