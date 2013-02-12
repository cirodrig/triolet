{-| Marshaling of function parameters and return values in code that 
is exported to C.
-}

module SystemF.Lowering.Marshaling(createCMarshalingFunction,
                                   createCxxMarshalingFunction,
                                   getCExportSig,
                                   getCxxExportSig)
where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import Debug.Trace

import Common.Error
import Builtins.Builtins
import qualified LowLevel.CodeTypes as LL
import qualified LowLevel.Syntax as LL
import qualified LowLevel.Builtins as LL
import LowLevel.Build
import LowLevel.Records
import SystemF.Lowering.LowerMonad
import Type.Environment
import Type.Eval
import Type.Type
import Export

pyonType :: ExportDataType -> Type
pyonType (ListET False ty) = varApp (coreBuiltin The_list) [pyonType ty]
pyonType (ListET True ty) = varApp (coreBuiltin The_blist) [pyonType ty]
pyonType (ArrayET n False ty) =
  let op = case n
           of 0 -> coreBuiltin The_array0
              1 -> coreBuiltin The_array1
              2 -> coreBuiltin The_array2
              3 -> coreBuiltin The_array3
  in varApp op [pyonType ty]
pyonType TrioletNoneET = VarT (coreBuiltin The_NoneType)
pyonType TrioletIntET = intT
pyonType TrioletFloatET = floatT
pyonType TrioletBoolET = VarT (coreBuiltin The_bool)

-- | Construct a representation dictionary for a marshalable type.
--   For types with an unknown head, 'lookupReprDict' is called.  Known types
--   are handled by case.
computeReprDict :: Type -> GenLower LL.Val
computeReprDict ty =
  case fromVarApp ty
  of Just (op, args)
       | op `isCoreBuiltin` The_list ->
           return $ LL.VarV $ LL.llBuiltin LL.the_bivar_repr_list
       | op `isCoreBuiltin` The_array0 ->
           return $ LL.VarV $ LL.llBuiltin LL.the_bivar_repr_array0
       | op `isCoreBuiltin` The_array1 ->
           return $ LL.VarV $ LL.llBuiltin LL.the_bivar_repr_array1
       | op `isCoreBuiltin` The_array2 ->
           return $ LL.VarV $ LL.llBuiltin LL.the_bivar_repr_array2
       | op `isCoreBuiltin` The_array3 ->
           return $ LL.VarV $ LL.llBuiltin LL.the_bivar_repr_array3
       | op `isCoreBuiltin` The_Tuple2 ->
           polymorphic_repr 2 args (LL.llBuiltin LL.the_fun_repr_Tuple2)
       | op `isCoreBuiltin` The_Tuple3 ->
           polymorphic_repr 3 args (LL.llBuiltin LL.the_fun_repr_Tuple3)
       | op `isCoreBuiltin` The_Tuple4 ->
           polymorphic_repr 4 args (LL.llBuiltin LL.the_fun_repr_Tuple4)
       | op == intV ->
           return $ LL.VarV $ LL.llBuiltin LL.the_bivar_repr_int
       | op == floatV ->
           return $ LL.VarV $ LL.llBuiltin LL.the_bivar_repr_float
       | op `isCoreBuiltin` The_bool ->
           return $ LL.VarV $ LL.llBuiltin LL.the_bivar_repr_bool
       | otherwise -> lookupReprDict ty return
  where
    owned_type = LL.PrimType LL.OwnedType

    -- Create a polymorphic representation dictionary.  Use all type arguments'
    -- representations as parameters.
    polymorphic_repr n args dict_op = do
      when (length args /= n) $
        internalError "computeReprDict: Wrong number of type parameters"
      dicts <- mapM computeReprDict args
      emitAtom1 owned_type $ LL.closureCallA (LL.VarV dict_op) dicts

-------------------------------------------------------------------------------
-- Parameter marshaling

-- | Code for marshaling one function parameter
data ParameterMarshaler =
  ParameterMarshaler
  { -- | The parameter variables of the wrapper function
    pmInputs :: [LL.Var]
    -- | Code that takes the inputs and produces the output value
  , pmCode :: GenLower ()
    -- | The parameter values 
  , pmOutput :: LL.Val
  }

combineParameterMarshalers :: [ParameterMarshaler]
                           -> ([LL.Var], GenLower (), [LL.Val])
combineParameterMarshalers pms =
  (concatMap pmInputs pms,
   sequence_ $ map pmCode pms,
   map pmOutput pms)

-- | Marshal a function parameter that was passed from C.  The converted
--   parameter will be passed to a pyon function.
marshalCParameter :: ExportDataType -> Lower ParameterMarshaler
marshalCParameter ty =
  case ty
  of ListET _ _ -> passParameterWithType (LL.PrimType LL.PointerType)
     ArrayET _ _ _ -> passParameterWithType (LL.PrimType LL.PointerType)
     TrioletNoneET -> passParameterWithType (LL.PrimType LL.UnitType)
     TrioletIntET -> passParameterWithType (LL.PrimType LL.trioletIntType)
     TrioletFloatET -> passParameterWithType (LL.PrimType LL.trioletFloatType)
     TrioletBoolET -> passParameterWithType (LL.PrimType LL.trioletBoolType)
     FunctionET args ret -> marshalParameterFunctionFromC args ret
  where
    complex_float_type = complexRecord (LL.PrimField LL.trioletFloatType)

-- | Marshal a function parameter that was passed from pyon.  The converted
--   parameter will be passed to a C function.
demarshalCParameter :: ExportDataType -> Lower ParameterMarshaler
demarshalCParameter ty =
  case ty
  of ListET _ _ -> passParameterWithType (LL.PrimType LL.PointerType)
     ArrayET _ _ _ -> passParameterWithType (LL.PrimType LL.PointerType)
     TrioletNoneET -> passParameterWithType (LL.PrimType LL.UnitType)
     TrioletIntET -> passParameterWithType (LL.PrimType LL.trioletIntType)
     TrioletFloatET -> passParameterWithType (LL.PrimType LL.trioletFloatType)
     TrioletBoolET -> passParameterWithType (LL.PrimType LL.trioletBoolType)
     FunctionET args ret -> marshalParameterFunctionToC args ret

-- | Marshal a function parameter that was passed from C++.  The converted
--   parameter will be passed to a pyon function.
marshalCxxParameter :: ExportDataType -> Lower ParameterMarshaler
marshalCxxParameter ty =
  case ty
  of TrioletNoneET -> passParameterWithType (LL.PrimType LL.UnitType)
     TrioletIntET -> passParameterWithType (LL.PrimType LL.trioletIntType)
     TrioletFloatET -> passParameterWithType (LL.PrimType LL.trioletFloatType)
     TrioletBoolET -> passParameterWithType (LL.PrimType LL.trioletBoolType)
     ListET _ _ -> passParameterWithType (LL.PrimType LL.PointerType)
     ArrayET _ _ _ -> passParameterWithType (LL.PrimType LL.PointerType)
     TupleET _ -> passParameterWithType (LL.PrimType LL.PointerType)

-- | Pass a parameter as a single variable.
passParameterWithType :: LL.ValueType -> Lower ParameterMarshaler
passParameterWithType t = do
  v <- LL.newAnonymousVar t
  return $ ParameterMarshaler { pmInputs = [v]
                              , pmCode = return ()
                              , pmOutput = LL.VarV v}

-- | Marshal a function parameter that holds a function from C to pyon.
--
--   The marshaling code creates a wrapper function is created that
--   takes pyon parameters, converts them to C, calls the C function,
--   converts its return value to Triolet, and returns it.

marshalParameterFunctionFromC :: [ExportDataType]
                              -> ExportDataType
                              -> Lower ParameterMarshaler
marshalParameterFunctionFromC params ret = do
  -- The parameter from C
  closure_ptr <- LL.newAnonymousVar (LL.RecordType cClosureRecord)
  -- Triolet function
  pyon_ptr <- LL.newAnonymousVar (LL.PrimType LL.OwnedType)

  -- Parameters are passed from pyon to C; returns are passed from C to pyon
  marshal_params <- mapM demarshalCParameter params
  marshal_return <- demarshalCReturn ret
  
  -- The code generator creates a local function
  let return_types = map LL.varType $ rmReturns marshal_return
      (param_inputs, param_code, param_arguments) =
        combineParameterMarshalers marshal_params

      code = do
        -- Unpack the parameter
        [fun_ptr, cap_ptr] <- unpackRecord cClosureRecord (LL.VarV closure_ptr)
        
        -- Define a local function
        f_body <- lift $ execBuild return_types $ do
          param_code
          rmCode marshal_return $ do
            let call_args = LL.VarV cap_ptr : param_arguments ++ rmOutput marshal_return
            return $ LL.primCallA (LL.VarV fun_ptr) call_args
          return $ LL.ReturnE $ LL.ValA (map LL.VarV $ rmReturns marshal_return)
        let f = LL.closureFun (param_inputs ++ rmInputs marshal_return) return_types f_body

        emitLetrec (LL.NonRec (LL.Def pyon_ptr f))
  
  return $ ParameterMarshaler { pmInputs = [closure_ptr]
                              , pmCode = code
                              , pmOutput = LL.VarV pyon_ptr}

marshalParameterFunctionToC :: [ExportDataType]
                            -> ExportDataType
                            -> Lower ParameterMarshaler
marshalParameterFunctionToC params ret =
  internalError "marshalParameterFunctionToC: Not implemented"

-------------------------------------------------------------------------------
-- Return marshaling

data ReturnMarshaler =
  ReturnMarshaler
  { -- | The parameter variables of the wrapper function; used for example
    --   when the return value is written into a pointer passed by the caller
    rmInputs :: [LL.Var]
    -- | A wrapper generator that takes the function call code and produces
    --   the output value
  , rmCode :: GenLower LL.Atom -> GenLower ()
    -- | Parameters to pass to the callee
  , rmOutput :: [LL.Val]
    -- | Return variables to return in the wrapper
  , rmReturns :: [LL.Var]}

-- | Marshal a return value to C code.
--
-- Returns a list of parameters to the exported function,
-- a code generator that wraps the real function call,
-- a list of argument values to pass to the Triolet function, 
-- and a list of return variables to return from the wrapper function.
marshalCReturn :: ExportDataType -> Lower ReturnMarshaler
marshalCReturn ty =
  case ty
  of TrioletNoneET -> passReturnWithType (LL.PrimType LL.UnitType)
     TrioletIntET -> passReturnWithType (LL.PrimType LL.trioletIntType)
     TrioletFloatET -> passReturnWithType (LL.PrimType LL.trioletFloatType)
     TrioletBoolET -> passReturnWithType (LL.PrimType LL.trioletBoolType)

-- | Marshal a return value to C++ code.
--
-- Returns a list of parameters to the exported function,
-- a code generator that wraps the real function call,
-- a list of argument values to pass to the Triolet function, 
-- and a list of return variables to return from the wrapper function.
marshalCxxReturn :: ExportDataType -> Lower ReturnMarshaler
marshalCxxReturn ty =
  case ty
  of TrioletNoneET -> passReturnWithType (LL.PrimType LL.UnitType)
     TrioletIntET -> passReturnWithType (LL.PrimType LL.trioletIntType)
     TrioletFloatET -> passReturnWithType (LL.PrimType LL.trioletFloatType)
     TrioletBoolET -> passReturnWithType (LL.PrimType LL.trioletBoolType)
     ListET _ _ -> passReturnBoxed
     ArrayET _ _ _ -> passReturnBoxed
     TupleET _ -> passReturnBoxed

demarshalCReturn :: ExportDataType -> Lower ReturnMarshaler
demarshalCReturn ty =
  case ty
  of TrioletNoneET -> passReturnWithType (LL.PrimType LL.UnitType)
     TrioletIntET -> passReturnWithType (LL.PrimType LL.trioletIntType)
     TrioletFloatET -> passReturnWithType (LL.PrimType LL.trioletFloatType)
     TrioletBoolET -> passReturnWithType (LL.PrimType LL.trioletBoolType)

-- Just return a primitive value
passReturnWithType pt = do
  v <- LL.newAnonymousVar pt
  let setup mk_real_call = bindAtom1 v =<< mk_real_call
  return $ ReturnMarshaler { rmInputs = []
                           , rmCode = setup
                           , rmOutput = []
                           , rmReturns = [v]}

-- | Return by initializing an object that's passed as a parameter 
passReturnParameter = do
  v <- LL.newAnonymousVar (LL.PrimType LL.PointerType)
  return $ ReturnMarshaler { rmInputs = [v]
                           , rmCode = \g -> g >>= emitAtom0
                           , rmOutput = [LL.VarV v]
                           , rmReturns = []}

-- | Return a boxed object
passReturnBoxed = do
  v <- LL.newAnonymousVar (LL.PrimType LL.OwnedType)
  return $ ReturnMarshaler { rmInputs = []
                           , rmCode = \g -> g >>= bindAtom1 v
                           , rmOutput = []
                           , rmReturns = [v]}

-- | Wrap the lowered function 'f' in marshaling code for C.  Produce a
-- primitive function.
createCMarshalingFunction :: CSignature -> LL.Fun -> Lower LL.Fun
createCMarshalingFunction (CSignature dom rng) f = do
  -- Generate marshaling code
  marshal_params <- mapM marshalCParameter dom
  marshal_return <- marshalCReturn rng
  createMarshalingFunction marshal_params marshal_return f

-- | Wrap the lowered function 'f' in marshaling code for C++.  Produce a
-- primitive function.
createCxxMarshalingFunction :: CXXSignature -> LL.Fun -> Lower LL.Fun
createCxxMarshalingFunction (CXXSignature _ dom rng) f = do
  -- Generate marshaling code
  marshal_params <- mapM marshalCxxParameter dom
  marshal_return <- marshalCxxReturn rng
  createMarshalingFunction marshal_params marshal_return f

createMarshalingFunction marshal_params marshal_return f = do
  -- Create the function
  let return_types = map LL.varType $ rmReturns marshal_return
      return_inputs = rmInputs marshal_return
      (param_inputs, param_code, param_arguments) =
        combineParameterMarshalers marshal_params

  fun_body <- execBuild return_types $ do
    param_code                  -- Marshal the parameters
    
    -- Call the function and marshal the return value
    let call_arguments = param_arguments ++ rmOutput marshal_return
    rmCode marshal_return $ do
      f_var <- emitLambda f
      return $ LL.closureCallA (LL.VarV f_var) call_arguments
    
    -- Return the return value
    return $ LL.ReturnE $ LL.ValA (map LL.VarV $ rmReturns marshal_return)

  return $ LL.primFun (param_inputs ++ return_inputs) return_types fun_body

-------------------------------------------------------------------------------
-- Exported types

-- | Given a memory function type signature, determine the type of the
--   function that's exported to C.
--
--   All elements of the type are assumed to be in their natural 
--   representation.  Code that looks at 'ExportSig's assumes this and
--   may break otherwise.
getCExportSig :: Type -> UnboxedTypeEvalM CSignature
getCExportSig ty = do
  (param_types, return_type) <- getExportedFunctionSignature getCExportType ty
  return $ CSignature param_types return_type

-- | Given a memory function type signature, determine the type of the
--   function that's exported to C++.
--
--   All elements of the type are assumed to be in their natural 
--   representation.  Code that looks at 'ExportSig's assumes this and
--   may break otherwise.
getCxxExportSig :: String -> Type -> UnboxedTypeEvalM CXXSignature
getCxxExportSig exported_name ty = do
  (param_types, return_type) <- getExportedFunctionSignature getCxxExportType ty
  return $ CXXSignature exported_name param_types return_type

-- | Determine the exported parameter and return types of some
--   function type, using the given type conversion function to
--   convert each parameter and return type.
getExportedFunctionSignature :: (Type -> UnboxedTypeEvalM ExportDataType)
                             -> Type
                             -> UnboxedTypeEvalM ([ExportDataType], ExportDataType)
getExportedFunctionSignature convert_type ty = do
  (param_types, return_type) <- deconFunctionType ty
  export_param_types <- mapM convert_type param_types
  export_return_type <- convert_type return_type
  return (export_param_types, export_return_type)

getCExportType :: Type -> UnboxedTypeEvalM ExportDataType
getCExportType ty = do
  decon_ty <- deconVarAppType ty
  case decon_ty of
    Just (con, [])
      | con `isCoreBuiltin` The_NoneType -> return TrioletNoneET
      | con == intV -> return TrioletIntET
      | con == floatV -> return TrioletFloatET
      | con `isCoreBuiltin` The_bool -> return TrioletBoolET
    Just (con, [arg])
      -- Look through 'Stored' and 'Boxed' constructors
      | con `isCoreBuiltin` The_Stored -> getCExportType arg
      | con `isCoreBuiltin` The_Boxed -> getCExportType arg
      | con `isCoreBuiltin` The_list ->
          ListET False <$> getCExportType arg
      | con `isCoreBuiltin` The_array2 ->
          ArrayET 2 False <$> getCExportType arg
    _ -> unsupported
  where
    unsupported = internalError "getCExportType: Unsupported exported type"
                                        
getCxxExportType :: Type -> UnboxedTypeEvalM ExportDataType
getCxxExportType ty = do
  decon_ty <- deconVarAppType ty
  case decon_ty of
    Just (con, [])
      | con `isCoreBuiltin` The_NoneType -> return TrioletNoneET
      | con == intV -> return TrioletIntET
      | con == floatV -> return TrioletFloatET
      | con `isCoreBuiltin` The_bool -> return TrioletBoolET
    Just (con, [arg])
      -- Look through 'Stored' and 'Boxed' constructors
      | con `isCoreBuiltin` The_Stored -> getCxxExportType arg
      | con `isCoreBuiltin` The_Boxed -> getCxxExportType arg
       
      | con `isCoreBuiltin` The_list ->
           unary (ListET False) arg
      | con `isCoreBuiltin` The_array0 ->
          unary (ArrayET 0 False) arg
      | con `isCoreBuiltin` The_array1 ->
          unary (ArrayET 1 False) arg
      | con `isCoreBuiltin` The_array2 ->
          unary (ArrayET 2 False) arg
      | con `isCoreBuiltin` The_array3 ->
          unary (ArrayET 3 False) arg
      | con `isCoreBuiltin` The_blist ->
          unary (ListET True) arg
      | con `isCoreBuiltin` The_barray1 ->
          unary (ArrayET 1 True) arg
      | con `isCoreBuiltin` The_barray2 ->
          unary (ArrayET 2 True) arg
      | con `isCoreBuiltin` The_barray3 ->
          unary (ArrayET 3 True) arg
    Just (con, args)
      | con `isCoreBuiltin` The_Tuple2 ->
          if length args /= 2
          then type_error
          else TupleET <$> mapM getCxxExportType args
      | con `isCoreBuiltin` The_Tuple3 ->
          if length args /= 3
          then type_error
          else TupleET <$> mapM getCxxExportType args
      | con `isCoreBuiltin` The_Tuple4 ->
          if length args /= 4
          then type_error
          else TupleET <$> mapM getCxxExportType args
    _ -> unsupported
  where
    unary con arg = con <$> getCxxExportType arg
    unsupported = internalError "getCxxExportType: Unsupported exported type"

    type_error = internalError "getCxxExportType: Type error detected"
                                        
  