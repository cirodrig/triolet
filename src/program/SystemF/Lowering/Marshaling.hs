{-| Marshaling of function parameters and return values in code that 
is exported to C.
-}

module SystemF.Lowering.Marshaling(createCMarshalingFunction,
                                   createCxxMarshalingFunction,
                                   getCExportSig,
                                   getCxxExportSig)
where

import Control.Monad
import Control.Monad.Trans
import Data.Maybe

import Common.Error
import Builtins.Builtins
import qualified LowLevel.CodeTypes as LL
import qualified LowLevel.Syntax as LL
import qualified LowLevel.Builtins as LL
import LowLevel.Build
import LowLevel.Records
import SystemF.Syntax
import SystemF.MemoryIR
import SystemF.Lowering.LowerMonad
import Type.Environment
import Type.Eval
import Type.Type
import Export

pyonType :: ExportDataType -> Type
pyonType (ListET False ty) = varApp (pyonBuiltin The_list) [pyonType ty]
pyonType (ListET True ty) = varApp (pyonBuiltin The_blist) [pyonType ty]
pyonType (ArrayET n False ty) =
  let op = case n
           of 0 -> pyonBuiltin The_array0
              1 -> pyonBuiltin The_array1
              2 -> pyonBuiltin The_array2
              3 -> pyonBuiltin The_array3
  in varApp op [pyonType ty]
pyonType PyonNoneET = VarT (pyonBuiltin The_NoneType)
pyonType PyonIntET = VarT (pyonBuiltin The_int)
pyonType PyonFloatET = VarT (pyonBuiltin The_float)
pyonType PyonBoolET = VarT (pyonBuiltin The_bool)

-- | Construct a representation dictionary for a marshalable type.
--   For types with an unknown head, 'lookupReprDict' is called.  Known types
--   are handled by case.
computeReprDict :: Type -> GenLower LL.Val
computeReprDict ty =
  case fromVarApp ty
  of Just (op, args)
       | op `isPyonBuiltin` The_list ->
           polymorphic_repr 1 args (LL.llBuiltin LL.the_fun_repr_list)
       | op `isPyonBuiltin` The_array0 ->
           polymorphic_repr 1 args (LL.llBuiltin LL.the_fun_repr_array0)
       | op `isPyonBuiltin` The_array1 ->
           polymorphic_repr 1 args (LL.llBuiltin LL.the_fun_repr_array1)
       | op `isPyonBuiltin` The_array2 ->
           polymorphic_repr 1 args (LL.llBuiltin LL.the_fun_repr_array2)
       | op `isPyonBuiltin` The_array3 ->
           polymorphic_repr 1 args (LL.llBuiltin LL.the_fun_repr_array3)
       | op `isPyonBuiltin` The_PyonTuple2 ->
           polymorphic_repr 2 args (LL.llBuiltin LL.the_fun_repr_PyonTuple2)
       | op `isPyonBuiltin` The_PyonTuple3 ->
           polymorphic_repr 3 args (LL.llBuiltin LL.the_fun_repr_PyonTuple3)
       | op `isPyonBuiltin` The_PyonTuple4 ->
           polymorphic_repr 4 args (LL.llBuiltin LL.the_fun_repr_PyonTuple4)
       | op `isPyonBuiltin` The_int ->
           return $ LL.VarV $ LL.llBuiltin LL.the_bivar_repr_int
       | op `isPyonBuiltin` The_float ->
           return $ LL.VarV $ LL.llBuiltin LL.the_bivar_repr_float
       | op `isPyonBuiltin` The_bool ->
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
     PyonNoneET -> passParameterWithType (LL.PrimType LL.UnitType)
     PyonIntET -> passParameterWithType (LL.PrimType LL.pyonIntType)
     PyonFloatET -> passParameterWithType (LL.PrimType LL.pyonFloatType)
     PyonBoolET -> passParameterWithType (LL.PrimType LL.pyonBoolType)
     FunctionET args ret -> marshalParameterFunctionFromC args ret
  where
    complex_float_type = complexRecord (LL.PrimField LL.pyonFloatType)

-- | Marshal a function parameter that was passed from pyon.  The converted
--   parameter will be passed to a C function.
demarshalCParameter :: ExportDataType -> Lower ParameterMarshaler
demarshalCParameter ty =
  case ty
  of ListET _ _ -> passParameterWithType (LL.PrimType LL.PointerType)
     ArrayET _ _ _ -> passParameterWithType (LL.PrimType LL.PointerType)
     PyonNoneET -> passParameterWithType (LL.PrimType LL.UnitType)
     PyonIntET -> passParameterWithType (LL.PrimType LL.pyonIntType)
     PyonFloatET -> passParameterWithType (LL.PrimType LL.pyonFloatType)
     PyonBoolET -> passParameterWithType (LL.PrimType LL.pyonBoolType)
     FunctionET args ret -> marshalParameterFunctionToC args ret

-- | Marshal a function parameter that was passed from C++.  The converted
--   parameter will be passed to a pyon function.
marshalCxxParameter :: ExportDataType -> Lower ParameterMarshaler
marshalCxxParameter ty =
  case ty
  of PyonNoneET -> passParameterWithType (LL.PrimType LL.UnitType)
     PyonIntET -> passParameterWithType (LL.PrimType LL.pyonIntType)
     PyonFloatET -> passParameterWithType (LL.PrimType LL.pyonFloatType)
     PyonBoolET -> passParameterWithType (LL.PrimType LL.pyonBoolType)
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
--   converts its return value to Pyon, and returns it.

marshalParameterFunctionFromC :: [ExportDataType]
                              -> ExportDataType
                              -> Lower ParameterMarshaler
marshalParameterFunctionFromC params ret = do
  -- The parameter from C
  closure_ptr <- LL.newAnonymousVar (LL.RecordType cClosureRecord)
  -- Pyon function
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
-- a list of argument values to pass to the Pyon function, 
-- and a list of return variables to return from the wrapper function.
marshalCReturn :: ExportDataType -> Lower ReturnMarshaler
marshalCReturn ty =
  case ty
  of ListET _ _ -> return_new_reference (LL.RecordType listRecord)
     ArrayET 2 False _ -> return_new_reference (LL.RecordType matrixRecord)
     PyonNoneET -> passReturnWithType (LL.PrimType LL.UnitType)
     PyonIntET -> passReturnWithType (LL.PrimType LL.pyonIntType)
     PyonFloatET -> passReturnWithType (LL.PrimType LL.pyonFloatType)
     PyonBoolET -> passReturnWithType (LL.PrimType LL.pyonBoolType)
  where
    complex_float_type = complexRecord (LL.PrimField LL.pyonFloatType)

    -- Allocate and return a new object.  The allocated object is passed
    -- as a parameter to the function.
    return_new_reference t = do
      v <- LL.newAnonymousVar (LL.PrimType LL.PointerType)
      
      let setup mk_real_call = do
            -- Allocate the return value
            allocateHeapMemAs (nativeWordV $ LL.sizeOf t) (boolV $ LL.pointerlessness t) v
            
            -- Call the function, which returns nothing
            emitAtom0 =<< mk_real_call

      return $ ReturnMarshaler { rmInputs = []
                               , rmCode = setup
                               , rmOutput = [LL.VarV v] 
                               , rmReturns = [v]}

-- | Marshal a return value to C++ code.
--
-- Returns a list of parameters to the exported function,
-- a code generator that wraps the real function call,
-- a list of argument values to pass to the Pyon function, 
-- and a list of return variables to return from the wrapper function.
marshalCxxReturn :: ExportDataType -> Lower ReturnMarshaler
marshalCxxReturn ty =
  case ty
  of PyonNoneET -> passReturnWithType (LL.PrimType LL.UnitType)
     PyonIntET -> passReturnWithType (LL.PrimType LL.pyonIntType)
     PyonFloatET -> passReturnWithType (LL.PrimType LL.pyonFloatType)
     PyonBoolET -> passReturnWithType (LL.PrimType LL.pyonBoolType)
     ListET _ _ -> passReturnParameter
     ArrayET _ _ _ -> passReturnParameter
     TupleET _ -> passReturnParameter

demarshalCReturn :: ExportDataType -> Lower ReturnMarshaler
demarshalCReturn ty =
  case ty
  of ListET False element_type ->
       let list_type = varApp (pyonBuiltin The_list) [pyonType element_type]
       in demarshal_reference list_type
     ArrayET 2 False element_type ->
       let mat_type = varApp (pyonBuiltin The_array2) [pyonType element_type]
       in demarshal_reference mat_type
     PyonNoneET -> passReturnWithType (LL.PrimType LL.UnitType)
     PyonIntET -> passReturnWithType (LL.PrimType LL.pyonIntType)
     PyonFloatET -> passReturnWithType (LL.PrimType LL.pyonFloatType)
     PyonBoolET -> passReturnWithType (LL.PrimType LL.pyonBoolType)
  where
    complex_float_type = complexRecord (LL.PrimField LL.pyonFloatType)
    demarshal_reference ref_type = do
      -- An uninitialized pyon object pointer is passed as a parameter to 
      -- the marshaling function.  The C function returns a reference to an
      -- object.  Copy the returned data into the destination function and
      -- free the data.
      pyon_ref <- LL.newAnonymousVar (LL.PrimType LL.PointerType)

      let setup mk_call = do
            ret_val <- emitAtom1 (LL.PrimType LL.PointerType) =<< mk_call
            dict <- computeReprDict ref_type

            -- Copy to output
            copy_fun <- selectPassConvCopy dict
            emitAtom0 $ LL.closureCallA copy_fun [ret_val, LL.VarV pyon_ref]
              
            -- Deallocate
            free_fun <- selectPassConvFinalize dict
            emitAtom0 $ LL.closureCallA free_fun [ret_val]

      -- Copy the C reference into the pyon reference
      return $ ReturnMarshaler { rmInputs = [pyon_ref]
                               , rmCode = setup
                               , rmOutput = []
                               , rmReturns = []}

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
getCExportSig :: TypeEnv -> Type -> CSignature
getCExportSig tenv ty =
  case getExportedFunctionSignature (getCExportType tenv) tenv ty
  of (param_types, return_type) ->
       CSignature param_types return_type

-- | Given a memory function type signature, determine the type of the
--   function that's exported to C++.
--
--   All elements of the type are assumed to be in their natural 
--   representation.  Code that looks at 'ExportSig's assumes this and
--   may break otherwise.
getCxxExportSig :: String -> TypeEnv -> Type -> CXXSignature
getCxxExportSig exported_name tenv ty =
  case getExportedFunctionSignature (getCxxExportType tenv) tenv ty
  of (param_types, return_type) ->
       CXXSignature exported_name param_types return_type

-- | Determine the exported parameter and return types of some
--   function type, using the given type conversion function to
--   convert each parameter and return type.
getExportedFunctionSignature :: (Type -> ExportDataType)
                             -> TypeEnv
                             -> Type
                             -> ([ExportDataType], ExportDataType)
getExportedFunctionSignature convert_type tenv ty =
  case getFunctionInputsAndOutputs tenv ty
  of (param_types, return_type) ->
       (map convert_type param_types, convert_type return_type)

-- | Determine the input and output types of a function. 
--
--   In most cases, the input types are the parameter types and
--   the output is the return type.  The primary exception is output
--   parameters.  These are converted to a bare return type.
--   The original function must not have a bare return type.
getFunctionInputsAndOutputs tenv ty =
  case fromFunType ty
  of (params, return) ->
       let param_types = mapMaybe get_param_input_type params
           return_type = get_output_type params return
       in (param_types, return_type)
  where
    kind t = toBaseKind $ typeKind tenv t

    -- Decide whether the parameter type describes an input
    input_param t =
      case kind t
      of ValK  -> True
         BoxK  -> True
         BareK -> True
         OutK  -> False
         _     -> internalError "getCExportSig: Unexpected type"

    -- Decide whether the return type describes an output.
    -- Store objects represent a return by side effect.
    output_return t =
      case kind t
      of ValK -> case t
                 of VarT v | v `isPyonBuiltin` The_Store -> False
                    _ -> True
         BoxK -> True
         _  -> internalError "getCExportSig: Unexpected type"

    get_param_input_type ty =
      if input_param ty then Just ty else Nothing

    get_output_type params rtype =
      -- If the function returns a value, then return that value
      -- If it returns by writing a pointer, then return the output object
      case (param_type, return_type)
      of (Just t, Nothing) -> t
         (Nothing, Just t) -> t
         _ -> internalError "getCExportSig: Unexpected type"
      where
        return_type = if output_return rtype then Just rtype else Nothing
        param_type =
          if null params
          then Nothing
          else case fromVarApp $ last params
               of Just (con, [arg])
                    | con `isPyonBuiltin` The_OutPtr -> Just arg
                  _ -> Nothing

getCExportType :: TypeEnv -> Type -> ExportDataType
getCExportType tenv ty =
  case fromVarApp ty
  of Just (con, args)
       | con `isPyonBuiltin` The_NoneType -> PyonNoneET
       | con `isPyonBuiltin` The_int -> PyonIntET
       | con `isPyonBuiltin` The_float -> PyonFloatET
       | con `isPyonBuiltin` The_bool -> PyonBoolET
       | con `isPyonBuiltin` The_list ->
           case args
           of [arg] -> ListET False (getCExportType tenv arg)
       | con `isPyonBuiltin` The_array2 ->
           case args
           of [arg] -> ArrayET 2 False (getCExportType tenv arg)
     _ | FunT {} <- ty ->
       case getExportedFunctionSignature (getCExportType tenv) tenv ty
       of (param_types, return_type) -> FunctionET param_types return_type
     _ -> unsupported
  where
    unsupported = internalError "getCExportType: Unsupported exported type"
                                        
getCxxExportType :: TypeEnv -> Type -> ExportDataType
getCxxExportType tenv ty =
  case fromVarApp ty
  of Just (con, args)
       | con `isPyonBuiltin` The_Stored ->
           -- Look through 'Stored' constructors.  Exported types are always 
           -- in their natural reprsentation, so we can ignore them.
           case args of [arg] -> getCxxExportType tenv arg
       | con `isPyonBuiltin` The_NoneType -> PyonNoneET
       | con `isPyonBuiltin` The_int -> PyonIntET
       | con `isPyonBuiltin` The_float -> PyonFloatET
       | con `isPyonBuiltin` The_bool -> PyonBoolET
       | con `isPyonBuiltin` The_PyonTuple2 ->
           if length args /= 2
           then type_error
           else TupleET $ map (getCxxExportType tenv) args
       | con `isPyonBuiltin` The_PyonTuple3 ->
           if length args /= 3
           then type_error
           else TupleET $ map (getCxxExportType tenv) args
       | con `isPyonBuiltin` The_PyonTuple4 ->
           if length args /= 4
           then type_error
           else TupleET $ map (getCxxExportType tenv) args
       | con `isPyonBuiltin` The_list ->
           unary (ListET False) args
       | con `isPyonBuiltin` The_array0 ->
           unary (ArrayET 0 False) args
       | con `isPyonBuiltin` The_array1 ->
           unary (ArrayET 1 False) args
       | con `isPyonBuiltin` The_array2 ->
           unary (ArrayET 2 False) args
       | con `isPyonBuiltin` The_array3 ->
           unary (ArrayET 3 False) args
       | con `isPyonBuiltin` The_blist ->
           unary (ListET True) args
       | con `isPyonBuiltin` The_barray1 ->
           unary (ArrayET 1 True) args
       | con `isPyonBuiltin` The_barray2 ->
           unary (ArrayET 2 True) args
       | con `isPyonBuiltin` The_barray3 ->
           unary (ArrayET 3 True) args
     _ -> unsupported
  where
    unary con [arg] = con (getCxxExportType tenv arg)
    unsupported = internalError "getCxxExportType: Unsupported exported type"

    type_error = internalError "getCxxExportType: Type error detected"
                                        
  