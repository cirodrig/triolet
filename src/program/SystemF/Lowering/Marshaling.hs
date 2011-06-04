{-| Marshaling of function parameters and return values in code that 
is exported to C.
-}

module SystemF.Lowering.Marshaling(createCMarshalingFunction,
                                   getCExportSig)
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

-- | Construct a representation dictionary for a marshalable type.
--   For types with an unknown head, 'lookupReprDict' is called.  Known types
--   are handled by case.
computeReprDict :: Type -> GenLower LL.Val
computeReprDict ty =
  case fromVarApp ty
  of Just (op, args)
       | op `isPyonBuiltin` the_list -> do
           let [element_type] = args
           let list_repr_ctor = LL.VarV (LL.llBuiltin LL.the_fun_repr_list)
           element_dict <- computeReprDict element_type
           emitAtom1 owned_type $
             LL.closureCallA list_repr_ctor [element_dict]
       | op `isPyonBuiltin` the_int ->
           return $ LL.VarV $ LL.llBuiltin LL.the_bivar_repr_int
       | op `isPyonBuiltin` the_float ->
           return $ LL.VarV $ LL.llBuiltin LL.the_bivar_repr_float
       | op `isPyonBuiltin` the_bool ->
           return $ LL.VarV $ LL.llBuiltin LL.the_bivar_repr_bool
       | otherwise -> lookupReprDict ty return
  where
    owned_type = LL.PrimType LL.OwnedType
           
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
  of ListET _ -> passParameterWithType (LL.PrimType LL.PointerType)
     PyonIntET -> passParameterWithType (LL.PrimType LL.pyonIntType)
     PyonFloatET -> passParameterWithType (LL.PrimType LL.pyonFloatType)
     PyonComplexFloatET ->
       passParameterWithType (LL.RecordType complex_float_type)
     PyonBoolET -> passParameterWithType (LL.PrimType LL.pyonBoolType)
     FunctionET args ret -> marshalParameterFunctionFromC args ret
  where
    complex_float_type = complexRecord (LL.PrimField LL.pyonFloatType)

-- | Marshal a function parameter that was passed from pyon.  The converted
--   parameter will be passed to a C function.
demarshalCParameter :: ExportDataType -> Lower ParameterMarshaler
demarshalCParameter ty =
  case ty
  of ListET _ -> passParameterWithType (LL.PrimType LL.PointerType)
     PyonIntET -> passParameterWithType (LL.PrimType LL.pyonIntType)
     PyonFloatET -> passParameterWithType (LL.PrimType LL.pyonFloatType)
     PyonBoolET -> passParameterWithType (LL.PrimType LL.pyonBoolType)
     FunctionET args ret -> marshalParameterFunctionToC args ret

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
  of ListET _ -> return_new_reference (LL.RecordType listRecord)
     PyonIntET -> passReturnWithType (LL.PrimType LL.pyonIntType)
     PyonFloatET -> passReturnWithType (LL.PrimType LL.pyonFloatType)
     PyonComplexFloatET -> passReturnWithType (LL.RecordType complex_float_type)
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

demarshalCReturn :: ExportDataType -> Lower ReturnMarshaler
demarshalCReturn ty =
  case ty
  of ListET element_type ->
       let list_type = varApp (pyonBuiltin the_list) [element_type]
       in demarshal_reference list_type
     PyonIntET -> passReturnWithType (LL.PrimType LL.pyonIntType)
     PyonFloatET -> passReturnWithType (LL.PrimType LL.pyonFloatType)
     PyonComplexFloatET -> passReturnWithType (LL.RecordType complex_float_type)
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

-- | Wrap the lowered function 'f' in marshaling code for C.  Produce a
-- primitive function.
createCMarshalingFunction :: ExportSig -> LL.Fun -> Lower LL.Fun
createCMarshalingFunction sig@(CExportSig dom rng) f = do
  -- Generate marshaling code
  marshal_params <- mapM marshalCParameter dom
  marshal_return <- marshalCReturn rng

  -- Create the function
  let return_types = map LL.varType $ rmReturns marshal_return
      (param_inputs, param_code, param_arguments) =
        combineParameterMarshalers marshal_params

  fun_body <- execBuild return_types $ do
    param_code                  -- Marshal the parameters
    
    -- Call the function and marshal the return value
    let call_arguments = param_arguments ++ rmOutput marshal_return
    rmCode marshal_return $ do
      return $ LL.closureCallA (LL.LamV f) call_arguments
    
    -- Return the return value
    return $ LL.ReturnE $ LL.ValA (map LL.VarV $ rmReturns marshal_return)

  return $ LL.primFun param_inputs return_types fun_body

createCMarshallingFunction _ _ =
  internalError "createCMarshallingFunction: Not exported to C"

-------------------------------------------------------------------------------
-- Exported types

-- | Given a memory function type signature, determine the type of the
--   function that's exported to C.
--
--   All elements of the type are assumed to be in their natural 
--   representation.  Code that looks at 'ExportSig's assumes this and
--   may break otherwise.
getCExportSig :: TypeEnv -> Type -> ExportSig
getCExportSig tenv ty =
  case getFunctionExportType tenv ty
  of (param_types, return_type) -> CExportSig param_types return_type

getFunctionExportType tenv ty =
  case fromFunType ty
  of (params, return) ->
       let param_types = mapMaybe get_param_export_type params
           return_type = get_return_export_type params return
       in (param_types, return_type)
  where
    kind t = toBaseKind $ typeKind tenv t

    get_param_export_type ty = 
      case kind ty
      of ValK  -> Just $ getCExportType tenv ty
         BoxK  -> Just $ getCExportType tenv ty
         BareK -> Just $ getCExportType tenv ty
         OutK  -> Nothing
         _ -> internalError "getCExportSig: Unexpected type"

    -- If the function returns a value, then return that value
    -- If it returns by writing a pointer, then return the output object
    get_return_export_type params rtype =
      let return_type =
            case kind rtype
            of ValK -> Just $ getCExportType tenv rtype
               BoxK -> Just $ getCExportType tenv rtype
               SideEffectK -> Nothing
               _ -> internalError "getCExportSig: Unexpected type"
          param_type =
            if null params
            then Nothing
            else case fromVarApp $ last params
                 of Just (con, [arg])
                      | con `isPyonBuiltin` the_OutPtr ->
                          Just $ getCExportType tenv arg
                    _ -> Nothing
      in case (param_type, return_type)
         of (Just t, Nothing) -> t
            (Nothing, Just t) -> t
            _ -> internalError "getCExportSig: Unexpected type"

getCExportType :: TypeEnv -> Type -> ExportDataType
getCExportType tenv ty =
  case fromVarApp ty
  of Just (con, args)
       | con `isPyonBuiltin` the_int -> PyonIntET
       | con `isPyonBuiltin` the_float -> PyonFloatET
       | con `isPyonBuiltin` the_bool -> PyonBoolET
       | con `isPyonBuiltin` the_complex ->
           case args
           of [arg] ->
                case fromVarApp arg
                of Just (con, _)
                     | con `isPyonBuiltin` the_float -> PyonComplexFloatET
                   _ -> unsupported
       | con `isPyonBuiltin` the_list ->
           case args
           of [arg] -> ListET arg -- FIXME: verify that 'arg' is monomorphic
     _ | FunT {} <- ty ->
       case getFunctionExportType tenv ty
       of (param_types, return_type) -> FunctionET param_types return_type
     _ -> unsupported
  where
    unsupported = internalError "Unsupported exported type"
                                        
  