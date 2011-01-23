{-| Marshaling of function parameters and return values in code that 
is exported to C.
-}

module SystemF.Lowering.Marshaling(createCMarshalingFunction,
                                   getCExportSig)
where

import Gluon.Common.Error
import Builtins.Builtins
import qualified LowLevel.CodeTypes as LL
import qualified LowLevel.Syntax as LL
import LowLevel.Build
import LowLevel.Records
import SystemF.Syntax
import SystemF.MemoryIR
import SystemF.Lowering.LowerMonad
import Type.Type
import Export

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

marshalCParameter :: ExportDataType -> Lower ParameterMarshaler
marshalCParameter ty =
  case ty
  of ListET _ -> pass_by_reference
     PyonIntET -> marshal_value (LL.PrimType LL.pyonIntType)
     PyonFloatET -> marshal_value (LL.PrimType LL.pyonFloatType)
     PyonComplexFloatET -> marshal_value (LL.RecordType complex_float_type)
     PyonBoolET -> marshal_value (LL.PrimType LL.pyonBoolType)
  where
    complex_float_type = complexRecord (LL.PrimField LL.pyonFloatType)

    -- Pass an object reference
    pass_by_reference = do
      v <- LL.newAnonymousVar (LL.PrimType LL.PointerType)
      return $ ParameterMarshaler { pmInputs = [v]
                                  , pmCode = return ()
                                  , pmOutput = LL.VarV v}

    -- Pass a primitive type by value
    marshal_value t = do
      v <- LL.newAnonymousVar t
      return $ ParameterMarshaler { pmInputs = [v]
                                  , pmCode = return ()
                                  , pmOutput = LL.VarV v}

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
     PyonIntET -> marshal_value (LL.PrimType LL.pyonIntType)
     PyonFloatET -> marshal_value (LL.PrimType LL.pyonFloatType)
     PyonComplexFloatET -> marshal_value (LL.RecordType complex_float_type)
     PyonBoolET -> marshal_value (LL.PrimType LL.pyonBoolType)
  where
    complex_float_type = complexRecord (LL.PrimField LL.pyonFloatType)

    -- Allocate and return a new object.  The allocated object is passed
    -- as a parameter to the function.
    return_new_reference t = do
      v <- LL.newAnonymousVar (LL.PrimType LL.PointerType)
      
      let setup mk_real_call = do
            -- Allocate the return value
            allocateHeapMemAs (nativeWordV $ LL.sizeOf t) v
            
            -- Call the function, which returns nothing
            emitAtom0 =<< mk_real_call

      return $ ReturnMarshaler { rmInputs = []
                               , rmCode = setup
                               , rmOutput = [LL.VarV v] 
                               , rmReturns = [v]}

    -- Just return a primitive value
    marshal_value pt = do
      v <- LL.newAnonymousVar pt
      
      let setup mk_real_call = bindAtom1 v =<< mk_real_call
          
      return $ ReturnMarshaler { rmInputs = []
                               , rmCode = setup
                               , rmOutput = []
                               , rmReturns = [v]}

-- | Wrap the lowered function 'f' in marshaling code for C.  Produce a
-- primitive function.
createCMarshalingFunction :: ExportSig -> LL.Fun -> Lower LL.Fun
createCMarshalingFunction (CExportSig dom rng) f = do
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
getCExportSig :: Type -> ExportSig
getCExportSig ty =
  case fromFunType ty
  of (params, return) ->
       let param_types = [getCExportType t | _ ::: t <- params]
           return_type = case return of _ ::: t -> getCExportType t
       in CExportSig param_types return_type

getCExportType :: Type -> ExportDataType
getCExportType ty =
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
           of [arg] -> ListET $! getCExportType arg
     _ -> unsupported
  where
    unsupported = internalError "Unsupported exported type"
                                        
  