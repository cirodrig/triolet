
{-# LANGUAGE TemplateHaskell, FlexibleInstances #-}
module LowLevel.BuiltinsTH
where

import Language.Haskell.TH(Strict(..))
import Language.Haskell.TH.Syntax(Lift(..))

import Common.Error
import Common.Label
import Common.THRecord
import qualified Builtins.Builtins as SystemF
import Builtins.Builtins(pyonBuiltin)
import LowLevel.Types
import LowLevel.Record
import LowLevel.CodeTypes
import LowLevel.Records
import LowLevel.Syntax

instance Lift Signedness where
  lift x = let n = fromEnum x in [| toEnum n |]

instance Lift Size where
  lift x = let n = fromEnum x in [| toEnum n |]

instance Lift Mutability where
  lift x = let n = fromEnum x in [| toEnum n |]

instance Lift PrimType where
  lift UnitType = [| UnitType |]
  lift BoolType = [| BoolType |]
  lift (IntType sgn sz) = [| IntType sgn sz |]
  lift (FloatType sz) = [| FloatType sz |]
  lift PointerType = [| PointerType |]
  lift OwnedType = [| OwnedType |]

instance Lift (Field Int) where
  lift (Field off m t) = [| Field off m t |]

instance Lift (FieldType Int) where
  lift (PrimField pt) = [| PrimField pt |]
  lift (RecordField rt) = [| RecordField rt |]
  lift (BytesField s a) = [| BytesField s a |]
  lift (AlignField n) = [| AlignField n |]

instance Lift (Record Int) where
  lift rec = let fields = [(fieldOffset f, fieldMutable f , fieldType f) 
                          | f <- recordFields rec]
                 sz = sizeOf rec
                 al = alignOf rec
             in [| Rec [mkField o m t | (o, m, t) <- fields] sz al |]

instance Lift ValueType where
  lift (PrimType pt) = [| PrimType pt |]
  lift (RecordType rt) = [| RecordType rt |] 

instance Lift CallConvention where
  lift PrimCall = [| PrimCall |]
  lift ClosureCall = [| ClosureCall |]

instance Lift FunctionType where
  lift ft = [| mkFunctionType conv params returns |]
    where
      conv = ftConvention ft
      params = ftParamTypes ft
      returns = ftReturnTypes ft

-- | A 'BuiltinVarName' controls what name is assigned to a built-in variable. 
data BuiltinVarName =
    -- | Use the string as the external name
    CName { builtinVarModuleName :: ModuleName 
          , builtinVarUnqualifiedName :: String
          }
    -- | No external name
  | PyonName { builtinVarModuleName :: ModuleName 
             , builtinVarUnqualifiedName :: String
             }

instance Lift BuiltinVarName where
  lift (CName nm s) = [| CName nm s |]
  lift (PyonName nm s) = [| PyonName nm s |]

biName = CName builtinModuleName

applyName = PyonName (ModuleName "pyon.internal.apply_new")

-- | Predefined primitive functions
builtinPrimitives =
  [ -- debug.c
    (biName "pyon_db_int",
     primFunctionType [PrimType nativeIntType] [])
  , (biName "pyon_db_word",
     primFunctionType [PrimType nativeWordType] [])
  , (biName "pyon_db_pointer",
     primFunctionType [PrimType PointerType] [])
    -- memory.c
  , (biName "pyon_alloc",
     primFunctionType [PrimType nativeWordType] [PrimType PointerType])
  , (biName "pyon_dealloc",
     primFunctionType [PrimType PointerType] [])
    -- apply.c
  , (applyName "apply_i32_f",
     primFunctionType [ PrimType OwnedType
                      , PrimType (IntType Signed S32)] [PrimType OwnedType])
  , (applyName "apply_i32",
     primFunctionType [PrimType OwnedType
                      , PrimType (IntType Signed S32)
                      , PrimType PointerType] [])
  , (applyName "apply_f32_f",
     primFunctionType [ PrimType OwnedType
                      , PrimType (FloatType S32)] [PrimType OwnedType])
  , (applyName "apply_f32",
     primFunctionType [PrimType OwnedType
                      , PrimType (FloatType S32)
                      , PrimType PointerType] [])
  , (applyName "apply_i64_f",
     primFunctionType [ PrimType OwnedType
                      , PrimType (IntType Signed S64)] [PrimType OwnedType])
  , (applyName "apply_i64",
     primFunctionType [PrimType OwnedType
                      , PrimType (IntType Signed S64)
                      , PrimType PointerType] [])
{-  , (biName "free_pap",
     primFunctionType [PrimType PointerType] [])-}
  ]

closureBinaryFunctionType t = closureFunctionType [t, t] [t]

module_prim = ModuleName "pyon.internal.prim"
module_memory_py = ModuleName "pyon.internal.memory_py"
module_stream = ModuleName "pyon.internal.stream"
module_structures = ModuleName "pyon.internal.structures"
module_complex = ModuleName "pyon.internal.complex"
module_list = ModuleName "pyon.internal.list"

-- | Predefined closure functions and the core constructor they're derived
-- from.
builtinFunctions =
  [ -- Functions that do not exist in Core
    -- memory_py.pyasm
    (PyonName module_memory_py "deallocF",
     Left $ closureFunctionType [PrimType PointerType] [])
  , (CName module_memory_py "dummy_finalizer",
     Left $ closureFunctionType [PrimType PointerType] [])
  , (CName module_memory_py "copy1F",
     Left $
     closureFunctionType [PrimType PointerType, PrimType PointerType] [])
  , (CName module_memory_py "copy2F",
     Left $
     closureFunctionType [PrimType PointerType, PrimType PointerType] [])
  , (CName module_memory_py "copy4F",
     Left $
     closureFunctionType [PrimType PointerType, PrimType PointerType] [])

    -- Functions translated from Core
  , (PyonName module_memory_py "copy",
     Right [| pyonBuiltin (SystemF.the_copy) |])
{-  , (PyonName module_structures "makeComplex",
     Right [| pyonBuiltin (SystemF.the_makeComplex) |]) -}
  , (PyonName module_list "repr_list",
     Right [| pyonBuiltin SystemF.the_repr_list |])
  , (PyonName module_list "list_build",
     Right [| pyonBuiltin SystemF.the_TraversableDict_list_build |])
  , (PyonName module_list "list_traverse",
     Right [| pyonBuiltin SystemF.the_TraversableDict_list_traverse |]) {-
  , (PyonName module_list "list_generate",
     Right [| pyonBuiltin (SystemF.the_fun_generateList) |])
  , (PyonName module_list "list_vGenerate",
     Right [| pyonBuiltin (SystemF.the_fun_vectorGenerateList) |])
  , (PyonName module_stream "passConv_iter",
     Right [| pyonBuiltin (SystemF.the_passConv_iter) |]) -}
  , (PyonName module_stream "Stream_bind",
     Right [| pyonBuiltin (SystemF.the_oper_CAT_MAP) |])
  , (PyonName module_stream "Stream_return",
     Right [| pyonBuiltin (SystemF.the_oper_DO) |])
  , (PyonName module_stream "Stream_asList",
     Right [| pyonBuiltin (SystemF.the_fun_asList_Stream) |])    
  , (PyonName module_stream "generate",
     Right [| pyonBuiltin (SystemF.the_generate) |])
  , (PyonName module_stream "Stream_map",
     Right [| pyonBuiltin (SystemF.the_fun_map_Stream) |])
  , (PyonName module_stream "map",
     Right [| pyonBuiltin (SystemF.the_fun_map) |])
  , (PyonName module_stream "Stream_reduce",
     Right [| pyonBuiltin (SystemF.the_fun_reduce_Stream) |])
  , (PyonName module_stream "reduce",
     Right [| pyonBuiltin (SystemF.the_fun_reduce) |])
  , (PyonName module_stream "Stream_reduce1",
     Right [| pyonBuiltin (SystemF.the_fun_reduce1_Stream) |])
  , (PyonName module_stream "reduce1",
     Right [| pyonBuiltin (SystemF.the_fun_reduce1) |])
  , (PyonName module_stream "Stream_zip",
     Right [| pyonBuiltin (SystemF.the_fun_zip_Stream) |])
  , (PyonName module_stream "Stream_zip3",
     Right [| pyonBuiltin (SystemF.the_fun_zip3_Stream) |])
  , (PyonName module_stream "Stream_zip4",
     Right [| pyonBuiltin (SystemF.the_fun_zip4_Stream) |])
  , (PyonName module_stream "zip",
     Right [| pyonBuiltin (SystemF.the_fun_zip) |])
  , (PyonName module_stream "zip3",
     Right [| pyonBuiltin (SystemF.the_fun_zip3) |])
  , (PyonName module_stream "zip4",
     Right [| pyonBuiltin (SystemF.the_fun_zip4) |])
  , (PyonName module_stream "Stream_build",
     Right [| pyonBuiltin (SystemF.the_TraversableDict_Stream_build) |])
  , (PyonName module_stream "Stream_traverse",
     Right [| pyonBuiltin (SystemF.the_TraversableDict_Stream_traverse) |])
  , (PyonName module_stream "Stream_count",
     Right [| pyonBuiltin (SystemF.the_count) |])
  , (PyonName module_stream "Stream_range",
     Right [| pyonBuiltin (SystemF.the_range) |])
  , (PyonName module_stream "histogram",
     Right [| pyonBuiltin (SystemF.the_histogram) |])
  , (PyonName module_structures "repr_Box",
     Right [| SystemF.pyonBuiltin SystemF.the_repr_Box |])
  , (PyonName module_structures "repr_Boxed",
     Right [| SystemF.pyonBuiltin SystemF.the_repr_Boxed |])
  , (PyonName module_structures "repr_Stream",
     Right [| SystemF.pyonBuiltin SystemF.the_repr_Stream |])
  , (PyonName module_structures "repr_EmptyReference",
     Right [| SystemF.pyonBuiltin SystemF.the_repr_EmptyReference |])
  {-, (PyonName module_structures "complex_pass_conv",
     Left $
     closureFunctionType [PrimType UnitType,
                          PrimType PointerType,
                          PrimType PointerType] []) -}
  , (PyonName module_structures "repr_PyonTuple2",
     Right [| SystemF.pyonBuiltin SystemF.the_repr_PyonTuple2 |])
  , (PyonName module_structures "repr_PyonTuple3",
     Right [| SystemF.pyonBuiltin SystemF.the_repr_PyonTuple3 |])
  , (PyonName module_structures "repr_PyonTuple4",
     Right [| SystemF.pyonBuiltin SystemF.the_repr_PyonTuple4 |])
    
  , (PyonName module_prim "subscript",
     Right [| pyonBuiltin (SystemF.the_subscript) |])
  , (PyonName module_prim "subscript_out",
     Right [| pyonBuiltin (SystemF.the_subscript_out) |])

  , (PyonName module_prim "doall",
     Right [| pyonBuiltin (SystemF.the_doall) |])
  , (PyonName module_prim "for",
     Right [| pyonBuiltin (SystemF.the_for) |])

    -- Functions that are replaced by primitive operations
  , (PyonName module_prim "storeBox",
     Right [| pyonBuiltin SystemF.the_storeBox |])
  , (PyonName module_prim "loadBox",
     Right [| pyonBuiltin SystemF.the_loadBox |])
  , (PyonName module_prim "ptrToBox",
     Right [| pyonBuiltin SystemF.the_ptrToBox |])
  , (PyonName module_prim "boxToPtr",
     Right [| pyonBuiltin SystemF.the_boxToPtr |])
  , (PyonName module_prim "eq_int",
     Right [| pyonBuiltin (SystemF.the_EqDict_int_eq) |])
  , (PyonName module_prim "ne_int",
     Right [| pyonBuiltin (SystemF.the_EqDict_int_ne) |])
  , (PyonName module_prim "eq_float",
     Right [| pyonBuiltin (SystemF.the_EqDict_float_eq) |])
  , (PyonName module_prim "ne_float",
     Right [| pyonBuiltin (SystemF.the_EqDict_float_ne) |])
  , (PyonName module_prim "lt_int",
     Right [| pyonBuiltin SystemF.the_OrdDict_int_lt |])
  , (PyonName module_prim "le_int",
     Right [| pyonBuiltin SystemF.the_OrdDict_int_le |])
  , (PyonName module_prim "gt_int",
     Right [| pyonBuiltin SystemF.the_OrdDict_int_gt |])
  , (PyonName module_prim "ge_int",
     Right [| pyonBuiltin SystemF.the_OrdDict_int_ge |])
  , (PyonName module_prim "lt_float",
     Right [| pyonBuiltin SystemF.the_OrdDict_float_lt |])
  , (PyonName module_prim "le_float",
     Right [| pyonBuiltin SystemF.the_OrdDict_float_le |])
  , (PyonName module_prim "gt_float",
     Right [| pyonBuiltin SystemF.the_OrdDict_float_gt |])
  , (PyonName module_prim "ge_float",
     Right [| pyonBuiltin SystemF.the_OrdDict_float_ge |])
    -- the_AdditiveDict_int_{add,sub} were replaced by intrinsics
  , (PyonName module_prim "negate_int",
     Right [| pyonBuiltin (SystemF.the_AdditiveDict_int_negate) |])
    -- zero_int was replaced by a literal value
    -- the_AdditiveDict_float_{add,sub} were replaced by intrinsics
  , (PyonName module_prim "negate_float",
     Right [| pyonBuiltin (SystemF.the_AdditiveDict_float_negate) |])
  , (PyonName module_prim "min_ii",
     Right [| pyonBuiltin (SystemF.the_min_ii) |])
    -- zero_float was replaced by a literal value
  , (PyonName module_complex "AdditiveDict_Complex_add",
     Right [| pyonBuiltin (SystemF.the_AdditiveDict_Complex_add) |])
  , (PyonName module_complex "AdditiveDict_Complex_sub",
     Right [| pyonBuiltin (SystemF.the_AdditiveDict_Complex_sub) |])
  , (PyonName module_complex "AdditiveDict_Complex_negate",
     Right [| pyonBuiltin (SystemF.the_AdditiveDict_Complex_negate) |])
  , (PyonName module_complex "AdditiveDict_Complex_zero",
     Right [| pyonBuiltin (SystemF.the_AdditiveDict_Complex_zero) |])
    -- the_MultiplicativeDict_int_* are intrinsics
    -- the_MultiplicativeDict_float_mul is intrinsic
  , (PyonName module_prim "fromint_float",
     Right [| pyonBuiltin (SystemF.the_MultiplicativeDict_float_fromInt) |])
  , (PyonName module_complex "MultiplicativeDict_Complex_mul",
     Right [| pyonBuiltin (SystemF.the_MultiplicativeDict_Complex_mul) |])
  , (PyonName module_complex "MultiplicativeDict_Complex_fromInt",
     Right [| pyonBuiltin (SystemF.the_MultiplicativeDict_Complex_fromInt) |])
  , (PyonName module_complex "MultiplicativeDict_Complex_one",
     Right [| pyonBuiltin (SystemF.the_MultiplicativeDict_Complex_one) |])
  , (PyonName module_prim "mod_int",
     Right [| pyonBuiltin SystemF.the_RemainderDict_int_mod |])
  , (PyonName module_prim "floordiv_int",
     Right [| pyonBuiltin SystemF.the_RemainderDict_int_floordiv |])
  , (PyonName module_prim "mod_float",
     Right [| pyonBuiltin SystemF.the_RemainderDict_float_mod |])
  , (PyonName module_prim "floordiv_float",
     Right [| pyonBuiltin SystemF.the_RemainderDict_float_floordiv |])
  , (PyonName module_prim "div_float",
     Right [| pyonBuiltin SystemF.the_FractionalDict_float_div |])
    -- one_float was replaced by a literal value
{-  , (PyonName builtinModuleName "load_int",
     Right [| pyonBuiltin (SystemF.the_fun_load_int) |])
  , (PyonName builtinModuleName "load_float",
     Right [| pyonBuiltin (SystemF.the_fun_load_float) |])
  , (PyonName module_prim "load_complexFloat",
     Right [| pyonBuiltin SystemF.the_fun_load_complexFloat |])
  , (PyonName builtinModuleName "load_bool",
     Right [| pyonBuiltin (SystemF.the_fun_load_bool) |])
  , (PyonName builtinModuleName "load_NoneType",
     Right [| pyonBuiltin (SystemF.the_fun_load_NoneType) |])
  , (PyonName builtinModuleName "store_int",
     Right [| pyonBuiltin (SystemF.the_fun_store_int) |])
  , (PyonName builtinModuleName "store_float",
     Right [| pyonBuiltin (SystemF.the_fun_store_float) |])
  , (PyonName module_prim "store_complexFloat",
     Right [| pyonBuiltin SystemF.the_fun_store_complexFloat |])
  , (PyonName builtinModuleName "store_bool",
     Right [| pyonBuiltin (SystemF.the_fun_store_bool) |])
  , (PyonName builtinModuleName "store_NoneType",
     Right [| pyonBuiltin (SystemF.the_fun_store_NoneType) |])-}
  ]

-- | Predefined global data
builtinGlobals =
  [ -- Info tables
    (biName "pap_info",
     Left $ PrimType PointerType)
  , (biName "global_closure_info",
     Left $ PrimType PointerType)
    -- Dictionaries
  , (PyonName module_structures "OpaqueTraversableDict_list",
     Right [| pyonBuiltin SystemF.the_OpaqueTraversableDict_list |])
    -- Physical representations of data types
  , (PyonName module_structures "repr_Box_value",
     Left $ PrimType OwnedType)
  , (PyonName module_structures "repr_int",
     Right [| pyonBuiltin (SystemF.the_repr_int) |] )
  , (PyonName module_structures "repr_float",
     Right [| pyonBuiltin (SystemF.the_repr_float) |] )
  , (PyonName module_structures "repr_bool",
     Right [| pyonBuiltin (SystemF.the_repr_bool) |] )
  ]

builtinVarPrimName nm = "the_biprim_" ++ builtinVarUnqualifiedName nm
builtinVarFunName nm = "the_bifun_" ++ builtinVarUnqualifiedName nm
builtinVarVarName nm = "the_bivar_" ++ builtinVarUnqualifiedName nm

lowLevelBuiltinsRecord = recordDef "LowLevelBuiltins" fields
  where
    prim_field (nm, _) =
      (builtinVarPrimName nm, IsStrict,
       [t| (Var, FunctionType) |])
    clo_field (nm, _) =
      (builtinVarFunName nm, IsStrict,
       [t| (Var, EntryPoints) |])
    var_field (nm, _) =
      (builtinVarVarName nm, IsStrict, [t| Var |])
    fields = map prim_field builtinPrimitives ++
             map clo_field builtinFunctions ++
             map var_field builtinGlobals
