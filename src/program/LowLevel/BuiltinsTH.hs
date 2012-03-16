
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
             in [| Record [mkField o m t | (o, m, t) <- fields] sz al |]

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
  [ -- C library functions
    (biName "exit",
     primFunctionType [PrimType nativeIntType] [])
    -- debug.c
  , (biName "pyon_db_int",
     primFunctionType [PrimType nativeIntType] [])
  , (biName "pyon_db_word",
     primFunctionType [PrimType nativeWordType] [])
  , (biName "pyon_db_pointer",
     primFunctionType [PrimType PointerType] [])
    -- memory.c
  , (biName "pyon_alloc",
     primFunctionType [PrimType nativeWordType] [PrimType PointerType])
  , (biName "pyon_alloc_nopointers",
     primFunctionType [PrimType nativeWordType] [PrimType PointerType])
  , (biName "pyon_dealloc",
     primFunctionType [PrimType PointerType] [])
    -- prim.pyasm
  , (PyonName module_prim "min_fii",
     primFunctionType
     [RecordType finIndexedIntRecord, RecordType finIndexedIntRecord]
     [RecordType finIndexedIntRecord])
  , (PyonName module_prim "minus_fii",
     primFunctionType
     [RecordType finIndexedIntRecord, RecordType finIndexedIntRecord]
     [RecordType finIndexedIntRecord])
    -- apply.c
  , (applyName "apply_u_f",
     primFunctionType [ PrimType OwnedType
                      , PrimType UnitType] [PrimType OwnedType])
  , (applyName "apply_u",
     primFunctionType [PrimType OwnedType
                      , PrimType UnitType
                      , PrimType PointerType] [])
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
module_effects = ModuleName "pyon.internal.effects"
module_inplace = ModuleName "pyon.internal.inplace"
module_complex = ModuleName "pyon.internal.complex"
module_list = ModuleName "pyon.internal.list"

-- | Predefined closure functions and the core constructor they're derived
-- from.
builtinFunctions =
  [ -- Functions that do not exist in Core
    -- memory_py.pyasm
    (PyonName module_memory_py "deallocF",
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
     Right [| pyonBuiltin (SystemF.The_copy) |])
  , (PyonName module_prim "convertToBoxed",
     Right [| pyonBuiltin (SystemF.The_convertToBoxed) |])
  , (PyonName module_prim "convertToBare",
     Right [| pyonBuiltin (SystemF.The_convertToBare) |])
{-  , (PyonName module_structures "makeComplex",
     Right [| pyonBuiltin (SystemF.The_makeComplex) |]) -}
  , (PyonName module_list "repr_list",
     Right [| pyonBuiltin SystemF.The_repr_list |])
  , (PyonName module_list "repr_array0",
     Right [| pyonBuiltin SystemF.The_repr_array0 |])
  , (PyonName module_list "repr_array1",
     Right [| pyonBuiltin SystemF.The_repr_array1 |])
  , (PyonName module_list "repr_array2",
     Right [| pyonBuiltin SystemF.The_repr_array2 |])
  , (PyonName module_list "repr_array3",
     Right [| pyonBuiltin SystemF.The_repr_array3 |])
  --, (PyonName module_list "list_len",
  --   Right [| pyonBuiltin SystemF.The_len |])
  , (PyonName module_list "list_build",
     Right [| pyonBuiltin SystemF.The_Sequence_build_list |])
  , (PyonName module_list "array1_build",
     Right [| pyonBuiltin SystemF.The_Sequence_array1_build |])
  -- , (PyonName module_list "list_traverse",
  --   Right [| pyonBuiltin SystemF.The_TraversableDict_list_traverse |])
  {- , (PyonName module_list "safeSubscript",
     Right [| pyonBuiltin (SystemF.The_safeSubscript) |])
  , (PyonName module_list "list_generate",
     Right [| pyonBuiltin (SystemF.The_fun_generateList) |])
  , (PyonName module_list "list_vGenerate",
     Right [| pyonBuiltin (SystemF.The_fun_vectorGenerateList) |])
  , (PyonName module_stream "passConv_iter",
     Right [| pyonBuiltin (SystemF.The_passConv_iter) |])
  , (PyonName module_stream "Stream_bind",
     Right [| pyonBuiltin (SystemF.The_oper_CAT_MAP) |])
  , (PyonName module_stream "Stream_guard",
     Right [| pyonBuiltin (SystemF.The_oper_GUARD) |])
  , (PyonName module_stream "Stream_return",
     Right [| pyonBuiltin (SystemF.The_oper_DO) |])
  , (PyonName module_stream "Stream_empty",
     Right [| pyonBuiltin (SystemF.The_oper_EMPTY) |])
  , (PyonName module_stream "Stream_asList",
     Right [| pyonBuiltin (SystemF.The_fun_asList_Stream) |])    
  , (PyonName module_stream "generate",
     Right [| pyonBuiltin (SystemF.The_generate) |])
  , (PyonName module_stream "Stream_map",
     Right [| pyonBuiltin (SystemF.The_fun_map_Stream) |])
  , (PyonName module_stream "map",
     Right [| pyonBuiltin (SystemF.The_fun_map) |])
  , (PyonName module_stream "Stream_reduce",
     Right [| pyonBuiltin (SystemF.The_fun_reduce_Stream) |])
  , (PyonName module_stream "reduce",
     Right [| pyonBuiltin (SystemF.The_fun_reduce) |])
  , (PyonName module_stream "Stream_reduce1",
     Right [| pyonBuiltin (SystemF.The_fun_reduce1_Stream) |])
  , (PyonName module_stream "reduce1",
     Right [| pyonBuiltin (SystemF.The_fun_reduce1) |])
  , (PyonName module_stream "Stream_fold",
     Right [| pyonBuiltin (SystemF.The_fun_fold_Stream) |])
  , (PyonName module_stream "Stream_zip",
     Right [| pyonBuiltin (SystemF.The_fun_zip_Stream) |])
  , (PyonName module_stream "Stream_zip3",
     Right [| pyonBuiltin (SystemF.The_fun_zip3_Stream) |])
  , (PyonName module_stream "Stream_zip4",
     Right [| pyonBuiltin (SystemF.The_fun_zip4_Stream) |])
  , (PyonName module_stream "zip",
     Right [| pyonBuiltin (SystemF.The_fun_zip) |])
  , (PyonName module_stream "zip3",
     Right [| pyonBuiltin (SystemF.The_fun_zip3) |])
  , (PyonName module_stream "zip4",
     Right [| pyonBuiltin (SystemF.The_fun_zip4) |])
  , (PyonName module_stream "Stream_build",
     Right [| pyonBuiltin (SystemF.The_TraversableDict_Stream_build) |])
  , (PyonName module_stream "Stream_traverse",
     Right [| pyonBuiltin (SystemF.The_TraversableDict_Stream_traverse) |])
  , (PyonName module_stream "Stream_range",
     Right [| pyonBuiltin (SystemF.The_range) |])
  , (PyonName module_stream "Stream_rangeIndexed",
     Right [| pyonBuiltin (SystemF.The_rangeIndexed) |])
  , (PyonName module_stream "histogram",
     Right [| pyonBuiltin (SystemF.The_histogram) |])-}
  , (PyonName module_inplace "intSumScatter_make_init",
     Right [| pyonBuiltin (SystemF.The_intSumScatter_make_init) |])
  , (PyonName module_inplace "countingScatter_make_init",
     Right [| pyonBuiltin (SystemF.The_countingScatter_make_init) |])
  , (PyonName module_inplace "intUpdateInPlace_initializer",
     Right [| pyonBuiltin (SystemF.The_intUpdateInPlace_initializer) |])
  , (PyonName module_inplace "intUpdateInPlace_updater",
     Right [| pyonBuiltin (SystemF.The_intUpdateInPlace_updater) |])
  , (PyonName module_inplace "floatSumScatter_make_init",
     Right [| pyonBuiltin (SystemF.The_floatSumScatter_make_init) |])
  , (PyonName module_inplace "floatUpdateInPlace_initializer",
     Right [| pyonBuiltin (SystemF.The_floatUpdateInPlace_initializer) |])
  , (PyonName module_inplace "floatUpdateInPlace_updater",
     Right [| pyonBuiltin (SystemF.The_floatUpdateInPlace_updater) |])
  , (PyonName module_inplace "boxedScatter_updater",
     Right [| pyonBuiltin (SystemF.The_boxedScatter_updater) |])
  , (PyonName module_effects "seqEffTok",
     Right [| pyonBuiltin (SystemF.The_seqEffTok) |])
  , (PyonName module_structures "repr_arr",
     Right [| SystemF.pyonBuiltin SystemF.The_repr_arr |])
  , (PyonName module_structures "repr_Referenced",
     Right [| SystemF.pyonBuiltin SystemF.The_repr_Referenced |])
  , (PyonName module_structures "repr_Maybe",
     Right [| SystemF.pyonBuiltin SystemF.The_repr_Maybe |])
  {-, (PyonName module_structures "complex_pass_conv",
     Left $
     closureFunctionType [PrimType UnitType,
                          PrimType PointerType,
                          PrimType PointerType] []) -}
  , (PyonName module_structures "repr_PyonTuple2",
     Right [| SystemF.pyonBuiltin SystemF.The_repr_PyonTuple2 |])
  , (PyonName module_structures "repr_PyonTuple3",
     Right [| SystemF.pyonBuiltin SystemF.The_repr_PyonTuple3 |])
  , (PyonName module_structures "repr_PyonTuple4",
     Right [| SystemF.pyonBuiltin SystemF.The_repr_PyonTuple4 |])
  
  , (PyonName module_prim "defineIntIndex",
     Right [| pyonBuiltin (SystemF.The_defineIntIndex) |])
  , (PyonName module_prim "subscript",
     Right [| pyonBuiltin (SystemF.The_subscript) |])
  , (PyonName module_prim "subscript_out",
     Right [| pyonBuiltin (SystemF.The_subscript_out) |])
  , (PyonName module_prim "min_ii",
     Right [| pyonBuiltin (SystemF.The_min_ii) |])
  , (PyonName module_prim "minus_ii",
     Right [| pyonBuiltin (SystemF.The_minus_ii) |])
  , (PyonName module_prim "not",
     Right [| pyonBuiltin (SystemF.The_not) |])
  , (PyonName module_prim "gcd",
     Right [| pyonBuiltin (SystemF.The_gcd) |])
  , (PyonName module_prim "extgcd_x",
     Right [| pyonBuiltin (SystemF.The_extgcd_x) |])

  , (PyonName module_prim "doall",
     Right [| pyonBuiltin (SystemF.The_doall) |])
  --, (PyonName module_prim "for",
  --   Right [| pyonBuiltin (SystemF.The_for) |])
  , (PyonName module_prim "blocked_1d_reduce",
     Right [| pyonBuiltin (SystemF.The_blocked_1d_reduce) |])
  , (PyonName module_prim "blocked_2d_reduce",
     Right [| pyonBuiltin (SystemF.The_blocked_2d_reduce) |])
  , (PyonName module_prim "blocked_doall",
     Right [| pyonBuiltin (SystemF.The_blocked_doall) |])
  , (PyonName module_prim "blocked_doall2",
     Right [| pyonBuiltin (SystemF.The_blocked_doall2) |])

    -- Functions that are replaced by primitive operations
  , (PyonName module_prim "eq_int",
     Right [| pyonBuiltin (SystemF.The_EqDict_int_eq) |])
  , (PyonName module_prim "ne_int",
     Right [| pyonBuiltin (SystemF.The_EqDict_int_ne) |])
  , (PyonName module_prim "eq_float",
     Right [| pyonBuiltin (SystemF.The_EqDict_float_eq) |])
  , (PyonName module_prim "ne_float",
     Right [| pyonBuiltin (SystemF.The_EqDict_float_ne) |])
  , (PyonName module_prim "lt_int",
     Right [| pyonBuiltin SystemF.The_OrdDict_int_lt |])
  , (PyonName module_prim "le_int",
     Right [| pyonBuiltin SystemF.The_OrdDict_int_le |])
  , (PyonName module_prim "gt_int",
     Right [| pyonBuiltin SystemF.The_OrdDict_int_gt |])
  , (PyonName module_prim "ge_int",
     Right [| pyonBuiltin SystemF.The_OrdDict_int_ge |])
  , (PyonName module_prim "lt_float",
     Right [| pyonBuiltin SystemF.The_OrdDict_float_lt |])
  , (PyonName module_prim "le_float",
     Right [| pyonBuiltin SystemF.The_OrdDict_float_le |])
  , (PyonName module_prim "gt_float",
     Right [| pyonBuiltin SystemF.The_OrdDict_float_gt |])
  , (PyonName module_prim "ge_float",
     Right [| pyonBuiltin SystemF.The_OrdDict_float_ge |])
    -- the_AdditiveDict_int_{add,sub} were replaced by intrinsics
  , (PyonName module_prim "negate_int",
     Right [| pyonBuiltin (SystemF.The_AdditiveDict_int_negate) |])
    -- zero_int was replaced by a literal value
    -- the_AdditiveDict_float_{add,sub} were replaced by intrinsics
  , (PyonName module_prim "negate_float",
     Right [| pyonBuiltin (SystemF.The_AdditiveDict_float_negate) |])
    -- zero_float was replaced by a literal value
  {-, (PyonName module_complex "AdditiveDict_Complex_add",
     Right [| pyonBuiltin (SystemF.The_AdditiveDict_Complex_add) |])
  , (PyonName module_complex "AdditiveDict_Complex_sub",
     Right [| pyonBuiltin (SystemF.The_AdditiveDict_Complex_sub) |])
  , (PyonName module_complex "AdditiveDict_Complex_negate",
     Right [| pyonBuiltin (SystemF.The_AdditiveDict_Complex_negate) |])
  , (PyonName module_complex "AdditiveDict_Complex_zero",
     Right [| pyonBuiltin (SystemF.The_AdditiveDict_Complex_zero) |])-}
    -- the_MultiplicativeDict_int_* are intrinsics
    -- the_MultiplicativeDict_float_mul is intrinsic
  , (PyonName module_prim "fromint_float",
     Right [| pyonBuiltin (SystemF.The_MultiplicativeDict_float_fromInt) |])
  {-, (PyonName module_complex "MultiplicativeDict_Complex_mul",
     Right [| pyonBuiltin (SystemF.The_MultiplicativeDict_Complex_mul) |])
  , (PyonName module_complex "MultiplicativeDict_Complex_fromInt",
     Right [| pyonBuiltin (SystemF.The_MultiplicativeDict_Complex_fromInt) |])
  , (PyonName module_complex "MultiplicativeDict_Complex_one",
     Right [| pyonBuiltin (SystemF.The_MultiplicativeDict_Complex_one) |])-}
  , (PyonName module_prim "mod_int",
     Right [| pyonBuiltin SystemF.The_RemainderDict_int_mod |])
  , (PyonName module_prim "floordiv_int",
     Right [| pyonBuiltin SystemF.The_RemainderDict_int_floordiv |])
  , (PyonName module_prim "mod_float",
     Right [| pyonBuiltin SystemF.The_RemainderDict_float_mod |])
  , (PyonName module_prim "floordiv_float",
     Right [| pyonBuiltin SystemF.The_RemainderDict_float_floordiv |])
  , (PyonName module_prim "div_float",
     Right [| pyonBuiltin SystemF.The_FractionalDict_float_div |])
    -- one_float was replaced by a literal value
{-  , (PyonName builtinModuleName "load_int",
     Right [| pyonBuiltin (SystemF.The_fun_load_int) |])
  , (PyonName builtinModuleName "load_float",
     Right [| pyonBuiltin (SystemF.The_fun_load_float) |])
  , (PyonName module_prim "load_complexFloat",
     Right [| pyonBuiltin SystemF.The_fun_load_complexFloat |])
  , (PyonName builtinModuleName "load_bool",
     Right [| pyonBuiltin (SystemF.The_fun_load_bool) |])
  , (PyonName builtinModuleName "load_NoneType",
     Right [| pyonBuiltin (SystemF.The_fun_load_NoneType) |])
  , (PyonName builtinModuleName "store_int",
     Right [| pyonBuiltin (SystemF.The_fun_store_int) |])
  , (PyonName builtinModuleName "store_float",
     Right [| pyonBuiltin (SystemF.The_fun_store_float) |])
  , (PyonName module_prim "store_complexFloat",
     Right [| pyonBuiltin SystemF.The_fun_store_complexFloat |])
  , (PyonName builtinModuleName "store_bool",
     Right [| pyonBuiltin (SystemF.The_fun_store_bool) |])
  , (PyonName builtinModuleName "store_NoneType",
     Right [| pyonBuiltin (SystemF.The_fun_store_NoneType) |])-}
  ]

-- | Predefined global data
builtinGlobals =
  [ -- Info tables
    (biName "pap_info",
     Left $ PrimType PointerType)
  , (biName "global_closure_info",
     Left $ PrimType PointerType)

    -- Physical representations of data types
  , (PyonName module_list "repr_barray1",
     Right [| pyonBuiltin SystemF.The_repr_barray1 |])
  , (PyonName module_list "repr_barray2",
     Right [| pyonBuiltin SystemF.The_repr_barray2 |])
  , (PyonName module_list "repr_barray3",
     Right [| pyonBuiltin SystemF.The_repr_barray3 |])
  , (PyonName module_structures "repr_StoredBox",
     Right [| SystemF.pyonBuiltin SystemF.The_repr_StoredBox |])
  , (PyonName module_structures "repr_StuckRef",
     Right [| SystemF.pyonBuiltin SystemF.The_repr_StuckRef |])
  , (PyonName module_structures "repr_Box",
     Right [| SystemF.pyonBuiltin SystemF.The_repr_Box |])
  , (PyonName module_structures "repr_Stream",
     Right [| SystemF.pyonBuiltin SystemF.The_repr_Stream |])
  , (PyonName module_structures "repr_EmptyReference",
     Right [| SystemF.pyonBuiltin SystemF.The_repr_EmptyReference |])
  , (PyonName module_structures "repr_EffTok",
     Right [| SystemF.pyonBuiltin SystemF.The_repr_EffTok |])
  , (PyonName module_structures "repr_int",
     Right [| pyonBuiltin (SystemF.The_repr_int) |] )
  , (PyonName module_structures "repr_float",
     Right [| pyonBuiltin (SystemF.The_repr_float) |] )
  , (PyonName module_structures "repr_bool",
     Right [| pyonBuiltin (SystemF.The_repr_bool) |] )
    -- Streams
  , (PyonName module_stream "Stream_count",
     Right [| pyonBuiltin (SystemF.The_count) |])
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
