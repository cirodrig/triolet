
{-# LANGUAGE TemplateHaskell, FlexibleInstances #-}
module LowLevel.BuiltinsTH
where

import Language.Haskell.TH(Strict(..))
import Language.Haskell.TH.Syntax(Lift(..))

import Common.Error
import Common.Label
import Common.THRecord
import qualified Builtins.Builtins as SystemF
import qualified Type.Type as SystemF
import Builtins.Builtins(coreBuiltin)
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
  lift CursorType = [| CursorType |]

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
  | CoreName { builtinVarModuleName :: ModuleName 
             , builtinVarUnqualifiedName :: String
             }

instance Lift BuiltinVarName where
  lift (CName nm s) = [| CName nm s |]
  lift (CoreName nm s) = [| CoreName nm s |]

biName = CName builtinModuleName

applyName = CoreName (ModuleName "core.internal.apply_new")

-- | Predefined primitive functions
builtinPrimitives =
  [ -- C library functions
    (biName "exit",
     primFunctionType [PrimType nativeIntType] [])
    -- debug.c
  , (biName "triolet_db_int",
     primFunctionType [PrimType nativeIntType] [])
  , (biName "triolet_db_word",
     primFunctionType [PrimType nativeWordType] [])
  , (biName "triolet_db_pointer",
     primFunctionType [PrimType PointerType] [])
  , (biName "triolet_assert_nonnull_owned",
     primFunctionType [PrimType OwnedType] [])
    -- memory.c
  , (biName "triolet_alloc",
     primFunctionType [PrimType nativeWordType] [PrimType PointerType])
  , (biName "triolet_alloc_nopointers",
     primFunctionType [PrimType nativeWordType] [PrimType PointerType])
  , (biName "triolet_dealloc",
     primFunctionType [PrimType PointerType] [])
    -- prim.pyasm
  , (CoreName module_prim "min_fii",
     primFunctionType
     [RecordType finIndexedIntRecord, RecordType finIndexedIntRecord]
     [RecordType finIndexedIntRecord])
  , (CoreName module_prim "minus_fii",
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
  , (applyName "apply_i64_f",
     primFunctionType [ PrimType OwnedType
                      , PrimType (IntType Signed S64)] [PrimType OwnedType])
  , (applyName "apply_i64",
     primFunctionType [PrimType OwnedType
                      , PrimType (IntType Signed S64)
                      , PrimType PointerType] [])
  , (applyName "apply_f32_f",
     primFunctionType [ PrimType OwnedType
                      , PrimType (FloatType S32)] [PrimType OwnedType])
  , (applyName "apply_f32",
     primFunctionType [PrimType OwnedType
                      , PrimType (FloatType S32)
                      , PrimType PointerType] [])
  , (applyName "apply_p_f",
     primFunctionType [ PrimType OwnedType
                      , PrimType PointerType] [PrimType OwnedType])
  , (applyName "apply_p",
     primFunctionType [ PrimType OwnedType
                      , PrimType PointerType
                      , PrimType PointerType] [])
  , (applyName "apply_o_f",
     primFunctionType [ PrimType OwnedType
                      , PrimType OwnedType] [PrimType OwnedType])
  , (applyName "apply_o",
     primFunctionType [ PrimType OwnedType
                      , PrimType OwnedType
                      , PrimType PointerType] [])
  , (applyName "apply_c_f",
     primFunctionType [ PrimType OwnedType
                      , PrimType CursorType] [PrimType OwnedType])
  , (applyName "apply_c",
     primFunctionType [ PrimType OwnedType
                      , PrimType CursorType
                      , PrimType PointerType] [])
  
  , (CoreName module_lazy "force_Lazy",
     primFunctionType [PrimType PointerType,
                       PrimType nativeWordType,
                       PrimType nativeWordType] [])
  ]

closureBinaryFunctionType t = closureFunctionType [t, t] [t]

module_prim = ModuleName "core.internal.prim"
module_memory_py = ModuleName "core.internal.memory_py"
module_stream = ModuleName "core.internal.stream"
module_structures = ModuleName "core.internal.structures"
module_buffer = ModuleName "core.internal.buffer"
module_inplace = ModuleName "core.internal.inplace"
module_complex = ModuleName "core.internal.complex"
module_list = ModuleName "core.internal.list"
module_lazy = ModuleName "core.internal.lazy"

-- | Predefined closure functions and the core constructor they're derived
-- from.
builtinFunctions =
  [ (CoreName module_memory_py "blockcopy",
     Right [| coreBuiltin SystemF.The_blockcopy |])
  , (CoreName module_prim "read_int",
     Right [| coreBuiltin SystemF.The_read_int |])
  , (CoreName module_prim "write_int",
     Right [| coreBuiltin SystemF.The_write_int |])
  , (CoreName module_prim "read_int64",
     Right [| coreBuiltin SystemF.The_read_int64 |])
  , (CoreName module_prim "write_int64",
     Right [| coreBuiltin SystemF.The_write_int64 |])
  , (CoreName module_prim "read_float",
     Right [| coreBuiltin SystemF.The_read_float |])
  , (CoreName module_prim "write_float",
     Right [| coreBuiltin SystemF.The_write_float |])

  --, (CoreName module_prim "convertToBoxed",
  --  Right [| coreBuiltin (SystemF.The_asbox) |])
  --, (CoreName module_prim "convertToBare",
  --   Right [| coreBuiltin (SystemF.The_asbare) |])

{-  , (CoreName module_structures "makeComplex",
     Right [| coreBuiltin (SystemF.The_makeComplex) |]) -}
  --, (CoreName module_list "list_len",
  --   Right [| coreBuiltin SystemF.The_len |])
  --, (CoreName module_list "array1_build",
  --   Right [| coreBuiltin SystemF.The_Sequence_array1_build |])
  -- , (CoreName module_list "list_traverse",
  --   Right [| coreBuiltin SystemF.The_TraversableDict_list_traverse |])
  {- , (CoreName module_list "safeSubscript",
     Right [| coreBuiltin (SystemF.The_safeSubscript) |])
  , (CoreName module_list "list_generate",
     Right [| coreBuiltin (SystemF.The_fun_generateList) |])
  , (CoreName module_list "list_vGenerate",
     Right [| coreBuiltin (SystemF.The_fun_vectorGenerateList) |])
  , (CoreName module_stream "passConv_iter",
     Right [| coreBuiltin (SystemF.The_passConv_iter) |])
  , (CoreName module_stream "Stream_bind",
     Right [| coreBuiltin (SystemF.The_oper_CAT_MAP) |])
  , (CoreName module_stream "Stream_guard",
     Right [| coreBuiltin (SystemF.The_oper_GUARD) |])
  , (CoreName module_stream "Stream_return",
     Right [| coreBuiltin (SystemF.The_oper_DO) |])
  , (CoreName module_stream "Stream_empty",
     Right [| coreBuiltin (SystemF.The_oper_EMPTY) |])
  , (CoreName module_stream "Stream_asList",
     Right [| coreBuiltin (SystemF.The_fun_asList_Stream) |])    
  , (CoreName module_stream "generate",
     Right [| coreBuiltin (SystemF.The_generate) |])
  , (CoreName module_stream "Stream_map",
     Right [| coreBuiltin (SystemF.The_fun_map_Stream) |])
  , (CoreName module_stream "map",
     Right [| coreBuiltin (SystemF.The_fun_map) |])
  , (CoreName module_stream "Stream_reduce",
     Right [| coreBuiltin (SystemF.The_fun_reduce_Stream) |])
  , (CoreName module_stream "reduce",
     Right [| coreBuiltin (SystemF.The_fun_reduce) |])
  , (CoreName module_stream "Stream_reduce1",
     Right [| coreBuiltin (SystemF.The_fun_reduce1_Stream) |])
  , (CoreName module_stream "reduce1",
     Right [| coreBuiltin (SystemF.The_fun_reduce1) |])
  , (CoreName module_stream "Stream_fold",
     Right [| coreBuiltin (SystemF.The_fun_fold_Stream) |])
  , (CoreName module_stream "Stream_zip",
     Right [| coreBuiltin (SystemF.The_fun_zip_Stream) |])
  , (CoreName module_stream "Stream_zip3",
     Right [| coreBuiltin (SystemF.The_fun_zip3_Stream) |])
  , (CoreName module_stream "Stream_zip4",
     Right [| coreBuiltin (SystemF.The_fun_zip4_Stream) |])
  , (CoreName module_stream "zip",
     Right [| coreBuiltin (SystemF.The_fun_zip) |])
  , (CoreName module_stream "zip3",
     Right [| coreBuiltin (SystemF.The_fun_zip3) |])
  , (CoreName module_stream "zip4",
     Right [| coreBuiltin (SystemF.The_fun_zip4) |])
  , (CoreName module_stream "Stream_build",
     Right [| coreBuiltin (SystemF.The_TraversableDict_Stream_build) |])
  , (CoreName module_stream "Stream_traverse",
     Right [| coreBuiltin (SystemF.The_TraversableDict_Stream_traverse) |])
  , (CoreName module_stream "Stream_range",
     Right [| coreBuiltin (SystemF.The_range) |])
  , (CoreName module_stream "Stream_rangeIndexed",
     Right [| coreBuiltin (SystemF.The_rangeIndexed) |])
  , (CoreName module_stream "histogram",
     Right [| coreBuiltin (SystemF.The_histogram) |])-}
  , (CoreName module_inplace "append_build_list",
     Right [| coreBuiltin SystemF.The_append_build_list |])
  {-, (CoreName module_inplace "repr_append_list",
     Right [| coreBuiltin SystemF.The_repr_append_list |])-}
  {-, (CoreName module_inplace "intSumScatter_make_init",
     Right [| coreBuiltin (SystemF.The_intSumScatter_make_init) |])
  , (CoreName module_inplace "countingScatter_make_init",
     Right [| coreBuiltin (SystemF.The_countingScatter_make_init) |])
  , (CoreName module_inplace "intUpdateInPlace_initializer",
     Right [| coreBuiltin (SystemF.The_intUpdateInPlace_initializer) |])
  , (CoreName module_inplace "intUpdateInPlace_updater",
     Right [| coreBuiltin (SystemF.The_intUpdateInPlace_updater) |])
  , (CoreName module_inplace "floatSumScatter_make_init",
     Right [| coreBuiltin (SystemF.The_floatSumScatter_make_init) |])
  , (CoreName module_inplace "floatUpdateInPlace_initializer",
     Right [| coreBuiltin (SystemF.The_floatUpdateInPlace_initializer) |])
  , (CoreName module_inplace "floatUpdateInPlace_updater",
     Right [| coreBuiltin (SystemF.The_floatUpdateInPlace_updater) |])
  , (CoreName module_inplace "boolUpdateInPlace_initializer",
     Right [| coreBuiltin (SystemF.The_boolUpdateInPlace_initializer) |])
  , (CoreName module_inplace "boolUpdateInPlace_updater",
     Right [| coreBuiltin (SystemF.The_boolUpdateInPlace_updater) |])
  , (CoreName module_inplace "boxedScatter_updater",
     Right [| coreBuiltin (SystemF.The_boxedScatter_updater) |])
  , (CoreName module_inplace "appendScatter_initializer",
     Right [| coreBuiltin (SystemF.The_appendScatter_initializer) |])
  , (CoreName module_inplace "appendScatter_update_real",
     Right [| coreBuiltin (SystemF.The_appendScatter_update_real) |])-}
  , (CoreName module_inplace "compute_hash_table_size",
     Right [| coreBuiltin (SystemF.The_compute_hash_table_size) |])
  , (CoreName module_inplace "build_hash_table",
     Right [| coreBuiltin (SystemF.The_build_hash_table) |])
  , (CoreName module_inplace "lookup_hash_table",
     Right [| coreBuiltin (SystemF.The_lookup_hash_table) |])

  , (CoreName module_buffer "putInt",
     Right [| SystemF.putIntV |])
  , (CoreName module_buffer "putUint",
     Right [| SystemF.putUintV |])
  , (CoreName module_buffer "putUintAsUint8",
     Right [| SystemF.putUintAsUint8V |])
  , (CoreName module_buffer "putUintAsUint16",
     Right [| SystemF.putUintAsUint16V |])
  , (CoreName module_buffer "putFloat",
     Right [| SystemF.putFloatV |])
  , (CoreName module_buffer "putUnit",
     Left (closureFunctionType
           [PrimType UnitType, PrimType OwnedType, PrimType UnitType]
           [PrimType UnitType]))
  , (CoreName module_buffer "putCursor",
     Right [| SystemF.putCursorV |])
  , (CoreName module_buffer "putBoxedObject",
     Right [| SystemF.putBoxedObjectV |])
  , (CoreName module_buffer "putStoredInt",
     Right [| SystemF.putStoredIntV |])
  , (CoreName module_buffer "putStoredUint",
     Right [| SystemF.putStoredUintV |])
  , (CoreName module_buffer "putStoredFloat",
     Right [| SystemF.putStoredFloatV |])
  , (CoreName module_buffer "putStoredByte",
     Right [| SystemF.putStoredByteV |])
  , (CoreName module_buffer "putStoredInt64",
     Right [| SystemF.putStoredInt64V |])
  , (CoreName module_buffer "putStoredCursor",
     Right [| SystemF.putStoredCursorV |])
  , (CoreName module_buffer "putArrWithSerializer",
     Right [| coreBuiltin SystemF.The_putArrWithSerializer |])
  , (CoreName module_buffer "putListSection_low_level",
     Right [| coreBuiltin SystemF.The_putListSection_low_level |])
  , (CoreName module_buffer "getListSection_low_level",
     Right [| coreBuiltin SystemF.The_getListSection_low_level |])
  , (CoreName module_buffer "getInt",
     Right [| SystemF.getIntV |])
  , (CoreName module_buffer "getUint",
     Right [| SystemF.getUintV |])
  , (CoreName module_buffer "getUint8AsUint",
     Right [| SystemF.getUint8AsUintV |])
  , (CoreName module_buffer "getUint16AsUint",
     Right [| SystemF.getUint16AsUintV |])
  , (CoreName module_buffer "getFloat",
     Right [| SystemF.getFloatV |])
  , (CoreName module_buffer "getUnit",
     Left (closureFunctionType
           [PrimType OwnedType, PrimType CursorType]
           [RecordType $ constStaticRecord [PrimField CursorType, PrimField UnitType]]))
  , (CoreName module_buffer "getCursor",
     Right [| SystemF.getCursorV |])
  , (CoreName module_buffer "getBoxedObject",
     Right [| SystemF.getBoxedObjectV |])
  , (CoreName module_buffer "getStoredInt",
     Right [| SystemF.getStoredIntV |])
  , (CoreName module_buffer "getStoredUint",
     Right [| SystemF.getStoredUintV |])
  , (CoreName module_buffer "getStoredFloat",
     Right [| SystemF.getStoredFloatV |])
  , (CoreName module_buffer "getStoredByte",
     Right [| SystemF.getStoredByteV |])
  , (CoreName module_buffer "getStoredInt64",
     Right [| SystemF.getStoredInt64V |])
  , (CoreName module_buffer "getStoredCursor",
     Right [| SystemF.getStoredCursorV |])
  , (CoreName module_buffer "getArrWithSerializer",
     Right [| coreBuiltin SystemF.The_getArrWithSerializer |])
  , (CoreName module_buffer "testCopyViaBuffer",
     Right [| coreBuiltin SystemF.The_testCopyViaBuffer |])
  , (CoreName module_buffer "updateDeserializationTable",
     Left (closureFunctionType
           [PrimType OwnedType, PrimType OwnedType]
           [PrimType UnitType]))
    
  , (CoreName module_prim "seqStore",
     Right [| coreBuiltin (SystemF.The_seqStore) |])
  {-, (CoreName module_structures "repr_arr",
     Right [| SystemF.coreBuiltin SystemF.The_repr_arr |])-}
  --, (CoreName module_structures "repr_Referenced",
    --Right [| SystemF.coreBuiltin SystemF.The_repr_Referenced |])
  {-, (CoreName module_structures "repr_Maybe",
     Right [| SystemF.coreBuiltin SystemF.The_repr_Maybe |])
  , (CoreName module_structures "repr_Tuple1",
     Right [| SystemF.coreBuiltin SystemF.The_repr_Tuple1 |])
  , (CoreName module_structures "repr_Tuple2",
     Right [| SystemF.coreBuiltin SystemF.The_repr_Tuple2 |])
  , (CoreName module_structures "repr_Tuple3",
     Right [| SystemF.coreBuiltin SystemF.The_repr_Tuple3 |])
  , (CoreName module_structures "repr_Tuple4",
     Right [| SystemF.coreBuiltin SystemF.The_repr_Tuple4 |])
  , (CoreName module_structures "sizealign_Tuple2",
     Right [| SystemF.coreBuiltin SystemF.The_sizealign_Tuple2 |])
  , (CoreName module_structures "sizealign_Tuple3",
     Right [| SystemF.coreBuiltin SystemF.The_sizealign_Tuple3 |])
  , (CoreName module_structures "sizealign_Tuple4",
     Right [| SystemF.coreBuiltin SystemF.The_sizealign_Tuple4 |])-}
  {-, (CoreName module_structures "sizealign_arr",
     Right [| SystemF.coreBuiltin SystemF.The_sizealign_arr |])-}
  
  , (CoreName module_prim "makeIdCoercion",
     Right [| coreBuiltin SystemF.The_makeIdCoercion |])
  , (CoreName module_prim "makeIdBareCoercion",
     Right [| coreBuiltin SystemF.The_makeIdBareCoercion |])
  , (CoreName module_prim "preserve",
     Right [| coreBuiltin SystemF.The_preserve |])
  , (CoreName module_prim "traceInt_int",
     Right [| coreBuiltin (SystemF.The_traceInt_int) |])
  , (CoreName module_prim "traceInt_box",
     Right [| coreBuiltin (SystemF.The_traceInt_box) |])
  , (CoreName module_prim "defineIntIndex",
     Right [| coreBuiltin (SystemF.The_defineIntIndex) |])
  , (CoreName module_prim "fromCursor",
     Right [| coreBuiltin (SystemF.The_fromCursor) |])
  , (CoreName module_prim "toCursor",
     Right [| coreBuiltin (SystemF.The_toCursor) |])
  , (CoreName module_prim "subscript",
     Right [| coreBuiltin (SystemF.The_subscript) |])
  , (CoreName module_prim "subscript_out",
     Right [| coreBuiltin (SystemF.The_subscript_out) |])
  , (CoreName module_prim "subarray",
     Right [| coreBuiltin (SystemF.The_subarray) |])
  , (CoreName module_prim "subarray_out",
     Right [| coreBuiltin (SystemF.The_subarray_out) |])
  , (CoreName module_prim "min_ii",
     Right [| coreBuiltin (SystemF.The_min_ii) |])
  , (CoreName module_prim "minus_ii",
     Right [| coreBuiltin (SystemF.The_minus_ii) |])
  , (CoreName module_prim "not",
     Right [| coreBuiltin (SystemF.The_not) |])
  , (CoreName module_prim "gcd",
     Right [| coreBuiltin (SystemF.The_gcd) |])
  , (CoreName module_prim "extgcd_x",
     Right [| coreBuiltin (SystemF.The_extgcd_x) |])
  , (CoreName module_prim "getNumDistributedPlaces",
     Right [| coreBuiltin (SystemF.The_getNumDistributedPlaces) |])
  , (CoreName module_prim "inDistributedTask",
     Right [| coreBuiltin (SystemF.The_inDistributedTask) |])

  , (CoreName module_prim "farm",
     Right [| coreBuiltin (SystemF.The_farm) |])
  , (CoreName module_prim "doall",
     Right [| coreBuiltin (SystemF.The_doall) |])
  , (CoreName module_prim "doall_mutable",
     Right [| coreBuiltin (SystemF.The_doall_mutable) |])
  --, (CoreName module_prim "for",
  --   Right [| coreBuiltin (SystemF.The_for) |])
  --, (CoreName module_prim "blocked_1d_reduce",
  --   Right [| coreBuiltin (SystemF.The_blocked_1d_reduce) |])
  --, (CoreName module_prim "blocked_2d_reduce",
  --   Right [| coreBuiltin (SystemF.The_blocked_2d_reduce) |])
  --, (CoreName module_prim "blocked_1d_reduceip",
  --   Right [| coreBuiltin (SystemF.The_blocked_1d_reduceip) |])
  , (CoreName module_prim "blocked_doall",
     Right [| coreBuiltin (SystemF.The_blocked_doall) |])
  , (CoreName module_prim "blocked_doall2",
     Right [| coreBuiltin (SystemF.The_blocked_doall2) |])
  , (CoreName module_prim "blocked_greduce",
     Right [| coreBuiltin (SystemF.The_blocked_greduce) |])    
  , (CoreName module_prim "static_greduce",
     Right [| coreBuiltin (SystemF.The_static_greduce) |])    
  , (CoreName module_prim "blocked_PBTree_doall",
     Right [| coreBuiltin (SystemF.The_blocked_PBTree_doall) |])

    -- Functions that are replaced by primitive operations
  , (CoreName module_prim "eq_int",
     Right [| coreBuiltin (SystemF.The_eqI) |])
  , (CoreName module_prim "ne_int",
     Right [| coreBuiltin (SystemF.The_neI) |])
  , (CoreName module_prim "eq_int64",
     Right [| coreBuiltin (SystemF.The_eqI64) |])
  , (CoreName module_prim "ne_int64",
     Right [| coreBuiltin (SystemF.The_neI64) |])
  , (CoreName module_prim "eq_float",
     Right [| coreBuiltin (SystemF.The_eqF) |])
  , (CoreName module_prim "ne_float",
     Right [| coreBuiltin (SystemF.The_neF) |])
  , (CoreName module_prim "lt_int",
     Right [| coreBuiltin SystemF.The_ltI |])
  , (CoreName module_prim "le_int",
     Right [| coreBuiltin SystemF.The_leI |])
  , (CoreName module_prim "gt_int",
     Right [| coreBuiltin SystemF.The_gtI |])
  , (CoreName module_prim "ge_int",
     Right [| coreBuiltin SystemF.The_geI |])
  , (CoreName module_prim "lt_int64",
     Right [| coreBuiltin SystemF.The_ltI64 |])
  , (CoreName module_prim "le_int64",
     Right [| coreBuiltin SystemF.The_leI64 |])
  , (CoreName module_prim "gt_int64",
     Right [| coreBuiltin SystemF.The_gtI64 |])
  , (CoreName module_prim "ge_int64",
     Right [| coreBuiltin SystemF.The_geI64 |])
  , (CoreName module_prim "lt_float",
     Right [| coreBuiltin SystemF.The_ltF |])
  , (CoreName module_prim "le_float",
     Right [| coreBuiltin SystemF.The_leF |])
  , (CoreName module_prim "gt_float",
     Right [| coreBuiltin SystemF.The_gtF |])
  , (CoreName module_prim "ge_float",
     Right [| coreBuiltin SystemF.The_geF |])
    -- the_AdditiveDict_int_{add,sub} were replaced by intrinsics
  , (CoreName module_prim "negate_int",
     Right [| coreBuiltin (SystemF.The_negI) |])
  , (CoreName module_prim "negate_int64",
     Right [| coreBuiltin (SystemF.The_negI64) |])
    -- zero_int was replaced by a literal value
    -- the_AdditiveDict_float_{add,sub} were replaced by intrinsics
  , (CoreName module_prim "negate_float",
     Right [| coreBuiltin (SystemF.The_negF) |])
    -- zero_float was replaced by a literal value
  , (CoreName module_prim "fromint_float",
     Right [| coreBuiltin (SystemF.The_fromintF) |])
  , (CoreName module_prim "mod_int",
     Right [| coreBuiltin SystemF.The_modI |])
  , (CoreName module_prim "floordiv_int",
     Right [| coreBuiltin SystemF.The_floordivI |])
  , (CoreName module_prim "mod_float",
     Right [| coreBuiltin SystemF.The_modF |])
  , (CoreName module_prim "floordiv_float",
     Right [| coreBuiltin SystemF.The_floordivF |])
  , (CoreName module_prim "div_float",
     Right [| coreBuiltin SystemF.The_divF |])
    -- one_float was replaced by a literal value
{-  , (CoreName builtinModuleName "load_int",
     Right [| coreBuiltin (SystemF.The_fun_load_int) |])
  , (CoreName builtinModuleName "load_float",
     Right [| coreBuiltin (SystemF.The_fun_load_float) |])
  , (CoreName module_prim "load_complexFloat",
     Right [| coreBuiltin SystemF.The_fun_load_complexFloat |])
  , (CoreName builtinModuleName "load_bool",
     Right [| coreBuiltin (SystemF.The_fun_load_bool) |])
  , (CoreName builtinModuleName "load_NoneType",
     Right [| coreBuiltin (SystemF.The_fun_load_NoneType) |])
  , (CoreName builtinModuleName "store_int",
     Right [| coreBuiltin (SystemF.The_fun_store_int) |])
  , (CoreName builtinModuleName "store_float",
     Right [| coreBuiltin (SystemF.The_fun_store_float) |])
  , (CoreName module_prim "store_complexFloat",
     Right [| coreBuiltin SystemF.The_fun_store_complexFloat |])
  , (CoreName builtinModuleName "store_bool",
     Right [| coreBuiltin (SystemF.The_fun_store_bool) |])
  , (CoreName builtinModuleName "store_NoneType",
     Right [| coreBuiltin (SystemF.The_fun_store_NoneType) |])-}
  ]

-- | Predefined global data
builtinGlobals =
  [ -- Info tables
    (biName "pap_info",
     Left $ PrimType PointerType)
  , (biName "global_closure_info",
     Left $ PrimType PointerType)
  , (CName module_structures "triolet_typeObject_function",
     Left $ PrimType OwnedType)

    -- Physical representations of data types
  , (CoreName module_structures "typeObject_typeObject",
     Right [| SystemF.boxInfo_boxInfoV |])
  {-, (CoreName module_structures "typeObject_repr",
     Right [| SystemF.boxInfo_bareInfoV |])-}
  {-, (CoreName module_list "repr_list",
     Right [| coreBuiltin SystemF.The_repr_list |])
  , (CoreName module_list "repr_array0",
     Right [| coreBuiltin SystemF.The_repr_array0 |])
  , (CoreName module_list "repr_array1",
     Right [| coreBuiltin SystemF.The_repr_array1 |])
  , (CoreName module_list "repr_array2",
     Right [| coreBuiltin SystemF.The_repr_array2 |])
  , (CoreName module_list "repr_array3",
     Right [| coreBuiltin SystemF.The_repr_array3 |])
  , (CoreName module_list "repr_barray1",
     Right [| coreBuiltin SystemF.The_repr_barray1 |])
  , (CoreName module_list "repr_barray2",
     Right [| coreBuiltin SystemF.The_repr_barray2 |])
  , (CoreName module_list "repr_barray3",
     Right [| coreBuiltin SystemF.The_repr_barray3 |])
  , (CoreName module_structures "repr_Ref",
     Right [| SystemF.coreBuiltin SystemF.The_repr_Ref |])
  , (CoreName module_structures "repr_StuckRef",
     Right [| SystemF.coreBuiltin SystemF.The_repr_StuckRef |])
  , (CoreName module_structures "repr_Box",
     Right [| SystemF.coreBuiltin SystemF.The_repr_Box |])
  , (CoreName module_structures "repr_intset",
     Right [| coreBuiltin (SystemF.The_repr_intset) |] )
  , (CoreName module_structures "repr_Stream",
     Right [| SystemF.coreBuiltin SystemF.The_repr_Stream |])
  , (CoreName module_structures "repr_EmptyReference",
     Right [| SystemF.coreBuiltin SystemF.The_repr_EmptyReference |])
  , (CoreName module_structures "repr_int",
     Right [| coreBuiltin (SystemF.The_repr_int) |] )
  , (CoreName module_structures "repr_uint",
     Right [| coreBuiltin (SystemF.The_repr_uint) |] )
  , (CoreName module_structures "repr_float",
     Right [| coreBuiltin (SystemF.The_repr_float) |] )
  , (CoreName module_structures "repr_bool",
     Right [| coreBuiltin (SystemF.The_repr_bool) |] )
  , (CoreName module_structures "repr_NoneType",
     Right [| coreBuiltin (SystemF.The_repr_NoneType) |] )-}
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
