
{-# LANGUAGE TemplateHaskell #-}
module Builtins.BuiltinsTH where
       
builtinTypeNames =
  [ "bool"
  , "int"
  , "uint"
  , "float"
  , "Complex"
  , "list"
  , "append_list"
  , "ListBuilder"
  , "OpaqueRef"
  , "blist"
  , "array0"
  , "array1"
  , "array2"
  , "array3"
  , "barray1"
  , "barray2"
  , "barray3"
  , "llist"
  , "view"
  , "NoneType"
  , "Maybe"
  , "MaybeVal"
  , "Any"
  , "Interval"
  , "LinearMap"
  , "SliceObject"
  , "InternalSlice"             -- TODO: remove this type
  , "Tuple0"
  , "Tuple1"
  , "Tuple2"
  , "Tuple3"
  , "Tuple4"
  , "intset"
  , "Stream"
  , "Stream1"
  , "Sequence"
  , "StreamNext"
  , "BindState"
  , "ChainState"
  , "FIInt"
  , "IInt"
  , "SomeIInt"
  , "arr"
  , "EffTok"
  , "Pf"
  , "UpdateInPlaceFinalizer"
  , "Scatter"
  , "PBTree"

    -- Representation coercions
  , "Stored"
  , "Ref"
  , "StuckRef"
  , "StuckBox"
  , "Boxed"
  , "OutPtr"
  , "Store"
  , "Init"
  , "BoxedType"
  , "BareType"
    
    -- Container type functions
  , "cartesianDomain"
  , "index"
  , "slice"
  , "array"
    
    -- Shape-related types
  , "shape"
  , "list_dim"
  , "dim0"
  , "dim1"
  , "dim2"
  , "dim3"
  , "arr_shape"

    -- Integer type indices
  , "plus_i"
  , "minus_i"
  , "min_i"
  , "max_i"
    
    -- Propositions
  , "eqZ"
  , "neZ"
  , "trueP"

    -- Dictionary types
  , "SizeAlign"
  , "SizeAlignVal"
  , "Repr"
  , "TraversableDict"
  , "ShapeDict"
  , "IndexableDict"
  , "EqDict"
  , "OrdDict"
  , "AdditiveDict"
  , "MultiplicativeDict"
  , "RemainderDict"
  , "FractionalDict"
  , "FloatingDict"
  , "VectorDict"
  , "CartesianDict"
  ]

builtinVariableNames =
  [ -- Data constructors
    "True"
  , "False"
  , "None"
  , "complex"
  , "interval"
  , "linearMap"
  , "sliceObject"
  , "internalSlice"             -- TODO: Remove this object
  , "emptySlice"                -- TODO: Remove this object
  , "tuple0"
  , "tuple1"
  , "tuple2"
  , "tuple3"
  , "tuple4"
  , "just"
  , "nothing"
  , "justVal"
  , "nothingVal"
  , "stored"
  , "ref"
  , "stuckRef"
  , "stuckBox"
  , "boxed"
  , "store"
  , "fiInt"
  , "iInt"
  , "iPosInfty"
  , "iNegInfty"
  , "someIInt"
  , "sequenceStream"
  , "viewStream"
  , "sequence"
  , "streamEmpty"
  , "streamValue"
  , "bindFromSource"
  , "bindFromTrans"
  , "chainFromFirst"
  , "chainFromNext"
  , "make_list"
  , "make_append_list"
  , "listBuilder"
  , "mk_array0"
  , "mk_array1"
  , "mk_array2"
  , "mk_array3"
  , "make_blist"
  , "mk_barray1"
  , "mk_barray2"
  , "mk_barray3"
  , "cons"
  , "nil"
  , "mk_view"
  , "effTok"
  , "pf"
  , "mk_list_dim"
  , "mk_dim0"
  , "mk_dim1"
  , "mk_dim2"
  , "mk_dim3"
  , "mk_arr_shape"
  , "mutateInPlace"
  , "mutateAndCopy"
  , "mk_scatter"
  , "pbBranch"
  , "pbLeaf"
  , "pbEmpty"

    -- Class constructors
  , "sizeAlign"
  , "sizeAlignVal"
  , "repr"
  , "traversableDict"
  , "shapeDict"
  , "indexableDict"
  , "eqDict"
  , "ordDict"
  , "additiveDict"
  , "multiplicativeDict"
  , "remainderDict"
  , "fractionalDict"
  , "floatingDict"
  , "vectorDict"
  , "cartesianDict"

    -- Class instances
  , "repr_bool"
  , "repr_int"
  , "repr_uint"
  , "repr_float"
  , "repr_MaybeVal_int"
  , "repr_MaybeVal_MaybeVal_int"
  , "repr_list_dim"
  , "repr_dim0"
  , "repr_dim1"
  , "repr_dim2"
  , "repr_dim3"
  , "repr_index2"
  , "repr_slice2"
  , "repr_index3"
  , "repr_slice3"
  , "repr_Complex"
  , "repr_list"
  , "repr_append_list"
  , "repr_ListBuilder"
  , "repr_array0"
  , "repr_array1"
  , "repr_array2"
  , "repr_array3"
  , "repr_blist"
  , "repr_barray1"
  , "repr_barray2"
  , "repr_barray3"
  , "repr_llist"
  , "repr_NoneType"
  , "repr_Any"
  , "repr_Ref"
  , "repr_StuckRef"
  , "repr_Box"
  , "repr_Stream"
  , "repr_Scatter"
  , "repr_view"
  , "repr_Maybe"
  , "repr_EmptyReference"
  , "repr_Coercion"
  , "repr_arr"
  , "repr_arr_2"
  , "repr_EffTok"
  , "repr_SliceObject"
  , "repr_Tuple0"
  , "repr_Tuple1"
  , "repr_Tuple2"
  , "repr_Tuple3"
  , "repr_Tuple4"
  , "repr_intset"
  , "sizealign_int"
  , "sizealign_uint"
  , "sizealign_float"
  , "sizealign_bool"
  , "sizealign_NoneType"
  , "sizealign_Tuple2"
  , "sizealign_Tuple3"
  , "sizealign_Tuple4"
  , "sizealign_ListBuilder"
  , "ShapeDict_list_dim"
  , "ShapeDict_dim0"
  , "ShapeDict_dim1"
  , "ShapeDict_dim2"
  , "ShapeDict_dim3"
  , "TraversableDict_Stream_traverse"
  , "TraversableDict_Stream_build"
  , "TraversableDict_llist_traverse"
  , "TraversableDict_llist_build"
  , "TraversableDict_view_list_dim_traverse"
  , "TraversableDict_view_list_dim_build"
  , "TraversableDict_view_dim0_traverse"
  , "TraversableDict_view_dim0_build"
  , "TraversableDict_view_dim1_traverse"
  , "TraversableDict_view_dim1_build"
  , "TraversableDict_view_dim2_traverse"
  , "TraversableDict_view_dim2_build"
  , "TraversableDict_view_dim3_traverse"
  , "TraversableDict_view_dim3_build"
  , "TraversableDict_list_traverse"
  , "TraversableDict_list_build"
  , "TraversableDict_array0_traverse"
  , "TraversableDict_array0_build"
  , "TraversableDict_array1_traverse"
  , "TraversableDict_array1_build"
  , "TraversableDict_array2_traverse"
  , "TraversableDict_array2_build"
  , "TraversableDict_array3_traverse"
  , "TraversableDict_array3_build"
  , "TraversableDict_blist_traverse"
  , "TraversableDict_blist_build"
  , "TraversableDict_barray1_traverse"
  , "TraversableDict_barray1_build"
  , "TraversableDict_barray2_traverse"
  , "TraversableDict_barray2_build"
  , "TraversableDict_barray3_traverse"
  , "TraversableDict_barray3_build"
  , "ShapeDict_list_dim_member"
  , "ShapeDict_list_dim_intersect"
  , "ShapeDict_list_dim_generate"
  , "ShapeDict_list_dim_flatten"
  , "ShapeDict_list_dim_map"
  , "ShapeDict_list_dim_zipWith"
  , "ShapeDict_list_dim_zipWith3"
  , "ShapeDict_list_dim_zipWith4"
  , "ShapeDict_list_dim_slice"
  , "ShapeDict_dim0_member"
  , "ShapeDict_dim0_intersect"
  , "ShapeDict_dim0_generate"
  , "ShapeDict_dim0_flatten"
  , "ShapeDict_dim0_map"
  , "ShapeDict_dim0_zipWith"
  , "ShapeDict_dim0_zipWith3"
  , "ShapeDict_dim0_zipWith4"
  , "ShapeDict_dim0_slice"
  , "ShapeDict_dim1_member"
  , "ShapeDict_dim1_intersect"
  , "ShapeDict_dim1_generate"
  , "ShapeDict_dim1_flatten"
  , "ShapeDict_dim1_map"
  , "ShapeDict_dim1_zipWith"
  , "ShapeDict_dim1_zipWith3"
  , "ShapeDict_dim1_zipWith4"
  , "ShapeDict_dim1_slice"
  , "ShapeDict_dim2_member"
  , "ShapeDict_dim2_intersect"
  , "ShapeDict_dim2_generate"
  , "ShapeDict_dim2_flatten"
  , "ShapeDict_dim2_flatten_helper"
  , "ShapeDict_dim2_flatten_helper2"
  , "ShapeDict_dim2_map"
  , "ShapeDict_dim2_zipWith"
  , "ShapeDict_dim2_zipWith3"
  , "ShapeDict_dim2_zipWith4"
  , "ShapeDict_dim2_slice"
  , "ShapeDict_dim3_member"
  , "ShapeDict_dim3_intersect"
  , "ShapeDict_dim3_generate"
  , "ShapeDict_dim3_flatten"
  , "ShapeDict_dim3_flatten_helper"
  , "ShapeDict_dim3_flatten_helper2"
  , "ShapeDict_dim3_map"
  , "ShapeDict_dim3_zipWith"
  , "ShapeDict_dim3_zipWith3"
  , "ShapeDict_dim3_zipWith4"
  , "ShapeDict_dim3_slice"
  , "IndexableDict_list_at_point"
  , "IndexableDict_list_get_shape"
  , "IndexableDict_view_at_point"
  , "IndexableDict_view_get_shape"
  , "IndexableDict_array0_at_point"
  , "IndexableDict_array0_get_shape"
  , "IndexableDict_array1_at_point"
  , "IndexableDict_array1_get_shape"
  , "IndexableDict_array2_at_point"
  , "IndexableDict_array2_get_shape"
  , "IndexableDict_array3_at_point"
  , "IndexableDict_array3_get_shape"
  , "IndexableDict_blist_at_point"
  , "IndexableDict_blist_get_shape"
  , "IndexableDict_barray1_at_point"
  , "IndexableDict_barray1_get_shape"
  , "IndexableDict_barray2_at_point"
  , "IndexableDict_barray2_get_shape"
  , "IndexableDict_barray3_at_point"
  , "IndexableDict_barray3_get_shape"
  , "EqDict_int"
  , "EqDict_int_eq"
  , "EqDict_int_ne"
  , "EqDict_float"
  , "EqDict_float_eq"
  , "EqDict_float_ne"
  , "EqDict_Tuple2"
  , "EqDict_Tuple2_eq"
  , "EqDict_Tuple2_ne"
  , "EqDict_Tuple3"
  , "EqDict_Tuple3_eq"
  , "EqDict_Tuple3_ne"
  , "OrdDict_int"
  , "OrdDict_int_lt"
  , "OrdDict_int_le"
  , "OrdDict_int_gt"
  , "OrdDict_int_ge"
  , "OrdDict_float"
  , "OrdDict_float_lt"
  , "OrdDict_float_le"
  , "OrdDict_float_gt"
  , "OrdDict_float_ge"
  , "OrdDict_Tuple2"
  , "OrdDict_Tuple2_lt"
  , "OrdDict_Tuple2_le"
  , "OrdDict_Tuple2_gt"
  , "OrdDict_Tuple2_ge"
  , "AdditiveDict_int"
  , "AdditiveDict_int_add"
  , "AdditiveDict_int_sub"
  , "AdditiveDict_int_negate"
  , "AdditiveDict_int_zero"
  , "AdditiveDict_uint"
  , "AdditiveDict_uint_add"
  , "AdditiveDict_uint_sub"
  , "AdditiveDict_uint_negate"
  , "AdditiveDict_uint_zero"
  , "AdditiveDict_float"
  , "AdditiveDict_float_add"
  , "AdditiveDict_float_sub"
  , "AdditiveDict_float_negate"
  , "AdditiveDict_float_zero"
  , "AdditiveDict_Tuple2_add"
  , "AdditiveDict_Tuple2_sub"
  , "AdditiveDict_Tuple2_negate"
  , "AdditiveDict_Tuple2_zero"
  , "MultiplicativeDict_int"
  , "MultiplicativeDict_int_mul"
  , "MultiplicativeDict_int_fromInt"
  , "MultiplicativeDict_int_one"
  , "MultiplicativeDict_uint"
  , "MultiplicativeDict_uint_mul"
  , "MultiplicativeDict_uint_fromInt"
  , "MultiplicativeDict_uint_one"
  , "MultiplicativeDict_float"
  , "MultiplicativeDict_float_mul"
  , "MultiplicativeDict_float_fromInt"
  , "MultiplicativeDict_float_one"
  , "RemainderDict_int_floordiv"
  , "RemainderDict_int_mod"
  , "RemainderDict_uint_floordiv"
  , "RemainderDict_uint_mod"
  , "RemainderDict_float_floordiv"
  , "RemainderDict_float_mod"
  , "FractionalDict_float_div"
  , "FloatingDict_float_fromfloat"
  , "FloatingDict_float_power"
  , "FloatingDict_float_exp"
  , "FloatingDict_float_log"
  , "FloatingDict_float_sqrt"
  , "FloatingDict_float_sin"
  , "FloatingDict_float_cos"
  , "FloatingDict_float_tan"
  , "FloatingDict_float_pi"
  {-, "FloatingDict_Complex_fromfloat"
  , "FloatingDict_Complex_power"
  , "FloatingDict_Complex_exp"
  , "FloatingDict_Complex_log"
  , "FloatingDict_Complex_sqrt"
  , "FloatingDict_Complex_sin"
  , "FloatingDict_Complex_cos"
  , "FloatingDict_Complex_tan"
  , "FloatingDict_Complex_pi"-}
  , "VectorDict_float_scale"
  , "VectorDict_float_magnitude"
  , "VectorDict_float_dot"
  {-, "VectorDict_Complex_scale"
  , "VectorDict_Complex_magnitude"
  , "VectorDict_Complex_dot"-}
  , "CartesianDict_dim0_loBound"
  , "CartesianDict_dim0_hiBound"
  , "CartesianDict_dim0_stride"
  , "CartesianDict_dim0_arrayDomain"
  , "CartesianDict_dim0_displaceDomain"
  , "CartesianDict_dim0_multiplyDomain"
  , "CartesianDict_dim0_divideDomain"
  , "CartesianDict_dim0_multiplyIndex"
  , "CartesianDict_dim0_divideIndex"
  , "CartesianDict_dim0_unbounded"
  , "CartesianDict_dim1_loBound"
  , "CartesianDict_dim1_hiBound"
  , "CartesianDict_dim1_stride"
  , "CartesianDict_dim1_arrayDomain"
  , "CartesianDict_dim1_displaceDomain"
  , "CartesianDict_dim1_multiplyDomain"
  , "CartesianDict_dim1_divideDomain"
  , "CartesianDict_dim1_multiplyIndex"
  , "CartesianDict_dim1_divideIndex"
  , "CartesianDict_dim1_unbounded"
  , "CartesianDict_dim2_loBound"
  , "CartesianDict_dim2_hiBound"
  , "CartesianDict_dim2_stride"
  , "CartesianDict_dim2_arrayDomain"
  , "CartesianDict_dim2_displaceDomain"
  , "CartesianDict_dim2_multiplyDomain"
  , "CartesianDict_dim2_divideDomain"
  , "CartesianDict_dim2_multiplyIndex"
  , "CartesianDict_dim2_divideIndex"
  , "CartesianDict_dim2_unbounded"
  , "CartesianDict_dim3_loBound"
  , "CartesianDict_dim3_hiBound"
  , "CartesianDict_dim3_stride"
  , "CartesianDict_dim3_arrayDomain"
  , "CartesianDict_dim3_displaceDomain"
  , "CartesianDict_dim3_multiplyDomain"
  , "CartesianDict_dim3_divideDomain"
  , "CartesianDict_dim3_multiplyIndex"
  , "CartesianDict_dim3_divideIndex"
  , "CartesianDict_dim3_unbounded"
    
    -- Constructor-like functions
  , "create_view2"
  , "fun_list_dim"
  , "fun_dim1"
  , "make_sliceObject"

    -- Pseudo-dictionary methods inserted by optimizations
  , "arr1D_build"
  , "arr2D_build"
  , "arr3D_build"
  , "view_generate"
  , "view_map"
  , "view_zipWith"
  , "view_zipWith3"
  , "view_zipWith4"
  , "Sequence_flatten"
  , "Sequence_generate"
  , "Sequence_from_llist"
  , "Sequence_map"
  , "Sequence_zipWith"
  , "Sequence_zipWith3"
  , "Sequence_zipWith4"

    -- Integer index arithmetic 
  , "zero_fii"
  , "one_fii"
  , "plus_fii"
  , "minus_fii"
  , "min_fii"
  , "max_fii"
  , "zero_ii"
  , "one_ii"
  , "plus_ii"
  , "minus_ii"
  , "min_ii"
  , "max_ii"
  , "range_nonempty_ii"
  , "eqZ_refl"
  , "deadProof"

    -- Integer arithmetic
  , "sizealign_arr"
  , "gcd"
  , "extgcd_x"
  , "isEmptyInterval"
  , "inInterval"
  , "intersectInterval"
  , "convolveInterval"
  , "subsetInterval"
  , "inLM"
  , "evalLM"
  , "invEvalLM"
  , "intersectLM"
  , "trimInterval"
  , "arrayDescToDim1"
  , "dim1ToArrayDesc"

    -- Built-in functions
  , "floor"
  , "min_int"
  , "max_int"
  , "max_uint"
  , "uint_to_int"
  , "or"
  , "and"
  , "not"
  , "lshift"
  , "rshift"
  , "oper_BITWISEAND"
  , "oper_BITWISEOR"
  , "oper_BITWISEXOR"
  , "fun_undefined"
  , "fun_isNothing"
  , "fun_isJust"
  , "fun_fromJust"
  , "fun_map"
  , "fun_filter"
  , "fun_reduce"
  , "fun_reduce1"
  , "fun_sum"
  , "fun_scatter"
  , "fun_indices"
  , "fun_zip"
  , "fun_zip3"
  , "fun_zip4"
  , "count"
  , "range"
  , "arrayRange"
  , "singletonIter"
  , "chain"
  , "len"
  , "safeIndex"
  , "safeSlice"
  , "width"
  , "height"
  , "histogram"
  , "rows"
  , "cols"
  , "outerproduct"
  , "outerproductStream"
  , "transpose"
  , "boxedPermute1D"
  , "permute1D"
  , "boxedStencil2D"
  , "stencil2D"
  , "boxedStencil3D"
  , "stencil3D"
  , "extend2D"
  , "extend3D"
  , "displaceView"
  , "multiplyView"
  , "divideView"
  , "internalApplyListSlice"
  , "internalApplyArraySlice"
  , "sliceToDomain"
  , "build_intset"
  , "intsetLookup"
  , "intsetElements"
  , "compute_hash_table_size"
  , "build_hash_table"
  , "lookup_hash_table"
  , "idCoercion"
  , "idBareCoercion"
  , "cartesianIndexCoercion"
  , "unsafeMakeCoercion"
  , "unsafeMakeBareCoercion"
  , "unsafeMakeViewCoercion"
  , "traceInt_int"
  , "traceInt_box"
    
  , "isCons"
  , "isNil"
  , "head"
  , "tail"

    -- In-place update
  , "intUpdateInPlace_int_coercion"
  , "intUpdateInPlace_finalizer"
  , "intUpdateInPlace_initializer"
  , "intUpdateInPlace_updater"
  , "intUpdateInPlace_combiner"
  , "floatUpdateInPlace_float_coercion"
  , "floatUpdateInPlace_finalizer"
  , "floatUpdateInPlace_initializer"
  , "floatUpdateInPlace_updater"
  , "floatUpdateInPlace_combiner"
  , "boolUpdateInPlace_bool_coercion"
  , "boolUpdateInPlace_finalizer"
  , "boolUpdateInPlace_initializer"
  , "boolUpdateInPlace_updater"

  , "intScatter"
  , "floatScatter"
  , "boolScatter"
  , "intSumScatter"
  , "intSumScatter_updater"
  , "intSumScatter_make_update"
  , "intSumScatter_make_init"
  , "floatSumScatter"
  , "floatSumScatter_updater"
  , "floatSumScatter_make_update"
  , "floatSumScatter_make_init"
  , "countingScatter"
  , "countingScatter_updater"
  , "countingScatter_make_update"
  , "countingScatter_make_init"
  , "appendScatter"
  , "appendScatter_initializer"
  , "appendScatter_updater"
  , "appendScatter_update_real"
  , "appendScatter_concatenate"
  , "boxedScatter"
  , "boxedScatter_updater"
  , "comapScatterIndex"
  , "arrScatter"
  , "blistScatter"
  , "listScatter"
  , "barray1Scatter"
  , "barray2Scatter"
  , "barray3Scatter"
  , "array1Scatter"
  , "array2Scatter"
  , "array3Scatter"
  , "Sequence_partial_scatter"
  , "partial_list_dim_scatter"
  , "finish_scatter"

    -- Inserted by rewrites or inlining
  , "sequenceToView"
  , "viewToSequence"
  , "view_transform"
  , "view_array1_build"
  , "Sequence_list_build"
  , "Sequence_array1_build"
  , "empty_list_dim_view"
  , "singleton_list_dim_view"
  , "peel_generate"
  , "peel_generate_bind"
    
    -- Sequence functions
  , "Stream1_empty"
  , "Stream1_return"
  , "Stream1_guard"
  , "Stream1_bind"
  , "Sequence_empty"
  , "Sequence_return"
  , "Sequence_chain"
  , "Sequence_guard"
  , "Sequence_bind"
  , "Sequence_generate_bind"
  , "Sequence_reduce"
  , "Sequence_reduce1"
  , "Sequence_scatter"
  , "Sequence_fold"
  , "Sequence_parallel_reduce"
  , "Sequence_parallel_build"
  , "Sequence_parallel_scatter"

    -- Fold-like functions
  , "build_dim1_array"
  , "build_list_dim_list"
  , "reduce_list_dim"
  , "reduce_dim1"
  , "reduce_dim2"
  , "reduce1_list_dim"
  , "reduce1_dim1"
  , "reduce1_dim2"
  , "scatter_list_dim"
  , "scatter_dim1"
  , "scatter_dim2"
  , "fold_list_dim"
  , "fold_dim1"
  , "fold_dim2"
  , "llist_fold"

    -- Primitive functions
  , "primitive_list_dim_chain"
  , "primitive_list_dim_reduce"
  , "primitive_dim1_reduce"
  , "primitive_dim2_reduce"
  , "primitive_list_dim_reduce1"
  , "primitive_dim1_reduce1"
  , "primitive_dim2_reduce1"
  , "primitive_list_dim_fold"
  , "primitive_dim1_fold"
  , "primitive_list_dim_scatter"
  --, "primitive_list_dim_list"
  --, "primitive_dim1_array"
  --, "primitive_dim2_array"
  , "append_build_list"
  
  , "parallel_list_dim_reduce"
  , "parallel_dim1_reduce"
  , "parallel_dim2_reduce"
  , "parallel_list_dim_reduce1"
  , "parallel_dim1_reduce1"
  , "parallel_dim2_reduce1"
  , "parallel_list_dim_scatter"
  --, "parallel_list_dim_list"
  -- , "parallel_dim1_array"
  -- , "parallel_dim2_array"
  --, "fun_fold_Stream"
  --, "fun_reduce_Stream"
  --, "fun_reduce1_Stream"
  --, "primitive_darr1_reduce"
  --, "primitive_darr1_reduce1"
  --, "primitive_darr1_generate"
  --, "view1_reduce"
  --, "view1_reduce1"
  --, "view1_scatter"
  --, "view1_fold"
  , "fun_from_MatrixView_Stream"
  , "fun_asArray2_Stream"
  , "histogramArray"
    
    -- Inserted by representation inference
  , "copy"
  , "convertToBoxed"
  , "convertToBare"
  , "reprSizeAlign"
  , "dynamicCopyError"
  , "copyArray"
  , "reify"
  , "shapeIndexRepr"
  , "shapeSliceRepr"
    
    -- Inserted by argument flattening
  , "deadBox"
  , "deadRef"
  
    -- Inserted by rewrite rules
  , "fromIndInt"
  , "defineIntIndex"
  , "rangeIndexed"
  , "subscript"
  , "subscript_out"
  , "doall"
  , "for"
  , "for_box"
  --, "parallel_dim1_reduce"
  --, "parallel_dim1_reduce1"
  --, "parallel_darr1_reduce"
  --, "parallel_darr1_reduce1"
  , "parallel_doall"
  --, "parallel_darr1_generate"
  --, "parallel_darr2_reduce"
  --, "parallel_darr2_generate"
  , "parallel_doall2"
  , "blocked_1d_reduce"
  , "blocked_2d_reduce"
  , "blocked_1d_reduceip"
  , "blocked_doall"
  , "blocked_doall2"
  , "blocked_PBTree_doall"
  , "emptyEffTok"
  , "toEffTok"
  , "seqEffTok"
  , "fromEffTok"
  
    -- Obsolete, will be eliminated
  , "fun_map_Stream"
  , "fun_zip_Stream"
  , "fun_zip3_Stream"
  , "fun_zip4_Stream"
  , "fun_asMatrix_Stream"
  ]
