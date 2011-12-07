
{-# LANGUAGE TemplateHaskell #-}
module Builtins.BuiltinsTH where
       
pyonBuiltinTypeNames =
  [ "bool"
  , "int"
  , "float"
  , "Complex"
  , "list"
  , "array0"
  , "array1"
  , "array2"
  , "view"
  , "darr1"
  , "darr2"
  , "NoneType"
  , "Maybe"
  , "MaybeVal"
  , "Any"
  , "Interval"
  , "LinearMap"
  , "SliceObject"
  , "InternalSlice"             -- TODO: remove this type
  , "PyonTuple0"
  , "PyonTuple1"
  , "PyonTuple2"
  , "PyonTuple3"
  , "PyonTuple4"
  , "Stream"
  , "Stream1"
  , "Sequence"
  , "StreamNext"
  , "BindState"
  , "FIInt"
  , "IInt"
  , "SomeIInt"
  , "arr"
  , "EffTok"
  , "Pf"
  , "UpdateInPlace"

    -- Representation coercions
  , "Stored"
  , "StoredBox"
  , "Boxed"
  , "Referenced"
  , "OutPtr"
  , "IEffect"
  , "Writer"
  , "BoxedType"
  , "BareType"
    
    -- Container type functions
  , "index"
  , "slice"
  , "array"
    
    -- Shape-related types
  , "shape"
  , "list_dim"
  , "dim0"
  , "dim1"
  , "dim2"
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
  ]

pyonBuiltinVariableNames =
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
  , "pyonTuple0"
  , "pyonTuple1"
  , "pyonTuple2"
  , "pyonTuple3"
  , "pyonTuple4"
  , "just"
  , "nothing"
  , "justVal"
  , "nothingVal"
  , "stored"
  , "storedBox"
  , "boxed"
  , "referenced"
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
  , "make_list"
  , "mk_array0"
  , "mk_array1"
  , "mk_array2"
  , "mk_view"
  , "mk_darr1"
  , "mk_darr2"
  , "effTok"
  , "pf"
  , "mk_list_dim"
  , "mk_dim0"
  , "mk_dim1"
  , "mk_dim2"
  , "mk_arr_shape"
  , "updateInPlace"

    -- Class constructors
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

    -- Class instances
  , "repr_bool"
  , "repr_int"
  , "repr_float"
  , "repr_MaybeVal"
  , "repr_list_dim"
  , "repr_dim0"
  , "repr_dim1"
  , "repr_dim2"
  , "repr_Complex"
  , "repr_list"
  , "repr_array0"
  , "repr_array1"
  , "repr_array2"
  , "repr_NoneType"
  , "repr_Any"
  , "repr_StoredBox"
  , "repr_Box"
  , "repr_Stream"
  , "repr_view"
  , "repr_Referenced"
  , "repr_Maybe"
  , "repr_EmptyReference"
  , "repr_arr"
  , "repr_EffTok"
  , "repr_SliceObject"
  , "repr_PyonTuple0"
  , "repr_PyonTuple1"
  , "repr_PyonTuple2"
  , "repr_PyonTuple3"
  , "repr_PyonTuple4"
  , "ShapeDict_list_dim"
  , "ShapeDict_dim0"
  , "ShapeDict_dim1"
  , "ShapeDict_dim2"
  , "TraversableDict_Stream_traverse"
  , "TraversableDict_Stream_build"
  , "TraversableDict_view_list_dim_traverse"
  , "TraversableDict_view_list_dim_build"
  , "TraversableDict_view_dim0_traverse"
  , "TraversableDict_view_dim0_build"
  , "TraversableDict_view_dim1_traverse"
  , "TraversableDict_view_dim1_build"
  , "TraversableDict_view_dim2_traverse"
  , "TraversableDict_view_dim2_build"
  , "TraversableDict_list_traverse"
  , "TraversableDict_list_build"
  , "TraversableDict_array0_traverse"
  , "TraversableDict_array0_build"
  , "TraversableDict_array1_traverse"
  , "TraversableDict_array1_build"
  , "TraversableDict_array2_traverse"
  , "TraversableDict_array2_build"
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
  , "ShapeDict_dim2_map"
  , "ShapeDict_dim2_zipWith"
  , "ShapeDict_dim2_zipWith3"
  , "ShapeDict_dim2_zipWith4"
  , "ShapeDict_dim2_slice"
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
  , "EqDict_int"
  , "EqDict_int_eq"
  , "EqDict_int_ne"
  , "EqDict_float"
  , "EqDict_float_eq"
  , "EqDict_float_ne"
  , "EqDict_Tuple2"
  , "EqDict_Tuple2_eq"
  , "EqDict_Tuple2_ne"
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
  , "AdditiveDict_float"
  , "AdditiveDict_float_add"
  , "AdditiveDict_float_sub"
  , "AdditiveDict_float_negate"
  , "AdditiveDict_float_zero"
  , "AdditiveDict_Complex_add"
  , "AdditiveDict_Complex_sub"
  , "AdditiveDict_Complex_negate"
  , "AdditiveDict_Complex_zero"
  , "MultiplicativeDict_int"
  , "MultiplicativeDict_int_mul"
  , "MultiplicativeDict_int_fromInt"
  , "MultiplicativeDict_int_one"
  , "MultiplicativeDict_float"
  , "MultiplicativeDict_float_mul"
  , "MultiplicativeDict_float_fromInt"
  , "MultiplicativeDict_float_one"
  , "MultiplicativeDict_Complex_mul"
  , "MultiplicativeDict_Complex_fromInt"
  , "MultiplicativeDict_Complex_one"
  , "RemainderDict_int_floordiv"
  , "RemainderDict_int_mod"
  , "RemainderDict_float_floordiv"
  , "RemainderDict_float_mod"
  , "FractionalDict_float_div"
  , "FractionalDict_Complex_div"
  , "FloatingDict_float_fromfloat"
  , "FloatingDict_float_power"
  , "FloatingDict_float_exp"
  , "FloatingDict_float_log"
  , "FloatingDict_float_sqrt"
  , "FloatingDict_float_sin"
  , "FloatingDict_float_cos"
  , "FloatingDict_float_tan"
  , "FloatingDict_float_pi"
  , "FloatingDict_Complex_fromfloat"
  , "FloatingDict_Complex_power"
  , "FloatingDict_Complex_exp"
  , "FloatingDict_Complex_log"
  , "FloatingDict_Complex_sqrt"
  , "FloatingDict_Complex_sin"
  , "FloatingDict_Complex_cos"
  , "FloatingDict_Complex_tan"
  , "FloatingDict_Complex_pi"
  , "VectorDict_float_scale"
  , "VectorDict_float_magnitude"
  , "VectorDict_float_dot"
  , "VectorDict_Complex_scale"
  , "VectorDict_Complex_magnitude"
  , "VectorDict_Complex_dot"

    -- Constructor-like functions
  , "create_view2"

    -- Pseudo-dictionary methods inserted by optimizations
  , "arr1D_build"
  , "arr2D_build"
  , "view_generate"
  , "view_map"
  , "view_zipWith"
  , "view_zipWith3"
  , "view_zipWith4"
  , "Sequence_flatten"
  , "Sequence_generate"
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
  , "gcd"
  , "extgcd_x"
  , "isEmptyInterval"
  , "inInterval"
  , "intersectInterval"
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
  , "or"
  , "and"
  , "oper_BITWISEAND"
  , "oper_BITWISEOR"
  , "oper_BITWISEXOR"
  , "fun_undefined"
  , "fun_just"
  , "fun_nothing"
  , "fun_isNothing"
  , "fun_isJust"
  , "fun_fromJust"
  , "fun_map"
  , "fun_reduce"
  , "fun_reduce1"
  , "fun_indices"
  , "fun_zip"
  , "fun_zip3"
  , "fun_zip4"
  , "count"
  , "range"
  , "len"
  , "safeIndex"
  , "safeSlice"
  , "width"
  , "height"
  , "histogram"
  , "makeComplex"
  , "rows"
  , "cols"
  , "outerproduct"
  , "transpose"
  , "stencil2D"
  , "extend2D"
  , "shift2D"
  , "range2D"
  , "internalApplyListSlice"
  , "internalApplyArraySlice"
  , "sliceToDomain"
  , "unsafeMakeCoercion"
  , "unsafeMakeViewCoercion"

    -- In-place update
  , "intUpdateInPlace"
  , "floatUpdateInPlace"
  , "intUpdateInPlace_initializer"
  , "intUpdateInPlace_updater"
  , "floatUpdateInPlace_initializer"
  , "floatUpdateInPlace_updater"
  , "arrUpdateInPlace"

    -- Inserted by rewrites or inlining
  , "sequenceToView"
  , "viewToSequence"
  , "view1ToDarr1"
  , "darr1ToView1"
  , "view2ToDarr2"
  , "darr2ToView2"
  , "view_list_build"
  , "view_array1_build"
  , "Sequence_list_build"
  , "Sequence_array1_build"
  , "empty_list_dim_view"
    
    -- Sequence functions
  , "Stream1_empty"
  , "Stream1_return"
  , "Stream1_guard"
  , "Stream1_bind"
  , "Sequence_build_list"
  , "Sequence_empty"
  , "Sequence_return"
  , "Sequence_guard"
  , "Sequence_bind"
  , "Sequence_generate_bind"
  , "Sequence_reduce"
  , "Sequence_reduce1"
  , "Sequence_fold"
  , "Sequence_parallel_reduce"

    -- Fold-like functions
  , "accumulate_Stream_int"
  , "build_dim1_array"
  , "build_list_dim_list"
  , "reduce_list_dim"
  , "reduce_dim1"
  , "reduce_dim2"
  , "reduce1_list_dim"
  , "reduce1_dim1"
  , "reduce1_dim2"

    -- Primitive functions
  , "primitive_list_dim_reduce"
  , "primitive_dim1_reduce"
  , "primitive_dim2_reduce"
  , "primitive_list_dim_reduce1"
  , "primitive_dim1_reduce1"
  , "primitive_dim2_reduce1"
  , "primitive_list_dim_fold"
  , "primitive_dim1_fold"
  , "primitive_list_dim_list"
  , "primitive_dim1_array"
  , "primitive_dim2_array"
  
  , "parallel_list_dim_reduce"
  , "parallel_dim1_reduce"
  , "parallel_dim2_reduce"
  , "parallel_list_dim_reduce1"
  , "parallel_dim1_reduce1"
  , "parallel_dim2_reduce1"
  , "parallel_list_dim_list"
  , "parallel_dim1_array"
  , "parallel_dim2_array"
  --, "fun_fold_Stream"
  --, "fun_reduce_Stream"
  --, "fun_reduce1_Stream"
  --, "primitive_darr1_reduce"
  --, "primitive_darr1_reduce1"
  --, "primitive_darr1_generate"
  , "darr1_reduce"
  , "darr1_reduce1"
  , "darr1_fold"
  , "view1_reduce"
  , "view1_reduce1"
  , "view1_fold"
  , "darr2_reduce"
  , "darr2_reduce1"
  , "darr2_fold"
  , "primitive_darr2_reduce"
  , "primitive_darr2_reduce1"
  , "primitive_darr2_generate"
  , "primitive_darr2_flatten"
  , "fun_from_MatrixView_Stream"
  , "fun_asArray2_Stream"
  , "histogramArray"
    
    -- Inserted by representation inference
  , "copy"
  , "convertToBoxed"
  , "convertToBare"
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
  , "blocked_1d_reduce1"
  , "blocked_2d_reduce1"
  , "blocked_doall"
  , "blocked_doall2"
  , "emptyEffTok"
  , "toEffTok"
  , "seqEffTok"
  , "fromEffTok"
  
    -- Obsolete, will be eliminated
  , "arr1D_traverse"
  , "arr2D_traverse"
  , "darr2_flatten"
  , "generate"
  , "generate_forever"
  , "array_build"
  , "array_reduce"
  , "fun_map_Stream"
  , "fun_zip_Stream"
  , "fun_zip3_Stream"
  , "fun_zip4_Stream"
  , "fun_asList_Stream"
  , "fun_asMatrix_Stream"
  ]
