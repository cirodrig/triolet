
{-# LANGUAGE TemplateHaskell #-}
module Builtins.BuiltinsTH where
       
import Language.Haskell.TH(Strict(..))
import Common.THRecord
import Common.Label
import Type.Var

pyonBuiltinTypeNames =
  [ "bool"
  , "int"
  , "float"
  , "Complex"
  , "list"
  , "NoneType"
  , "Any"
  , "PyonTuple0"
  , "PyonTuple1"
  , "PyonTuple2"
  , "PyonTuple3"
  , "PyonTuple4"
  , "Stream"
  , "Boxed"
  , "Referenced"
  , "IndexedInt"
  , "array"
    
    -- Dictionary types
  , "Repr"
  , "TraversableDict"
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
  , "pyonTuple0"
  , "pyonTuple1"
  , "pyonTuple2"
  , "pyonTuple3"
  , "pyonTuple4"
  , "boxed"
  , "referenced"
  , "indexedInt"
  , "make_list"

    -- Class constructors
  , "traversableDict"
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
  , "repr_Complex"
  , "repr_list"
  , "repr_NoneType"
  , "repr_Any"
  , "repr_Box"
  , "repr_Stream"
  , "repr_Boxed"
  , "repr_EmptyReference"
  , "repr_PyonTuple0"
  , "repr_PyonTuple1"
  , "repr_PyonTuple2"
  , "repr_PyonTuple3"
  , "repr_PyonTuple4"
  , "TraversableDict_Stream"
  , "TraversableDict_Stream_traverse"
  , "TraversableDict_Stream_build"
  , "TraversableDict_list"
  , "TraversableDict_list_traverse"
  , "TraversableDict_list_build"
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
  , "OpaqueTraversableDict_list"
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

    -- Integer index arithmetic 
  , "zero_i"
  , "one_i"
  , "plus_i"
  , "minus_i"
  , "min_i"
  , "zero_ii"
  , "one_ii"
  , "plus_ii"
  , "minus_ii"
  , "min_ii"

    -- Built-in functions
  , "floor"
  , "oper_DO"
  , "oper_GUARD"
  , "oper_CAT_MAP"
  , "oper_BITWISEAND"
  , "oper_BITWISEOR"
  , "oper_BITWISEXOR"
  , "fun_undefined"
  , "fun_map"
  , "fun_reduce"
  , "fun_reduce1"
  , "fun_zip"
  , "fun_zip3"
  , "fun_zip4"
  , "count"
  , "range"
  , "histogram"
  , "makeComplex"
    
    -- Inserted by stream specialization
  , "fun_map_Stream"
  , "fun_reduce_Stream"
  , "fun_reduce1_Stream"
  , "fun_zip_Stream"
  , "fun_zip3_Stream"
  , "fun_zip4_Stream"
  , "fun_asList_Stream"
  , "histogramArray"
    
    -- Inserted by representation inference
  , "load"
  , "store"
  , "copy"
  , "loadBox"
  , "storeBox"
  , "copyBox"
  , "boxToPtr"
  , "ptrToBox"
  
    -- Inserted by rewrite rules
  , "generate"
  , "subscript"
  , "subscript_out"
  , "doall"
  , "for"
  ]

pyonBuiltinsSpecification =
  recordDef "PyonBuiltins" variables
  where
    variables =
      [('_' : n, IsStrict, [t| Var |])
      | n <- pyonBuiltinTypeNames ++ pyonBuiltinVariableNames]

