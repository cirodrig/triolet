
{-# LANGUAGE TemplateHaskell #-}
module Builtins.BuiltinsTH where
       
import Language.Haskell.TH(Strict(..))
import Gluon.Common.THRecord
import LowLevel.Label
import Type.Var

pyonBuiltinModuleNameString = "builtin"
pyonBuiltinModuleName = moduleName pyonBuiltinModuleNameString

pyonBuiltinTypeNames =
  [ "bool"
  , "int"
  , "float"
  , "complex"
  , "list"
  , "NoneType"
  , "Any"
  , "PyonTuple0"
  , "PyonTuple1"
  , "PyonTuple2"
  , "PyonTuple3"
  , "Stream"
  , "LazyStream"
    
    -- Dictionary types
  , "Repr"
  , "TraversableDict"
  , "EqDict"
  , "OrdDict"
  , "AdditiveDict"
  , "MultiplicativeDict"
  , "VectorDict"
  ]

pyonBuiltinVariableNames =
  [ -- Data constructors
    "True"
  , "False"
  , "pyonTuple0"
  , "pyonTuple1"
  , "pyonTuple2"
  , "pyonTuple3"
    
    -- Class constructors
  , "traversableDict"
  , "eqDict"
  , "ordDict"
  , "additiveDict"
  , "multiplicativeDict"
  , "vectorDict"

    -- Class instances
  , "repr_bool"
  , "repr_int"
  , "repr_float"
  , "repr_complex"
  , "repr_list"
  , "repr_NoneType"
  , "repr_Any"
  , "repr_owned"
  , "repr_iter"
  , "repr_PyonTuple0"
  , "repr_PyonTuple1"
  , "repr_PyonTuple2"
  , "repr_PyonTuple3"
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
  , "additiveDict_complex"
  , "add_complex"
  , "sub_complex"
  , "negate_complex"
  , "zero_complex"
  , "MultiplicativeDict_int"
  , "MultiplicativeDict_int_mul"
  , "MultiplicativeDict_int_fromInt"
  , "MultiplicativeDict_int_one"
  , "MultiplicativeDict_float"
  , "MultiplicativeDict_float_mul"
  , "MultiplicativeDict_float_fromInt"
  , "MultiplicativeDict_float_one"

    -- Built-in functions
  , "oper_DO"
  , "oper_GUARD"
  , "oper_CAT_MAP"
  , "oper_DIV"
  , "oper_MOD"
  , "oper_FLOORDIV"
  , "oper_POWER"
  , "oper_BITWISEAND"
  , "oper_BITWISEOR"
  , "oper_BITWISEXOR"
  , "fun_undefined"
  , "fun_map"
  , "fun_reduce"
  , "fun_reduce1"
  , "fun_zip"
  , "fun_iota"
  , "makeComplex"
    
    -- Inserted by stream specialization
  , "fun_map_Stream"
  , "fun_reduce_Stream"
  , "fun_reduce1_Stream"
  , "fun_zip_SS"
  , "fun_zip_SN"
  , "fun_zip_NS"
  ]

pyonBuiltinsSpecification =
  recordDef "PyonBuiltins" variables
  where
    variables =
      [('_' : n, IsStrict, [t| Var |])
      | n <- pyonBuiltinTypeNames ++ pyonBuiltinVariableNames]
