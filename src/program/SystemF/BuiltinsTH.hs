
{-# LANGUAGE TemplateHaskell #-}
module SystemF.BuiltinsTH where

import Language.Haskell.TH(Strict(..))
import Gluon.Common.Label
import Gluon.Common.THRecord
import Gluon.Core.Syntax

data EqDictMembers =
  EqDictMembers
  { eqMember :: !Con
  , neMember :: !Con
  }

data OrdDictMembers =
  OrdDictMembers
  { ltMember :: !Con
  , leMember :: !Con
  , gtMember :: !Con
  , geMember :: !Con
  }

data TraversableDictMembers =
  TraversableDictMembers
  { traverseMember :: !Con
  , buildMember    :: !Con
  }

data AdditiveDictMembers =
  AdditiveDictMembers
  { addMember :: !Con
  , subMember :: !Con
  , negateMember :: !Con
  , zeroMember :: !Con
  }

data MultiplicativeDictMembers =
  MultiplicativeDictMembers
  { mulMember :: !Con
  , fromIntMember :: !Con
  , oneMember :: !Con
  }

data VectorDictMembers =
  VectorDictMembers
  { scaleMember :: !Con
  , normMember :: !Con
  }

pyonBuiltinModuleNameString = "SFBuiltin"
pyonBuiltinModuleName = moduleName pyonBuiltinModuleNameString

pyonBuiltinTypeConstructors =
  [ "Stream"
  , "LazyStream" -- Streams with side effects produced by effect inference
  , "Ptr"                       -- Pointers produced by flattening
  , "Own"                       -- Produced by flattening
  , "Def"                       -- Produced by flattening
  , "Undef"                       -- Produced by flattening
  , "Action"                    -- Produced by flattening
  , "bool"
  , "int"
  , "float"
  , "complex"
  , "list"
  , "NoneType"
  , "Any"
  , "EqDict"
  , "OrdDict"
  , "TraversableDict"
  , "AdditiveDict"
  , "MultiplicativeDict"
  , "VectorDict"
  , "PassConv"
  ]

pyonBuiltinDataConstructors =
  [ "makeComplex"
  , "None"
  , "True"
  , "False"
  , "makeList"
  , "eqDict"
  , "ordDict"
  , "traversableDict"
  , "additiveDict"
  , "multiplicativeDict"
  , "vectorDict"
  , "OpaqueTraversableDict_list"
  ]

pyonBuiltinPassConvConstructors =
  [ "passConv_int"
  , "passConv_float"
  , "passConv_bool"
  , "passConv_NoneType"
  , "passConv_complex"
  , "passConv_iter"
  , "passConv_list"
  , "passConv_Any"
  , "passConv_owned"
  ]

pyonBuiltinPassConvAddresses =
  [ "passConv_int_addr"
  , "passConv_float_addr"
  , "passConv_bool_addr"
  , "passConv_NoneType_addr"
  , "passConv_Any_addr"
  , "passConv_owned_addr"
  , "eqDict_int_addr"
  , "eqDict_float_addr"
  , "additiveDict_int_zero_addr"
  , "additiveDict_float_zero_addr"
  , "multiplicativeDict_int_one_addr"
  , "multiplicativeDict_float_one_addr"
  , "OpaqueTraversableDict_list_addr"
  ]

pyonBuiltinPassConvPointers =
  [ "passConv_int_ptr"
  , "passConv_float_ptr"
  , "passConv_bool_ptr"
  , "passConv_NoneType_ptr"
  , "passConv_Any_ptr"
  , "passConv_owned_ptr"
  , "eqDict_int_ptr"
  , "eqDict_float_ptr"
  , "OpaqueTraversableDict_list_ptr"
  ]

pyonBuiltinFunctions =
  [ "oper_DIV"
  , "oper_FLOORDIV"
  , "oper_MOD"
  , "oper_POWER"
  , "oper_BITWISEAND"
  , "oper_BITWISEOR"
  , "oper_BITWISEXOR"
  , "oper_NEGATE"
  , "oper_CAT_MAP"
  , "oper_GUARD"
  , "oper_DO"
  , "fun_map"
  , "fun_map_Stream"
  , "fun_reduce"
  , "fun_reduce_Stream"
  , "fun_reduce1"
  , "fun_reduce1_Stream"
  , "fun_zip"
  , "fun_zip_SS"
  , "fun_zip_NS"
  , "fun_zip_SN"
  , "fun_iota"
  , "fun_undefined"
  , "additiveDict_complex"
  , "add_complex"
  , "sub_complex"
  , "negate_complex"
  , "zero_complex"
    
    -- Type class constructors
  , "eqDict_Tuple2"
  , "ordDict_Tuple2"

    -- Functions inserted by effect inference
  , "fun_return"
  , "fun_copy"
  , "fun_store_int"
  , "fun_store_float"
  , "fun_store_complexFloat"
  , "fun_store_bool"
  , "fun_store_NoneType"
  , "fun_store_boxed"
  , "fun_load_int"
  , "fun_load_float"
  , "fun_load_complexFloat"
  , "fun_load_bool"
  , "fun_load_NoneType"
  , "fun_load_boxed"
    
    -- Functions inserted in Core
  , "fun_subscript"
  , "fun_generate"
  , "fun_generateList"
  , "fun_vectorGenerateList"
  ]

pyonBuiltinConstructors =
  pyonBuiltinTypeConstructors ++
  pyonBuiltinDataConstructors ++
  pyonBuiltinPassConvConstructors ++
  pyonBuiltinFunctions

pyonBuiltinConstructorNames = map ('_':) pyonBuiltinConstructors

pyonBuiltinVariables =
  [ "dummy_addr" ] ++
  pyonBuiltinPassConvAddresses ++ pyonBuiltinPassConvPointers

pyonBuiltinVariableNames = map ('_':) pyonBuiltinVariables

pyonBuiltinsSpecification =
  recordDef "PyonBuiltins" (constructors ++ variables ++ others)
  where
    constructors =
      map (\n -> (n, IsStrict, [t| Con |])) pyonBuiltinConstructorNames

    variables =
      map (\n -> (n, IsStrict, [t| Var |])) pyonBuiltinVariableNames

    others = [ ("_tuples", NotStrict, [t| [Con] |])
             , ("_tupleConstructors", NotStrict, [t| [Con] |])
             , ("_tuplePassConvConstructors", NotStrict, [t| [Con] |])
             , ("_EqDict_int", IsStrict, [t| EqDictMembers |])
             , ("_OrdDict_int", IsStrict, [t| OrdDictMembers |])
             , ("_EqDict_float", IsStrict, [t| EqDictMembers |])
             , ("_OrdDict_float", IsStrict, [t| OrdDictMembers |])
             , ("_EqDict_Tuple2", IsStrict, [t| EqDictMembers |])
             , ("_OrdDict_Tuple2", IsStrict, [t| OrdDictMembers |])
             , ("_TraversableDict_Stream", IsStrict, [t| TraversableDictMembers |])
             , ("_TraversableDict_list", IsStrict, [t| TraversableDictMembers |])
             , ("_AdditiveDict_int", IsStrict, [t| AdditiveDictMembers |])
             , ("_AdditiveDict_float", IsStrict, [t| AdditiveDictMembers |])
             , ("_MultiplicativeDict_int", IsStrict, [t| MultiplicativeDictMembers |])
             , ("_MultiplicativeDict_float", IsStrict, [t| MultiplicativeDictMembers |])
             ]
               