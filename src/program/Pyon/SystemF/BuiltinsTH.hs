
{-# LANGUAGE TemplateHaskell #-}
module Pyon.SystemF.BuiltinsTH where

import Language.Haskell.TH(Strict(..))
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
  }

data AdditiveDictMembers =
  AdditiveDictMembers
  { zeroMember :: !Con
  , addMember :: !Con
  , subMember :: !Con
  }

data VectorDictMembers =
  VectorDictMembers
  { scaleMember :: !Con
  , normMember :: !Con
  }

pyonBuiltinConstructors =
  [ -- Types
    "Stream"
  , "bool"
  , "list"
  , "NoneType"
  , "Any"
  , "EqDict"
  , "OrdDict"
  , "TraversableDict"
  , "AdditiveDict"
  , "VectorDict"
  , "PassConv"
    -- Data constructors
  , "None"
  , "True"
  , "False"
  , "eqDict"
  , "ordDict"
  , "traversableDict"
  , "additiveDict"
  , "vectorDict"
  , "passConv"
    -- Functions
  , "oper_MUL"
  , "oper_DIV"
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
  , "fun_makelist"
  , "fun_map"
  , "fun_reduce"
  , "fun_reduce1"
  , "fun_zip"
  , "fun_iota"
  , "fun_undefined"
  ]

pyonBuiltinConstructorNames = map ('_':) pyonBuiltinConstructors

pyonBuiltinsSpecification =
  recordDef "PyonBuiltins" (constructors ++ others)
  where
    constructors =
      map (\n -> (n, IsStrict, [t| Con |]))pyonBuiltinConstructorNames

    others = [ ("_tuples", NotStrict, [t| [Con] |])
             , ("_tupleConstructors", NotStrict, [t| [Con] |])
             , ("_EqDict_Int", IsStrict, [t| EqDictMembers |])
             , ("_OrdDict_Int", IsStrict, [t| OrdDictMembers |])
             , ("_EqDict_Float", IsStrict, [t| EqDictMembers |])
             , ("_OrdDict_Float", IsStrict, [t| OrdDictMembers |])
             , ("_EqDict_Tuple2", IsStrict, [t| EqDictMembers |])
             , ("_OrdDict_Tuple2", IsStrict, [t| OrdDictMembers |])
             , ("_TraversableDict_Stream", IsStrict, [t| TraversableDictMembers |])
             , ("_TraversableDict_list", IsStrict, [t| TraversableDictMembers |])
             , ("_AdditiveDict_Int", IsStrict, [t| AdditiveDictMembers |])
             , ("_AdditiveDict_Float", IsStrict, [t| AdditiveDictMembers |])
             ]
               