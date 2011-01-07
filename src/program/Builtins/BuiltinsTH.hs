
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
  ]

pyonBuiltinVariableNames =
  []

pyonBuiltinsSpecification =
  recordDef "PyonBuiltins" variables
  where
    variables =
      [('_' : n, IsStrict, [t| Var |])
      | n <- pyonBuiltinTypeNames ++ pyonBuiltinVariableNames]

