
{-# LANGUAGE TemplateHaskell #-}
module Untyped.BuiltinsTH where

import Language.Haskell.TH(Strict(..))
import Language.Haskell.TH.Syntax(Lift(..))
import Gluon.Common.THRecord
import Gluon.Core hiding(Kind)
import Untyped.Data
import Untyped.Kind
import Untyped.Syntax

instance Lift Kind where
  lift Star = [| Star |]
  lift (k1 :-> k2) = [| k1 :-> k2 |]

-- | All predefined data type names recognized by the Pyon parser
pyonSourceTypes :: [String] 
pyonSourceTypes =
  ["int", "float", "bool", "NoneType", "iter", "list", "Any"]

-- | All predefined global functions recognized by the Pyon parser
pyonSourceGlobals :: [String]
pyonSourceGlobals =
  [ "map"
  , "reduce"
  , "reduce1"
  , "zip"
  , "iota"
  , "__undefined__"
  , "__mul__"
  , "__div__"
  , "__mod__"
  , "__floordiv__"
  , "__power__"
  , "__and__"
  , "__or__"
  , "__xor__"
  , "__negate__"
    -- Class methods
  , "__eq__"
  , "__ne__"
  , "__lt__"
  , "__le__"  
  , "__gt__"
  , "__ge__"
  , "__iter__"
  , "zero"
  , "__add__"
  , "__sub__"
  , "scale"
  , "norm"
  ]

-- | Global variables that can't be referred to by name 
pyonOtherGlobals :: [String]
pyonOtherGlobals =
  [ "makelist", "do", "guard", "iterBind"
  ]

-- | All predefined class names
pyonClasses :: [String]
pyonClasses =
  [ "Eq", "Ord", "Traversable", "Additive", "Vector"]

-- Global variable fields are not strict because some of them are built 
-- using fields of the builtins table.  Class fields are strict, but most 
-- of their fields are not for the same reason.
tiBuiltinSpecification =
  recordDef "TIBuiltins" fields
  where
    fields = [('_':name, IsStrict, [t| Con |])
             | name <- pyonSourceTypes ] ++ 
             [("_con_" ++ name, IsStrict, [t| TyCon |])
             | name <- pyonSourceTypes] ++
             [('_':name, NotStrict, [t| Variable |])
             | name <- pyonSourceGlobals ++ pyonOtherGlobals] ++
             [('_':name, IsStrict, [t| Class |])
             | name <- pyonClasses]
