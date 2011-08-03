
{-# LANGUAGE TemplateHaskell #-}
module Untyped.BuiltinsTH where

import Language.Haskell.TH(Strict(..))
import Language.Haskell.TH.Syntax(Lift(..))
import Common.THRecord
import qualified Type.Var
import Untyped.Data
import Untyped.Kind
import Untyped.Syntax

instance Lift Kind where
  lift Star = [| Star |]
  lift (k1 :-> k2) = [| k1 :-> k2 |]

-- | All predefined data type names recognized by the Pyon parser
pyonSourceTypes :: [String] 
pyonSourceTypes =
  ["int", "float", "Complex", "bool", "NoneType", "iter", "list", "matrix",
   "ListView", "MatrixView", "ListShapeEliminator", "MatrixShapeEliminator",
   "Any", "shape"]

-- | All predefined global functions recognized by the Pyon parser
pyonSourceGlobals :: [String]
pyonSourceGlobals =
  [ "map"
  , "reduce"
  , "reduce1"
  , "zip"
  , "zip3"
  , "zip4"
  , "count"
  , "range"
  , "len"
  , "width"
  , "height"
  , "histogram"
  , "listiter"
  , "matrixiter"
  , "floor"
  , "__undefined__"
  , "__and__"
  , "__or__"
  , "__xor__"
  , "complex"
    -- Class methods
  , "__eq__"
  , "__ne__"
  , "__lt__"
  , "__le__"  
  , "__gt__"
  , "__ge__"
  , "__iter__"
  , "__build__"
  , "__add__"
  , "__sub__"
  , "__negate__"
  , "zero"
  , "__mul__"
  , "__fromint__"
  , "one"
  , "__mod__"
  , "__floordiv__"
  , "__div__"
  , "scale"
  , "magnitude"
  , "dot"
  , "__fromfloat__"
  , "__power__"
  , "exp"
  , "log"
  , "sqrt"
  , "sin"
  , "cos"
  , "tan"
  , "pi"
  ]

-- | Global variables that can't be referred to by name 
pyonOtherGlobals :: [String]
pyonOtherGlobals =
  [ "do", "guard", "iterBind",
    "safeIndex", "safeSlice",
    "safeIndex2", "safeSlice2",
    "flattenStream", "mapStream", "zipWithStream", "zipWith3Stream", "zipWith4Stream",
    "at_point", "at_slice", "with_shape",
    "at_point2", "at_slice2", "with_shape2"
  ]

-- | All predefined class names
pyonClasses :: [String]
pyonClasses =
  ["Repr", "Traversable", "Shape", "Indexable", "Indexable2",
   "Eq", "Ord",
   "Additive", "Multiplicative",
   "Remainder", "Fractional",
   "Floating",
   "Vector"]

-- Global variable fields are not strict because some of them are built 
-- using fields of the builtins table.  Class fields are strict, but most 
-- of their fields are not for the same reason.
tiBuiltinSpecification =
  recordDef "TIBuiltins" fields
  where
    fields = [('_':name, IsStrict, [t| Type.Var.Var |])
             | name <- pyonSourceTypes ] ++ 
             [("_con_" ++ name, IsStrict, [t| TyCon |])
             | name <- pyonSourceTypes] ++
             [('_':name, NotStrict, [t| Variable |])
             | name <- pyonSourceGlobals ++ pyonOtherGlobals] ++
             [('_':name, IsStrict, [t| Class |])
             | name <- pyonClasses]

