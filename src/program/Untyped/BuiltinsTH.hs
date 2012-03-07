
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
  ["int", "float", "Complex", "bool", "NoneType", "iter", "list",
   "array", "array0", "array1", "array2", "array3",
   "blist", "barray1", "barray2", "barray3",
   "Maybe", "Any",
   "shape", "list_dim", "dim0", "dim1", "dim2", "dim3",
   "index", "slice", "cartesianDomain",
   "view",
   "Scatter"]

-- | Predefined data types not visible to the Pyon parser
pyonOtherTypes :: [String]
pyonOtherTypes =
  ["SliceObject", "MaybeVal"]

-- | All predefined global functions recognized by the Pyon parser
pyonSourceGlobals :: [String]
pyonSourceGlobals =
  [ "Just"
  , "Nothing"
  , "isJust"
  , "isNothing"
  , "fromJust"
  , "list_dim"
  , "dim1"
  , "dim2"
  , "dim3"
  , "map"
  , "reduce"
  , "reduce1"
  , "zip"
  , "zip3"
  , "zip4"
  , "count"
  , "range"
  , "chain"
  , "singletonIter"
  , "indices"
  , "len"
  , "width"
  , "height"
  , "rows"
  , "cols"
  , "outerproduct"
  , "displaceView"
  , "multiplyView"
  , "divideView"
  , "view2"
  , "stencil2D"
  , "boxedStencil2D"
  , "extend2D"
  , "stencil3D"
  , "extend3D"
  , "histogram"
  , "matrixiter"
  , "floor"
  , "intSumScatter"
  , "floatSumScatter"
  , "countingScatter"
  , "array1Scatter"
  , "array2Scatter"
  , "array3Scatter"
  , "scatter"
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
  , "domain"
  , "intersection"
  , "flatten"
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
  , "loBound"
  , "hiBound"
  , "stride"
  , "arrayRange"
  , "unbounded"
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
    "member",
    "generate",
    "mapStream", "zipWithStream", "zipWith3Stream", "zipWith4Stream",
    "getSlice",
    "at_point",
    "displaceDomain", "multiplyDomain", "divideDomain",
    "multiplyIndex", "divideIndex",
    "sliceObject", "justVal", "nothingVal"
  ]

-- | All predefined class names
pyonClasses :: [String]
pyonClasses =
  ["Repr", "Traversable", "Shape", "Indexable",
   "Eq", "Ord",
   "Additive", "Multiplicative",
   "Remainder", "Fractional",
   "Floating",
   "Vector",
   "Cartesian"]

-- Global variable fields are not strict because some of them are built 
-- using fields of the builtins table.  Class fields are strict, but most 
-- of their fields are not for the same reason.
tiBuiltinSpecification =
  recordDef "TIBuiltins" fields
  where
    fields = [('t':'_':name, IsStrict, [t| Type.Var.Var |])
             | name <- pyonSourceTypes ++ pyonOtherTypes] ++ 
             [("con_" ++ name, IsStrict, [t| TyCon |])
             | name <- pyonSourceTypes ++ pyonOtherTypes] ++
             [('v':'_':name, NotStrict, [t| Variable |])
             | name <- pyonSourceGlobals ++ pyonOtherGlobals] ++
             [('c':'_':name, IsStrict, [t| Class |])
             | name <- pyonClasses]

