
module Untyped.BuiltinsTH2 where

import qualified Language.Haskell.TH as TH

-- | All predefined data type names recognized by the Triolet parser
frontendSourceTypes :: [String] 
frontendSourceTypes =
  ["int", "float", "bool", "NoneType", "int64",
   "iter", "list",
   "array0", "array1", "array2", "array3",
   "blist", "barray1", "barray2", "barray3",
   "Maybe", "intset", "llist",
   "shape", "list_dim", "dim0", "dim1", "dim2", "dim3",
   "index", "slice", "offset", "cartesianDomain",
   "view",
   "Collector",

   -- Classes
   "Repr", "Mutable", "Functor", "Traversable", "Shape", "Indexable",
   "Eq", "Ord",
   "Additive", "Multiplicative",
   "Remainder", "Fractional",
   "Floating",
   "Cartesian"]

-- | Predefined data types not visible to the Triolet parser
frontendOtherTypes :: [String]
frontendOtherTypes =
  ["SliceObject", "SomeIndexable", "Subdomain", "StuckRef"]

-- | All predefined global functions recognized by the Triolet parser
frontendSourceGlobals :: [String]
frontendSourceGlobals =
  [ "Just"
  , "Nothing"
  , "isJust"
  , "isNothing"
  , "fromJust"
  , "list_dim"
  , "dim0"
  , "dim2"
  , "dim3"
  , "cons"
  , "nil"
  , "isCons"
  , "isNil"
  , "head"
  , "tail"
  , "map"
  , "reduce"
  , "reduce1"
  , "filter"
  , "sum"
  , "zip"
  , "zip3"
  , "zip4"
  , "collect"
  , "histogram"
  , "count"
  , "par"
  , "localpar"
  , "seq"
  , "range"
  , "indices"
  , "len"
  , "arrayRange"
  , "rows"
  , "outerproduct"
  {-, "chain"
  , "singletonIter"
  , "width"
  , "height"
  , "cols"
  , "displaceView"
  , "multiplyView"
  , "divideView"-}
  , "testCopyViaBuffer"
  {-, "permute1D"
  , "boxedPermute1D"
  , "stencil2D"
  , "boxedStencil2D"
  , "extend2D"
  , "stencil3D"
  , "boxedStencil3D"
  , "extend3D"
  , "unionView3D"
  , "histogram"-}
  , "floor"
  , "valueCollector"
  , "listCollector"
  , "array3Collector"
  {-, "intScatter"
  , "floatScatter"
  , "boolScatter"
  , "intSumScatter"
  , "floatSumScatter"
  , "countingScatter"
  , "boxedScatter"
  , "appendScatter"
  , "listScatter"
  , "array1Scatter"
  , "array2Scatter"
  , "array3Scatter"
  , "blistScatter"
  , "barray1Scatter"
  , "barray2Scatter"
  , "barray3Scatter"
  , "scatter"
  , "intset"
  , "intsetLookup"
  , "intsetElements"-}
  , "__undefined__"
  , "__and__"
  , "__or__"
  , "__xor__"
  , "and"
  , "or"
  , "not"
  , "__getitem__"
  , "__getslice__"
    -- Class methods
  , "__eq__"
  , "__ne__"
  , "__lt__"
  , "__le__"  
  , "__gt__"
  , "__ge__"
  , "domain"
  , "unsafeIndex"
  , "intersection"
  , "flatten"
  , "iter"
  , "build"
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
  , "__lshift__"
  , "__rshift__"
  --, "scale"
  --, "magnitude"
  --, "dot"
  , "loBound"
  , "hiBound"
  , "stride"
  , "arrayDomain"
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
frontendOtherGlobals :: [String]
frontendOtherGlobals =
  [ "do", "guard", "iterBind",
    "safeIndex", "safeSlice",
    "member",
    "generate",
    "zipWithStream",
    "at_point",
    "displaceDomain", "multiplyDomain", "divideDomain",
    "multiplyIndex", "divideIndex",
    "make_sliceObject"
  ]

tcName s = TH.mkName $ "TheTC_" ++ s

vName s = TH.mkName $ "TheV_" ++ s