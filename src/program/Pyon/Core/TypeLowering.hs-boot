
module Pyon.Core.TypeLowering where

import Gluon.Core
import Pyon.Core.Syntax
import Pyon.LowLevel.Syntax as LL

valueType :: RCType -> LL.ValueType
lowerExpressionType :: CBind CReturnT Rec -> LL.ValueType
lowerFunctionType :: RCFunType -> LL.FunctionType
conLoweredFunctionType :: Con -> LL.FunctionType
