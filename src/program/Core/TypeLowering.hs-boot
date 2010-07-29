
module Core.TypeLowering where

import Gluon.Core
import Core.Syntax
import LowLevel.Syntax as LL

valueType :: RCType -> LL.ValueType
lowerExpressionType :: CBind CReturnT Rec -> LL.ValueType
lowerFunctionType :: RCFunType -> LL.FunctionType
conLoweredFunctionType :: Con -> LL.FunctionType
