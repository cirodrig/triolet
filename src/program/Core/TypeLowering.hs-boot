
module Core.TypeLowering where

import Gluon.Core
import Core.Syntax
import LowLevel.Syntax as LL
import LowLevel.CodeTypes

valueType :: RCType -> ValueType
lowerExpressionType :: CBind CReturnT Rec -> ValueType
lowerFunctionType :: RCFunType -> FunctionType
conLoweredFunctionType :: Con -> FunctionType
