
module SystemF.Lowering.Datatypes where

import qualified LowLevel.CodeTypes as LL
import Type.Type
import Type.Environment

lowerFunctionType :: TypeEnv -> Type -> LL.FunctionType
