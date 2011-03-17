
module SystemF.Lowering.Datatypes2 where

import Common.Identifier
import qualified LowLevel.Syntax as LL
import qualified LowLevel.CodeTypes as LL
import Type.Type
import Type.Environment

lowerFunctionType :: IdentSupply LL.Var -> IdentSupply Var -> TypeEnv -> Type
                  -> IO LL.FunctionType
