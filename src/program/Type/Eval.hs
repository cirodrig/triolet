
module Type.Eval where

import Control.Monad.Reader

import Gluon.Common.Identifier
import Gluon.Common.MonadLogic
import Gluon.Common.SourcePos
import Gluon.Common.Supply
import Type.Compare
import Type.Environment
import Type.Rename
import Type.Type
import Type.Var

-- | Compute the type produced by applying a value of type @op_type@ to
--   a value of type @arg_type@.
typeOfApp :: IdentSupply Var
          -> SourcePos
          -> TypeEnv
          -> Type               -- ^ Operator type
          -> Type               -- ^ Argument type
          -> Maybe Type         -- ^ Argument value; only used if operator is
                                --   dependent
          -> IO (Maybe (ReturnRepr ::: Type))
typeOfApp id_supply pos env op_type arg_type m_arg =
  case op_type
  of FunT (fun_arg ::: dom) result -> do
       type_ok <- compareTypes id_supply pos env dom arg_type
       if type_ok
         then apply fun_arg m_arg result
         else return Nothing
     _ -> return Nothing
  where
    apply (ValPT (Just pv)) (Just arg) result =
      let subst = singletonSubstitution pv arg
          result' = substituteBinding subst result
      in return (Just result')

    -- Dependent type, but missing argument value
    apply (ValPT (Just _)) Nothing _ = return Nothing
  
    -- Non-dependent type
    apply _ _ result = return (Just result)
