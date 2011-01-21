
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
          -> ReturnType         -- ^ Argument type and representation
          -> Maybe Type         -- ^ Argument value; only used if operator is
                                --   dependent
          -> IO (Maybe ReturnType)
typeOfApp id_supply pos env op_type (arg_repr ::: arg_type) m_arg =
  case op_type
  of FunT (fun_arg ::: dom) result 
       | repr_match fun_arg arg_repr -> do
           type_ok <- compareTypes id_supply pos env dom arg_type
           if type_ok
             then apply fun_arg m_arg result
             else return Nothing
     _ -> return Nothing
  where
    -- Does the function's expected representation match the argument's
    -- actual representation?
    repr_match (ValPT _) ValRT = True
    repr_match BoxPT BoxRT = True
    repr_match ReadPT ReadRT = True 
    repr_match WritePT WriteRT = True
    repr_match OutPT OutRT = True
    repr_match SideEffectPT SideEffectRT = True
    repr_match _ _ = False

    apply (ValPT (Just pv)) (Just arg) result =
      let subst = singletonSubstitution pv arg
          result' = substituteBinding subst result
      in return (Just result')

    -- Dependent type, but missing argument value
    apply (ValPT (Just _)) Nothing _ = return Nothing
  
    -- Non-dependent type
    apply _ _ result = return (Just result)
