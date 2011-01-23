
module Type.Eval where

import Control.Monad.Reader

import Gluon.Common.Error
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

-- | Given a data constructor type and the type arguments it will be applied
--   to, get the types of the data constructor fields and the
--   constructed value.  The types are not typechecked. 
instantiateDataConType :: DataConType -> [Type]
                       -> ([ReturnType], ReturnType)
instantiateDataConType con_ty arg_vals
  | length (dataConPatternParams con_ty) /= length arg_vals =
      internalError "instantiateDataConType"
  | otherwise =
      let subst = instantiate_arguments emptySubstitution $
                  zip (dataConPatternParams con_ty) arg_vals

          -- Apply the substitution to field and range types
          fields = map (substituteBinding subst) $ dataConPatternArgs con_ty
          range = substituteBinding subst $ dataConPatternRange con_ty
      in (fields, range)
  where
    -- Instantiate the type by substituing arguments for the constructor's
    -- type parameters
    instantiate_arguments subst ((param_repr ::: _, arg_val) : args) =
      let subst' = case param_repr
                   of ValPT (Just param_var) ->
                        insertSubstitution param_var arg_val subst
      in instantiate_arguments subst' args
  
    instantiate_arguments subst' [] = subst'