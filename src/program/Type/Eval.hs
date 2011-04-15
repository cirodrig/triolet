
module Type.Eval
       (typeOfApp,
        instantiateDataConType,
        instantiateDataConTypeWithFreshVariables,
        instantiateDataConTypeWithExistentials)
where

import Control.Monad.Reader

import Common.Error
import Common.Identifier
import Common.MonadLogic
import Common.SourcePos
import Common.Supply
import Type.Compare
import Type.Environment
import Type.Rename
import Type.Type

-- Need a monad supplying ... for reduction

-- | Reduce a type to weak head-normal form.  Evaluate type functions
--   that are in head position.
reduceToWhnf :: Type -> TypeEvalM Type
reduceToWhnf ty =
  case fromVarApp ty
  of Just (op, args) | not (null args) -> do
       env <- getTypeEnv
       case lookupTypeFunction op env of
         Nothing    -> return ty
         Just tyfun -> applyTypeFunction tyfun args
     _ -> return ty
     

-- | Compute the type produced by applying a value of type @op_type@ to
--   a value of type @arg_type@.
typeOfApp :: IdentSupply Var
          -> TypeEnv
          -> Type               -- ^ Operator type
          -> ReturnType         -- ^ Argument type and representation
          -> Maybe Type         -- ^ Argument value; only used if operator is
                                --   dependent
          -> IO (Maybe ReturnType)
typeOfApp id_supply env op_type (arg_repr ::: arg_type) m_arg =
  case op_type
  of FunT (fun_arg ::: dom) result 
       | repr_match fun_arg arg_repr -> do
           type_ok <- compareTypes id_supply env dom arg_type
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

-- | Given a data constructor type and the type arguments at which it's used,
--   get the instantiated type.
--
--   Returns the existential type parameters, the data constructor fields'
--   types as they appear in a pattern match, and the constructed value's type.
-- The types are not typechecked.
instantiateDataConType :: DataConType -- ^ Type to instantiate
                       -> [Type]      -- ^ Type parameters
                       -> [Var]       -- ^ Existential variable names to
                                      -- instantiate to
                       -> ([ParamType], [ReturnType], ReturnType)
instantiateDataConType con_ty arg_vals ex_vars
  | length (dataConPatternParams con_ty) /= length arg_vals =
      internalError "instantiateDataConType: Wrong number of type parameters"
  | length (dataConPatternExTypes con_ty) /= length ex_vars =
      internalError "instantiateDataConType: Wrong number of existential variables"
  | otherwise =
      let -- Assign parameters
          subst1 = instantiate_arguments emptySubstitution $
                   zip (dataConPatternParams con_ty) arg_vals

          -- Rename existential types, if new variables are given
          (subst2, ex_params) = instantiate_exvars subst1 $
                                zip (dataConPatternExTypes con_ty) ex_vars

          -- Apply the substitution to field and range types.
          fields = map (substituteBinding subst2) $ dataConPatternArgs con_ty
          -- Use subst1 because existential variables cannot appear
          -- in the range.
          range = substituteBinding subst1 $ dataConPatternRange con_ty
      in (ex_params, fields, range)
  where
    -- Instantiate the type by substituing arguments for the constructor's
    -- type parameters
    instantiate_arguments :: Substitution -> [(ParamType, Type)]
                          -> Substitution
    instantiate_arguments subst ((param_repr ::: _, arg_val) : args) =
      let subst' = case param_repr
                   of ValPT (Just param_var) ->
                        insertSubstitution param_var arg_val subst
      in instantiate_arguments subst' args
  
    instantiate_arguments subst' [] = subst'

    -- Instantiate existential types.  Rename each existential variable.
    instantiate_exvars :: Substitution -> [(ParamType, Var)]
                       -> (Substitution, [ParamType])
    instantiate_exvars subst ((param_repr ::: extype, ex_var) : params) =
      let old_ex_var = case param_repr
                       of ValPT (Just old_ex_var) -> old_ex_var
          subst' = insertSubstitution old_ex_var (VarT ex_var) subst
          !(subst'', params') = instantiate_exvars subst' params
      in (subst'', ValPT (Just ex_var) ::: extype : params')
    
    instantiate_exvars subst [] = (subst, [])

-- | Like 'instantiateDataConType', but each existential variable is given
--   a fresh name.
instantiateDataConTypeWithFreshVariables :: 
    DataConType -- ^ Type to instantiate
 -> [Type]      -- ^ Type parameters
 -> FreshVarM ([ParamType], [ReturnType], ReturnType)
instantiateDataConTypeWithFreshVariables con_ty arg_vals = do
  pattern_vars <- replicateM (length $ dataConPatternExTypes con_ty) $
                  newAnonymousVar TypeLevel
  return $ instantiateDataConType con_ty arg_vals pattern_vars

-- | Given a data constructor type and the type arguments at which it's used,
--   including existential types, get the instantiated type.
--
--   Returns the the data constructor fields'
--   types as they appear in a pattern match and the constructed value's type.
-- The types are not typechecked.
instantiateDataConTypeWithExistentials ::
    DataConType -- ^ Type to instantiate
 -> [Type]      -- ^ Type parameters and existential types
 -> ([ReturnType], ReturnType)
instantiateDataConTypeWithExistentials con_ty arg_vals
  | length (dataConPatternParams con_ty) +
    length (dataConPatternExTypes con_ty) /= length arg_vals =
      internalError $ "instantiateDataConTypeWithExistentials: " ++
                      "Wrong number of type parameters"
  | otherwise =
      let -- Assign parameters and existential types
          type_params =
            dataConPatternParams con_ty ++ dataConPatternExTypes con_ty
          subst = instantiate_arguments emptySubstitution $
                  zip type_params arg_vals

          -- Apply the substitution to field and range types
          fields = map (substituteBinding subst) $ dataConPatternArgs con_ty
          range = substituteBinding subst $ dataConPatternRange con_ty
      in (fields, range)
  where
    -- Instantiate the type by substituing arguments for the constructor's
    -- type parameters
    instantiate_arguments :: Substitution -> [(ParamType, Type)]
                          -> Substitution
    instantiate_arguments subst ((param_repr ::: _, arg_val) : args) =
      let subst' = case param_repr
                   of ValPT (Just param_var) ->
                        insertSubstitution param_var arg_val subst
      in instantiate_arguments subst' args
  
    instantiate_arguments subst' [] = subst'
