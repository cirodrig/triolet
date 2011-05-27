
module Type.Eval
       (reduceToWhnf,
        normalize,
        typeKind,
        typeCheckType,
        typeOfTypeApp,
        typeOfApp,
        dataConFieldKinds,
        unboxedTupleTyCon,
        unboxedTupleType,
        instantiateDataConType,
        instantiateDataConTypeWithFreshVariables,
        instantiateDataConTypeWithExistentials)
where

import Control.Monad.Reader
import Debug.Trace

import Common.Error
import Common.Identifier
import Common.MonadLogic
import Common.SourcePos
import Common.Supply
import Type.Compare
import Type.Environment
import Type.Rename
import Type.Type

-- | Evaluate a type as much as possible.
--   The type is assumed to be well-kinded.
normalize :: EvalMonad m => Type -> m Type
normalize t =
  -- Recursively reduce to WHNF
  normalize_recursive =<< reduceToWhnf t
  where
    normalize_recursive t = 
      case t
      of VarT {} -> return t
         AppT op arg ->
           AppT `liftM` normalize op `ap` normalize arg
         LamT (x ::: k) body ->
           LamT (x ::: k) `liftM` assume x k (normalize body)
         FunT dom rng ->
           FunT `liftM` normalize dom `ap` normalize rng
         AllT (x ::: k) rng ->
           AllT (x ::: k) `liftM` assume x k (normalize rng)
         AnyT {} -> return t
         IntT {} -> return t
         UTupleT {} -> return t

-- | Get the type of a type.
--   Minimal error checking is performed.
typeKind :: TypeEnv -> Type -> Type
typeKind tenv ty =
  case ty
  of VarT v ->
       case lookupType v tenv
       of Just k -> k
          _ -> internalError $ "typeKind: No type for variable: " ++ show v
     IntT _ -> intindexT
     AppT op _ ->
       -- Assume the application is properly typed.  Get the kind of the
       -- operator's range.
       case typeKind tenv op
       of _ `FunT` k -> k
          _ -> internalError "typeKind: Malformed application"
     LamT (x ::: param_k) ret_t ->
       -- A lambda function has an arrow kind
       let ret_k = typeKind (insertType x param_k tenv) ret_t
       in param_k `FunT` ret_k
     FunT _ rng ->
       case getLevel rng
       of TypeLevel -> boxT     -- Functions are always boxed
          KindLevel -> kindT
     AllT (_ ::: _) rng ->
       case getLevel rng
       of TypeLevel -> boxT     -- Functions are always boxed
          KindLevel -> internalError "typeKind: Unexpected type"
     UTupleT ks -> funType (map fromBaseKind ks) valT
     _ -> internalError "typeKind: Unrecognized type"

-- | Typecheck a type or kind.  If the term is valid, return its type,
--   which is the same as what 'typeKind' returns.  Otherwise, raise an
--   error.
typeCheckType :: Type -> TypeEvalM Type
typeCheckType ty =
  case ty
  of VarT v -> do
       tenv <- getTypeEnv
       case lookupType v tenv of 
         Just t -> return t
         Nothing ->
           internalError $ "typeCheckType: No type for variable: " ++ show v
     AppT op arg -> do
       -- Get type of op and argument
       op_k <- typeCheckType op
       arg_k <- typeCheckType arg
           
       -- Get type of application
       applied <- typeOfApp op_k arg_k
       case applied of
         Nothing -> trace (show (pprType ty) ++ "\n" ++ show (pprType op_k) ++ "\n" ++ show (pprType arg_k)) $ internalError "typeCheckType: Error in type application"
         Just result_t -> return result_t

     FunT dom rng -> do
       -- Check that types are valid
       typeCheckType dom
       typeCheckType rng
       return $! case getLevel rng
                 of TypeLevel -> boxT
                    KindLevel -> kindT

     LamT (v ::: dom) body -> do
       -- Get types of domain and range
       _ <- typeCheckType dom
       body_kind <- assume v dom $ typeCheckType body
       return $! case getLevel body
                 of TypeLevel -> FunT dom body_kind
                    _ -> internalError "typeCheckType: Unexpected type"

     AllT (v ::: dom) rng -> do
       -- Check that domain and range are valid
       typeCheckType dom
       assume v dom $ typeCheckType rng
       return $! case getLevel rng
                 of TypeLevel -> boxT
                    _ -> internalError "typeCheckType: Unexpected type"

     AnyT k -> return k
     IntT _ -> return intindexT
     UTupleT ks
       | all valid_unboxed_tuple_field ks ->
           return $ funType (map fromBaseKind ks) valT
       | otherwise -> internalError "typeCheckType: Invalid unboxed tuple type"
  where
    valid_unboxed_tuple_field ValK = True
    valid_unboxed_tuple_field BoxK = True
    valid_unboxed_tuple_field _ = False

-- | Compute the type produced by applying a value of type @op_type@ to
--   the type argument @arg@.  Verify that the application is well-typed.
typeOfTypeApp :: Type               -- ^ Operator type
              -> Kind               -- ^ Argument kind
              -> Type               -- ^ Argument
              -> TypeEvalM (Maybe Type)
typeOfTypeApp op_type arg_kind arg = do
  whnf_op_type <- reduceToWhnf op_type
  case whnf_op_type of
    AllT (x ::: dom) rng -> do
      type_ok <- compareTypes dom arg_kind
      if type_ok
        then fmap Just $ substitute (singletonSubstitution x arg) rng
        else return Nothing
    _ -> return Nothing

-- | Compute the type produced by applying a value of type @op_type@ to
--   a value of type @arg_type@.  Verify that the application is well-typed.
typeOfApp :: Type               -- ^ Operator type
          -> Type               -- ^ Argument type
          -> TypeEvalM (Maybe Type)
typeOfApp op_type arg_type = do
  whnf_op_type <- reduceToWhnf op_type
  case whnf_op_type of
    FunT dom rng -> do
      type_ok <- compareTypes dom arg_type
      if type_ok
        then return (Just rng)
        else return Nothing
    _ -> return Nothing

-- | Get the kinds of a data constructor's fields.
dataConFieldKinds :: TypeEnv -> DataConType -> [BaseKind]
dataConFieldKinds tenv dcon_type =
  let local_tenv =
        foldr insert_binder_type tenv $
        dataConPatternParams dcon_type ++ dataConPatternExTypes dcon_type
        where
          insert_binder_type (v ::: t) e = insertType v t e
  in [toBaseKind $ typeKind local_tenv t | t <- dataConPatternArgs dcon_type]

-- | Create an unboxed tuple type constructor that can hold 
--   the given sequence of types.
unboxedTupleTyCon :: TypeEnv -> [Type] -> Type
unboxedTupleTyCon tenv ts =
  -- Force kinds to be evaluated eagerly, so errors are detected sooner
  UTupleT $! convert_types ts
  where
    convert_types (t:ts) = (convert_type t :) $! convert_types ts
    convert_types []     = []
    
    convert_type t =
      case toBaseKind $ typeKind tenv t
      of ValK -> ValK
         BoxK -> BoxK
         _ -> internalError "unboxedTupleTyCon: Invalid kind for tuple"

-- | Create the type of an unboxed tuple whose fields are the given types
unboxedTupleType :: TypeEnv -> [Type] -> Type
unboxedTupleType tenv ts =
  let con = unboxedTupleTyCon tenv ts
  in con `seq` typeApp con ts

-- | Given a data constructor type and the type arguments at which it's used,
--   get the instantiated type.
--
--   Returns the existential type parameters, the data constructor fields'
--   types as they appear in a pattern match, and the constructed value's type.
-- The types are not typechecked.
instantiateDataConType :: EvalMonad m =>
                          DataConType -- ^ Type to instantiate
                       -> [Type]      -- ^ Type parameters
                       -> [Var]       -- ^ Existential variable names to
                                      -- instantiate to
                       -> m ([Binder], [Type], Type)
instantiateDataConType con_ty arg_vals ex_vars
  | length (dataConPatternParams con_ty) /= length arg_vals =
      internalError "instantiateDataConType: Wrong number of type parameters"
  | length (dataConPatternExTypes con_ty) /= length ex_vars =
      internalError "instantiateDataConType: Wrong number of existential variables"
  | otherwise = do
      let -- Assign parameters
          subst1 = instantiate_arguments emptySubstitution $
                   zip (dataConPatternParams con_ty) arg_vals

          -- Rename existential types, if new variables are given
          (subst2, ex_params) = instantiate_exvars subst1 $
                                zip (dataConPatternExTypes con_ty) ex_vars

      -- Apply substitution to range type.  Use subst1 because existential
      -- variables cannot appear in the range.
      range <- substitute subst1 $ dataConPatternRange con_ty

      -- Apply the substitution to field and range types
      fields <- mapM (substitute subst2) $ dataConPatternArgs con_ty
      return (ex_params, fields, range)
  where
    -- Instantiate the type by substituing arguments for the constructor's
    -- type parameters
    instantiate_arguments :: Substitution -> [(Binder, Type)]
                          -> Substitution
    instantiate_arguments subst ((param_var ::: _, arg_val) : args) =
      let subst' = insertSubstitution param_var arg_val subst
      in instantiate_arguments subst' args
  
    instantiate_arguments subst' [] = subst'

    -- Instantiate existential types.  Rename each existential variable.
    instantiate_exvars :: Substitution -> [(Binder, Var)]
                       -> (Substitution, [Binder])
    instantiate_exvars subst ((old_ex_var ::: extype, ex_var) : params) =
      let subst' = insertSubstitution old_ex_var (VarT ex_var) subst
          !(subst'', params') = instantiate_exvars subst' params
      in (subst'', ex_var ::: extype : params')
    
    instantiate_exvars subst [] = (subst, [])

-- | Like 'instantiateDataConType', but each existential variable is given
--   a fresh name.
instantiateDataConTypeWithFreshVariables :: 
    EvalMonad m =>
    DataConType -- ^ Type to instantiate
 -> [Type]      -- ^ Type parameters
 -> m ([Binder], [Type], Type)
instantiateDataConTypeWithFreshVariables con_ty arg_vals = do
  pattern_vars <- replicateM (length $ dataConPatternExTypes con_ty) $
                  newAnonymousVar TypeLevel
  instantiateDataConType con_ty arg_vals pattern_vars

-- | Given a data constructor type and the type arguments at which it's used,
--   including existential types, get the instantiated type.
--
--   Returns the the data constructor fields'
--   types as they appear in a pattern match and the constructed value's type.
-- The types are not typechecked.
instantiateDataConTypeWithExistentials ::
    EvalMonad m =>
    DataConType -- ^ Type to instantiate
 -> [Type]      -- ^ Type parameters and existential types
 -> m ([Type], Type)
instantiateDataConTypeWithExistentials con_ty arg_vals
  | length (dataConPatternParams con_ty) +
    length (dataConPatternExTypes con_ty) /= length arg_vals =
      internalError $ "instantiateDataConTypeWithExistentials: " ++
                      "Wrong number of type parameters"
  | otherwise = do
      let -- Assign parameters and existential types
          type_params =
            dataConPatternParams con_ty ++ dataConPatternExTypes con_ty
          subst = instantiate_arguments emptySubstitution $
                  zip type_params arg_vals

      -- Apply the substitution to field and range types
      fields <- mapM (substitute subst) $ dataConPatternArgs con_ty
      range <- substitute subst $ dataConPatternRange con_ty
      return (fields, range)
  where
    -- Instantiate the type by substituing arguments for the constructor's
    -- type parameters
    instantiate_arguments :: Substitution -> [(Binder, Type)]
                          -> Substitution
    instantiate_arguments subst ((param_var ::: _, arg_val) : args) =
      let subst' = insertSubstitution param_var arg_val subst
      in instantiate_arguments subst' args
  
    instantiate_arguments subst' [] = subst'

