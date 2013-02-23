
module Type.Eval
       (reduceToWhnf,
        normalize,

        -- * Computing and checking types
        typeKind,
        typeBaseKind,
        typeCheckType,
        typeOfTypeApp,
        typeOfApp,

        -- * Deconstructing types
        deconVarAppType,
        deconFunType,
        deconAllType,
        deconUniversalType,
        deconFunctionType,
        deconForallFunType,

        -- * Other functions
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
import qualified Type.Rename as Rename
import Type.Substitute(TypeSubst, Substitutable(..), substitute)
import qualified Type.Substitute as Substitute
import Type.Type
import Type.Error

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
         CoT {} -> return t
         UTupleT {} -> return t

-- | Get the type of a type, as a base kind.
--   Minimal error checking is performed.
typeBaseKind :: EvalMonad m => Type -> m BaseKind
typeBaseKind ty = toBaseKind `liftM` typeKind ty

-- | Get the type of a type.
--   Minimal error checking is performed.
typeKind :: EvalMonad m => Type -> m Type
typeKind ty = liftTypeEvalM $ typeKind' ty

typeKind' :: BoxingMode b => Type -> TypeEvalM b Type
typeKind' ty =
  case ty
  of VarT v -> do
       m_k <- lookupType v
       return $! case m_k
                 of Just k -> k
                    _ -> internalError $ "typeKind: No type for variable: " ++ show v
     IntT _ -> return intindexT
     AppT op _ -> do
       -- Assume the application is properly typed.  Get the kind of the
       -- operator's range.
       FunT _ k <- typeKind' op
       return k
     LamT (x ::: param_k) ret_t -> do
       ret_k <- assume x param_k $ typeKind' ret_t

       -- A lambda function has an arrow kind
       return $ param_k `FunT` ret_k
     FunT _ rng ->
       return $! case getLevel rng
                 of TypeLevel -> boxT     -- Functions are always boxed
                    KindLevel -> kindT
     AllT (x ::: param_k) rng ->
       -- Kind of 'forall' is the kind of its range
       assume x param_k $ typeKind' rng
     CoT k ->
       -- Kind of a coercion is k -> k -> val
       return $ k `FunT` k `FunT` valT
     UTupleT ks -> return $ funType (map fromBaseKind ks) valT
     _ -> internalError "typeKind: Unrecognized type"

-- | Typecheck a type or kind.  If the term is valid, return its type,
--   which is the same as what 'typeKind' returns.  Otherwise, raise an
--   error.
typeCheckType :: BoxingMode b => Type -> TypeEvalM b Type
typeCheckType ty =
  case ty
  of VarT v -> do
       m_t <- lookupType v
       case m_t of 
         Just t -> return t
         Nothing ->
           internalError $ "typeCheckType: No type for variable: " ++ show v
     AppT op arg -> do
       -- Get type of op and argument
       op_k <- typeCheckType op
       arg_k <- typeCheckType arg
           
       -- Get type of application
       typeOfApp noSourcePos 1 op_k arg_k

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
       -- Check that domain is valid
       typeCheckType dom
       -- Add domain to environment
       -- Return the range's kind
       assume v dom $ typeCheckType rng

     AnyT k -> return k
     IntT _ -> return intindexT
     CoT k -> do
       -- Check that the coercion kind is valid
       typeCheckType k

       -- Kind of a coercion is k -> k -> val
       return (k `FunT` k `FunT` valT)
     UTupleT ks
       | all valid_unboxed_tuple_field ks ->
           return $ funType (map fromBaseKind ks) valT
       | otherwise -> internalError "typeCheckType: Invalid unboxed tuple type"
  where
    valid_unboxed_tuple_field ValK = True
    valid_unboxed_tuple_field BoxK = True
    valid_unboxed_tuple_field _ = False

-- | Compute the type produced by applying a value of type @op_type@ to
--   the type argument @arg@.
--   Raise an exception on type error.
typeOfTypeApp :: BoxingMode b =>
                 SourcePos          -- ^ Location of type application
              -> Int                -- ^ Ordinal position of type argument,
                                    --   for error reporting
              -> Type               -- ^ Operator type
              -> Kind               -- ^ Argument kind
              -> Type               -- ^ Argument
              -> TypeEvalM b Type
typeOfTypeApp pos arg_index op_type arg_kind arg = do
  whnf_op_type <- reduceToWhnf op_type
  case whnf_op_type of
    AllT (x ::: dom) rng -> do
      type_ok <- compareTypes dom arg_kind
      if type_ok
        then Substitute.substituteVar x arg rng
        else throwTypeError $ typeArgKindMismatch pos arg_index dom arg_kind
    _ -> throwTypeError $ badTypeApplication pos whnf_op_type arg_kind

-- | Compute the type produced by applying a value of type @op_type@ to
--   a value of type @arg_type@, or a type of kind @op_type@ to a type of
--   kind @arg_type@.  Verify that the application is well-typed or
--   well-kinded.
typeOfApp :: BoxingMode b =>
             SourcePos          -- ^ Location of type application
          -> Int                -- ^ Ordinal position of type argument,
                                --   for error reporting
          -> Type               -- ^ Operator type
          -> Type               -- ^ Argument type
          -> TypeEvalM b Type
typeOfApp pos arg_index op_type arg_type = do
  whnf_op_type <- reduceToWhnf op_type
  case whnf_op_type of
    FunT dom rng -> do
      type_ok <- compareTypes dom arg_type
      if type_ok
        then return rng
        else throwTypeError $ argTypeMismatch pos arg_index dom arg_type
    _ -> throwTypeError $ badApplication pos whnf_op_type arg_type

-- | Given a type of the form @c t1 ... tN@, return @c@ and @t1 ... tN@.
deconVarAppType :: BoxingMode b => Type -> TypeEvalM b (Maybe (Var, [Type]))
{-# INLINE deconVarAppType #-}
deconVarAppType t = do
  t' <- reduceToWhnf t
  case fromTypeApp t' of
    (VarT op, args) -> return $ Just (op, args)
    _ -> return Nothing

-- | Given a type of the form @t1 -> t2@, return @t1@ and @t2@.
--
--   Returns a 'Right' value on success, 'Left' on failure.  The 'Left'
--   value is 't' after being reduced to WHNF.
deconFunType :: BoxingMode b => Type -> TypeEvalM b (Either Type (Type, Type))
{-# INLINE deconFunType #-}
deconFunType t = do
  t' <- reduceToWhnf t
  case t' of
    FunT d r -> return $ Right (d, r)
    _ -> return $ Left t'

-- | Given a type of the form @forall a. t@, return @a@ and @t@.
deconAllType :: BoxingMode b => Type -> TypeEvalM b (Either Type (Binder, Type))
{-# INLINE deconAllType #-}
deconAllType t = do
  t' <- reduceToWhnf t
  case t' of
    AllT b r -> return $ Right (b, r)
    _ -> return $ Left t'

-- | Given a type of the form @t1 -> ... -> tN@, get the domain and range
--   types.
deconFunctionType :: BoxingMode b => Type -> TypeEvalM b ([Type], Type)
deconFunctionType t = examine id t
  where 
    examine hd t = deconFunType t >>= continue
      where
        continue (Right (d, r)) = examine (hd . (d:)) r
        continue (Left t') = return (hd [], t')

-- | Given a type of the form @forall a ... z. t@, get the binders and range
--   type.
deconUniversalType :: BoxingMode b => Type -> TypeEvalM b ([Binder], Type)
deconUniversalType t = examine id t
  where 
    examine hd t = deconAllType t >>= continue
      where
        continue (Right (b, r)) = assumeBinder b $ examine (hd . (b:)) r
        continue (Left t') = return (hd [], t')

-- | Deconstruct a universally quantified function type.
deconForallFunType :: BoxingMode b =>
                      Type -> TypeEvalM b ([Binder], [Type], Type)
deconForallFunType t = do
  (binders, fntype) <- deconUniversalType t
  (domain, range) <- assumeBinders binders $ deconFunctionType fntype
  return (binders, domain, range)

-- | Create an unboxed tuple type constructor that can hold 
--   the given sequence of types.
unboxedTupleTyCon :: BoxingMode b => [Type] -> TypeEvalM b Type
unboxedTupleTyCon ts = UTupleT `liftM` mapM convert_type ts
  where
    convert_type t = do
      k <- typeKind t
      return $! case toBaseKind k
                of ValK -> ValK
                   BoxK -> BoxK
                   _ -> internalError "unboxedTupleTyCon: Invalid kind for tuple"

-- | Create the type of an unboxed tuple whose fields are the given types
unboxedTupleType :: BoxingMode b => [Type] -> TypeEvalM b Type
unboxedTupleType ts = do
  con <- unboxedTupleTyCon ts
  return $ typeApp con ts

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
  | length (dataConTyParams con_ty) /= length arg_vals =
      internalError "instantiateDataConType: Wrong number of type parameters"
  | length (dataConExTypes con_ty) /= length ex_vars =
      internalError "instantiateDataConType: Wrong number of existential variables"
  | otherwise = do
      let -- Assign parameters
          subst1 = instantiate_arguments $
                   zip (dataConTyParams con_ty) arg_vals

          -- Rename existential types, if new variables are given
          (subst2, ex_params) = instantiate_exvars subst1 $
                                zip (dataConExTypes con_ty) ex_vars

      -- Apply substitution to range type.  Use subst1 because existential
      -- variables cannot appear in the range.
      range <- substitute subst1 $ dataConPatternRange con_ty

      -- Apply the substitution to field and range types
      fields <- mapM (substitute subst2) $ dataConFieldTypes con_ty
      return (ex_params, fields, range)
  where
    -- Instantiate the type by substituing arguments for the constructor's
    -- type parameters
    instantiate_arguments :: [(Binder, Type)] -> TypeSubst
    instantiate_arguments assocs = 
      Substitute.fromList [(v, ty) | (v ::: _, ty) <- assocs]

    -- Instantiate existential types.  Rename each existential variable.
    instantiate_exvars :: TypeSubst -> [(Binder, Var)]
                       -> (TypeSubst, [Binder])
    instantiate_exvars subst ((old_ex_var ::: extype, ex_var) : params) =
      let subst' = Substitute.extend old_ex_var (VarT ex_var) subst
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
  pattern_vars <- replicateM (length $ dataConExTypes con_ty) $
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
  | length (dataConTyParams con_ty) +
    length (dataConExTypes con_ty) /= length arg_vals =
      internalError $ "instantiateDataConTypeWithExistentials: " ++
                      "Wrong number of type parameters"
  | otherwise = do
      let -- Assign parameters and existential types
          type_params =
            dataConTyParams con_ty ++ dataConExTypes con_ty
          subst = instantiate_arguments $ zip type_params arg_vals

      -- Apply the substitution to field and range types
      fields <- mapM (substitute subst) $ dataConFieldTypes con_ty
      range <- substitute subst $ dataConPatternRange con_ty
      return (fields, range)
  where
    -- Instantiate the type by substituing arguments for the constructor's
    -- type parameters
    instantiate_arguments :: [(Binder, Type)] -> TypeSubst
    instantiate_arguments assocs = 
      Substitute.fromList [(v, ty) | (v ::: _, ty) <- assocs]

