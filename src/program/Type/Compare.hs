
{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleInstances #-}
module Type.Compare
       (typeMentions,
        typeMentionsAny,
        reduceToWhnf,
        compareTypes,
        unifyTypeWithPattern
       )
where

import Control.Monad.Reader
import qualified Data.Set as Set
import qualified Data.IntMap as IntMap
import Debug.Trace
import GHC.Exts(inline)
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import Common.MonadLogic
import Common.SourcePos
import Common.Supply
import Type.Environment
import qualified Type.Rename as Rename
import Type.Rename(Renaming, Renameable(..))
import Type.Substitute(TypeSubst, Substitutable(..), substitute)
import qualified Type.Substitute as Substitute
import Type.Type

-- | Determine whether the type mentions a variable.
typeMentions :: Type -> Var -> Bool
typeMentions t target = search t
  where
    search (VarT v) = v == target
    search (AppT op arg) = search op || search arg
    search (LamT (x ::: dom) body) 
      | x == target = search dom     -- Shadowed by local binding
      | otherwise = search dom || search body
    search (FunT dom rng) = search dom || search rng
    search (AllT (x ::: dom) rng) 
      | x == target = search dom
      | otherwise = search dom || search rng
    search (AnyT k) = search k
    search (IntT _) = False
    search (CoT _) = False
    search (UTupleT _) = False

-- | Determine whether the type mentions a variable in the set.
--   It's assumed that name shadowing does /not/ occur.  If a variable is
--   defined somewhere inside the type and then used, that counts as a mention.
--   
typeMentionsAny :: Type -> Set.Set Var -> Bool
typeMentionsAny t target = search t
  where
    search (VarT v) = v `Set.member` target
    search (AppT op arg) = search op || search arg
    search (LamT (x ::: dom) body)
      | x `Set.member` target = search dom
      | otherwise = search dom || search body
    search (FunT dom rng) = search dom || search rng
    search (AllT (x ::: dom) rng)
      | x `Set.member` target = search dom
      | otherwise = search dom || search rng
    search (AnyT k) = search k
    search (IntT _) = False
    search (CoT _) = False
    search (UTupleT _) = False

-------------------------------------------------------------------------------

-- | Reduce a type to weak head-normal form.  Evaluate type functions
--   that are in head position.  The type is assumed to be well-kinded.
reduceToWhnf :: EvalMonad m => Type -> m Type
{-# INLINE reduceToWhnf #-}
reduceToWhnf ty = liftTypeEvalM $ reduceToWhnf' ty

-- | The main work of 'reduceToWhnf' is in this function.  It's less 
--   polymorphic for greater efficiency.
reduceToWhnf' :: BoxingMode b => Type -> TypeEvalM b Type
{-# SPECIALIZE reduceToWhnf' :: Type -> TypeEvalM FullyBoxedMode Type #-}
{-# SPECIALIZE reduceToWhnf' :: Type -> TypeEvalM UnboxedMode Type #-}
reduceToWhnf' ty =
  case fromTypeApp ty
  of (op_type, args) | not (null args) ->
       case op_type
       of VarT op_var -> reduce_function_con op_var args
          LamT (v ::: dom) body -> reduce_lambda_fun v dom body args
          UTupleT _ -> return ty
          CoT _ -> return ty
     _ -> return ty
  where
    -- If the operator is a type function, then evaluate it
    reduce_function_con op_var args = do
      env <- getTypeEnv
      case lookupTypeFunction op_var env of
        Nothing    -> return ty
        Just tyfun -> do b <- getBoxingMode
                         let tf = builtinTypeFunctionForEval b tyfun
                         applyTypeFunction tf args

    -- The operator is a lambda function; evaluate it
    reduce_lambda_fun v dom body (arg : other_args) = do
      -- Substitute 'arg' in place of 'v'
      body' <- substitute (Substitute.singleton v arg) body
            
      -- Continue to reduce
      reduceToWhnf' $ typeApp body' other_args

-- | Compare two types.  Return True if the given type is equal to or a subtype
--   of the expected type, False otherwise.
--
--   The types being compared are assumed to have the same kind.  If they do
--   not, the result of comparison is undefined.
compareTypes :: EvalMonad m =>
                Type            -- ^ Expected type
             -> Type            -- ^ Given Type
             -> m Bool
{-# INLINE compareTypes #-}
compareTypes t1 t2 = liftTypeEvalM $ compareTypes' t1 t2

-- | The main work of 'compareTypes' is in this function.
compareTypes' :: BoxingMode m => Type -> Type -> TypeEvalM m Bool
{-# SPECIALIZE compareTypes' :: Type -> Type -> TypeEvalM UnboxedMode Bool #-}
{-# SPECIALIZE compareTypes' :: Type -> Type -> TypeEvalM FullyBoxedMode Bool #-}
compareTypes' t1 t2 = do
  -- Ensure that the types are in weak head-normal form, then
  -- compare them structurally
  t1' <- reduceToWhnf' t1
  t2' <- reduceToWhnf' t2
  cmpType t1' t2'

-- | Structurally compare types.
--
--   Arguments are assumed to be in weak head-normal form and are assumed to
--   inhabit the same kind.

--   This function is very heavily used.
--   The call to 'unifyBoundVariables' is explicitly inlined to make 
--   optimization easier.
cmpType :: BoxingMode m => Type -> Type -> TypeEvalM m Bool
cmpType expected given =
  debug $ cmp =<< inline Substitute.unifyBoundVariables expected given
  where
    -- For debugging, print the types being compared
    debug x = x -- traceShow message x
      where 
        message = text "cmpType" <+>
                  (pprType expected $$ text "----" $$ pprType given)

    cmp (VarT v1, VarT v2) = return $! v1 == v2
    cmp (AppT op1 arg1, AppT op2 arg2) =
      compareTypes' op1 op2 >&&> compareTypes' arg1 arg2
    cmp (FunT dom1 rng1, FunT dom2 rng2) =
      compareTypes' dom1 dom2 >&&> compareTypes' rng1 rng2
    cmp (LamT (a1 ::: dom1) body1, LamT (a2 ::: dom2) body2) =
      compareTypes' dom1 dom2 >&&> bindAndCompare a2 dom2 body1 body2
    cmp (AllT (a1 ::: dom1) rng1, AllT (a2 ::: dom2) rng2) =
      compareTypes' dom1 dom2 >&&> bindAndCompare a2 dom2 rng1 rng2
    cmp (AnyT k1, AnyT k2) = return True -- Same-kinded 'Any' types are equal
    cmp (IntT n1, IntT n2) = return $! n1 == n2
    cmp (CoT k1, CoT k2) = compareTypes' k1 k2
    cmp (UTupleT a, UTupleT b) = return $! a == b

    -- Matching (\x. e1) with e2
    -- is the same as matching (\x. e1) with (\x. e2 x)
    cmp (t1@(LamT (a ::: dom) _), t2) =
      cmp (t1, LamT (a ::: dom) (t2 `AppT` VarT a))

    cmp (t1, t2@(LamT (a ::: dom) _)) =
      cmp (LamT (a ::: dom) (t1 `AppT` VarT a), t2)

    cmp (_, _) = return False
    
    bindAndCompare x dom expected given =
      assume x dom $ compareTypes' expected given

-- | Given an expected type @t_e@, a set of flexible variables @fv$, and a
--   given type @t_g@, try to construct a unifying substitution
--   @S : fv -> Type@ such that @S(t_e) = t_g@.  The substitution applied to
--   the expected type makes it equal to the given type.
unifyTypeWithPattern :: EvalMonad m =>
                        [Var]   -- ^ Free variables in expected type
                     -> Type    -- ^ Expected type
                     -> Type    -- ^ Given type
                     -> m (Maybe TypeSubst)
unifyTypeWithPattern free_vars expected given =
  liftTypeEvalM calculate_substitution
  where
    calculate_substitution = do
      result <- unify init_substitution expected given
      return $ case result
               of Just sub -> Just $ Substitute.fromMap $ IntMap.mapMaybe id sub
                  Nothing -> Nothing

    init_substitution = IntMap.fromList [(fromIdent $ varID v, Nothing)
                                        | v <- free_vars]

-- | A substitution used in unification.  All flexible variables are in
--   the substitution.  If they haven't been assigned a value, their
--   value in the map is 'Nothing'.
type USubst = IntMap.IntMap (Maybe Type)

-- | Search for a substitution that unifies @expected@ with @given@.
--   Return a unifying substition if found.
--
--   This is in the type evaluation monad because types may be reduced during
--   unification.
unify :: BoxingMode b => USubst -> Type -> Type -> TypeEvalM b (Maybe USubst)
unify subst expected given = do
  -- Evaluate both types to WHNF
  expected1 <- reduceToWhnf expected
  given1 <- reduceToWhnf given

  -- Rename 'expected' so that bound variables match
  (given2, expected2) <- Substitute.leftUnifyBoundVariables given1 expected1
  match_unify expected2 given2
  where
    no_unifier   = return Nothing
    unified_by s = return (Just s)

    -- Run two unification tasks sequentially
    unify2 s (e1, e2) (g1, g2) = do
      result1 <- unify s e1 g1
      case result1 of
        Just s' -> unify s' e2 g2
        Nothing -> no_unifier

    match_unify (VarT v) given =
      case IntMap.lookup (fromIdent $ varID v) subst
      of Just (Just v_value) ->
           -- v has been assigned a value; substitute it
           unify subst v_value given
         Just Nothing -> 
           -- v is flexible; assign it and succeed
           unified_by $ IntMap.insert (fromIdent $ varID v) (Just given) subst
         Nothing ->
           -- v is rigid; must be equal to 'given'
           case given
           of VarT v' | v == v' -> unified_by subst
              _ -> no_unifier

    match_unify (AppT t1 t2) (AppT t3 t4) =
      unify2 subst (t1, t2) (t3, t4)

    match_unify (FunT dom1 rng1) (FunT dom2 rng2) =
      unify2 subst (dom1, rng1) (dom2, rng2)

    match_unify (AnyT _) (AnyT _) =
      -- Assume the types have the same kind.  That means they're equal.
      unified_by subst

    match_unify (CoT _) (CoT _) =
      -- Assume the types have the same kind.  That means they're equal.
      unified_by subst

    match_unify (IntT n1) (IntT n2)
      | n1 == n2 = unified_by subst
      | otherwise = no_unifier

    match_unify (UTupleT x) (UTupleT y)
      | x == y = unified_by subst
      | otherwise = no_unifier

    match_unify (LamT (a ::: k) e_range) (LamT _ g_range) = do
      -- Assume the types have the same kind; k1 and k2 are equal
      -- Bound variables have been unified, so go ahead and compare the
      -- function ranges.  The bound variable is rigid.
      unify_lambdas a k e_range g_range

    match_unify (LamT (a ::: k1) e_range) given = do
      -- Eta-expand given; rename expected
      b <- newAnonymousVar TypeLevel
      let e_range' = rename (Rename.singleton a b) e_range
      unify_lambdas b k1 e_range' (given `AppT` VarT b)
      
    match_unify expected (LamT (a ::: k1) g_range) = do
      -- Eta-expand expected; rename given
      b <- newAnonymousVar TypeLevel
      let g_range' = rename (Rename.singleton a b) g_range
      unify_lambdas b k1 (expected `AppT` VarT b) g_range'
      
    match_unify (AllT {}) _ = not_implemented
    match_unify _ (AllT {}) = not_implemented

    match_unify _ _ = no_unifier

    unify_lambdas a k e_range g_range = 
      assume a k $ unify subst e_range g_range

    not_implemented = internalError "unify: Not implemented for this type"