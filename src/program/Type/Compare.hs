
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
import Text.PrettyPrint.HughesPJ

import Common.Identifier
import Common.MonadLogic
import Common.SourcePos
import Common.Supply
import Type.Environment
import Type.Rename
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
    serach (IntT _) = False

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
    serach (IntT _) = False

-------------------------------------------------------------------------------

-- | Reduce a type to weak head-normal form.  Evaluate type functions
--   that are in head position.  The type is assumed to be well-kinded.
reduceToWhnf :: EvalMonad m => Type -> m Type
reduceToWhnf ty =
  case fromTypeApp ty
  of (op_type, args) | not (null args) ->
       case op_type
       of VarT op_var -> reduce_function_con op_var args
          LamT (v ::: dom) body -> reduce_lambda_fun v dom body args
     _ -> return ty
  where
    -- If the operator is a type function, then evaluate it
    reduce_function_con op_var args = do
      env <- getTypeEnv
      case lookupTypeFunction op_var env of
        Nothing    -> return ty
        Just tyfun -> applyTypeFunction tyfun args

    -- The operator is a lambda function; evaluate it
    reduce_lambda_fun v dom body (arg : other_args) = do
      -- Substitute 'arg' in place of 'v'
      body' <- substitute (singletonSubstitution v arg) body
            
      -- Continue to reduce
      reduceToWhnf $ typeApp body' other_args

-- | Compare two types.  Return True if the given type is equal to or a subtype
--   of the expected type, False otherwise.
--
--   The types being compared are assumed to have the same kind.  If they do
--   not, the result of comparison is undefined.
compareTypes :: EvalMonad m =>
                Type            -- ^ Expected type
             -> Type            -- ^ Given Type
             -> m Bool
compareTypes t1 t2 = do
  -- Ensure that the types are in weak head-normal form, then
  -- compare them structurally
  t1' <- reduceToWhnf t1
  t2' <- reduceToWhnf t2
  cmpType t1' t2'

-- | Structurally compare types.
--
--   Arguments are assumed to be in weak head-normal form and are assumed to
--   inhabit the same kind.
cmpType :: EvalMonad m => Type -> Type -> m Bool
cmpType expected given = debug $ cmp =<< unifyBoundVariables expected given
  where
    -- For debugging, print the types being compared
    debug x = x -- traceShow message x
      where 
        message = text "cmpType" <+>
                  (pprType expected $$ text "----" $$ pprType given)

    cmp (VarT v1, VarT v2) = return $ v1 == v2
    cmp (AppT op1 arg1, AppT op2 arg2) =
      compareTypes op1 op2 >&&> compareTypes arg1 arg2
    cmp (FunT dom1 rng1, FunT dom2 rng2) =
      compareTypes dom1 dom2 >&&> compareTypes rng1 rng2
    cmp (LamT (a1 ::: dom1) body1, LamT (a2 ::: dom2) body2) =
      compareTypes dom1 dom2 >&&> bindAndCompare a2 dom2 body1 body2
    cmp (AllT (a1 ::: dom1) rng1, AllT (a2 ::: dom2) rng2) =
      compareTypes dom1 dom2 >&&> bindAndCompare a2 dom2 rng1 rng2
    cmp (AnyT k1, AnyT k2) = return True -- Same-kinded 'Any' types are equal
    cmp (IntT n1, IntT n2) = return $ n1 == n2

    -- Matching (\x. e1) with e2
    -- is the same as matching (\x. e1) with (\x. e2 x)
    cmp (t1@(LamT (a ::: dom) _), t2) =
      cmp (t1, LamT (a ::: dom) (t2 `AppT` VarT a))

    cmp (t1, t2@(LamT (a ::: dom) _)) =
      cmp (LamT (a ::: dom) (t1 `AppT` VarT a), t2)

    cmp (_, _) = return False
    
    bindAndCompare x dom expected given =
      assume x dom $ cmpType expected given

-- | Given an expected type @t_e@, a set of flexible variables @fv$, and a
--   given type @t_g@, try to construct a unifying substitution
--   @S : fv -> Type@ such that @S(t_e) = t_g@.  The substitution applied to
--   the expected type makes it equal to the given type.
unifyTypeWithPattern :: IdentSupply Var
                     -> TypeEnv
                     -> [Var]   -- ^ Free variables in expected type
                     -> Type    -- ^ Expected type
                     -> Type    -- ^ Given type
                     -> IO (Maybe Substitution)
unifyTypeWithPattern id_supply _ free_vars expected given =
  runFreshVarM id_supply calculate_substitution
  where
    calculate_substitution = do
      result <- unify init_substitution expected given
      return $ case result
               of Just sub -> Just $ substitutionFromMap $ IntMap.mapMaybe id sub
                  Nothing -> Nothing

    init_substitution = IntMap.fromList [(fromIdent $ varID v, Nothing)
                                        | v <- free_vars]

-- | A substitution used in unification.  All flexible variables are in
--   the substitution.  If they haven't been assigned a value, their
--   value in the map is 'Nothing'.
type USubst = IntMap.IntMap (Maybe Type)

-- | Search for a substitution that unifies @expected@ with @given@.
--   Return a unifying substition if found.
unify :: USubst -> Type -> Type -> FreshVarM (Maybe USubst)
unify subst expected given = do
  -- Rename 'expected' so that bound variables match
  (given', expected') <- leftUnifyBoundVariables given expected
  match_unify expected' given'
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

    match_unify (IntT n1) (IntT n2)
      | n1 == n2 = unified_by subst
      | otherwise = no_unifier

    match_unify _ _ = no_unifier
