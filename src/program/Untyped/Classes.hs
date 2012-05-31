{- | Constraint manipulation is performed in this module.
-}

{-# LANGUAGE TypeFamilies #-}
module Untyped.Classes
       (pprPredicate, pprContext,
        isInstancePredicate, isEqualityPredicate,
        instantiateClassConstraint,
        andSuperclassEqualityPredicates,
        reduceTypeFunction,
        toHnf,
        dependentTypeVariables,
        reduceContext,
        splitConstraint,
        defaultConstraint,
        prove)
where

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import Data.List
import Data.Maybe
import Data.Function
import qualified Data.Set as Set
import Debug.Trace
import Text.PrettyPrint.HughesPJ 

import Common.Error
import Common.MonadLogic
import Common.SourcePos
import Common.Supply
import Untyped.Data
import Untyped.HMType
import Untyped.Kind
import Untyped.GenSystemF
import Untyped.Builtins
import qualified SystemF.Syntax as SystemF
import qualified Builtins.Builtins as SystemF
import Untyped.Unification
import Type.Level
import Type.Var
import Globals

-- | Flag turns on debugging dumps during context reduction
debugContextReduction = False

pprList :: [Doc] -> Doc
pprList xs = brackets $ sep $ punctuate (text ",") xs

pprPredicate :: Predicate -> Ppr Doc
pprPredicate = uShow

pprContext :: [Predicate] -> Ppr Doc
pprContext []  = return (parens Text.PrettyPrint.HughesPJ.empty)
pprContext [p] = pprPredicate p
pprContext ps  = do docs <- mapM pprPredicate ps
                    return $ parens $ fsep $ punctuate (text ",") docs

mapAndUnzip3M :: Monad m => (a -> m (b, c, d)) -> [a] -> m ([b], [c], [d])
mapAndUnzip3M f xs = liftM unzip3 $ mapM f xs

isInstancePredicate (IsInst _ _) = True
isInstancePredicate _ = False

isEqualityPredicate (IsEqual _ _) = True
isEqualityPredicate _ = False

-- | Somewhat of a hack.  Decide whether this is the distinguished type class
-- for object layout information. 
isPassableClass cls = clsName (clsSignature cls) == "Repr"

-- | Instantiate a class signature's constraint to a given type
instantiateClassConstraint :: ClassSig -> HMType -> IO Constraint
instantiateClassConstraint sig instance_type =
  let substitution = substitutionFromList [(clsParam sig, instance_type)]
  in renameList substitution (clsConstraint sig)

-------------------------------------------------------------------------------
-- Type function evalution

-- | Attempt to reduce a type function application.  If the arguments are 
--   sufficiently known, reduction will yield a new type.
reduceTypeFunction :: TyFamily  -- ^ Type function to evaluate
                   -> [HMType]  -- ^ Arguments to the type function
                   -> IO (Maybe HMType) -- ^ Reduced type (if reducible)
reduceTypeFunction family [arg] = runMaybeT $ do
  (result_type, inst_cst) <-
    msum $ map match_instance $ tfInstances family
  when (not $ null inst_cst) $
    internalError "reduceTypeFunction: Constraint handling is not implemented"
  return result_type
  where
    match_instance inst = do
      let sig = tinsSignature inst
      (subst, match_cst) <- MaybeT $ match (insType sig) arg
      cst <- lift $ mapM (rename subst) $ match_cst ++ insConstraint sig
      result_type <- lift $ rename subst $ tinsType inst
      return (result_type, cst)

-------------------------------------------------------------------------------
-- Context reduction

-- | Get all superclass predicates of a given class predicate
superclassPredicates :: Predicate -> IO [Predicate]
superclassPredicates (IsInst ty cls) = do
  -- Get the actual class constraint for this type
  constraint <- instantiateClassConstraint (clsSignature cls) ty

  -- Find all superclasses
  liftM concat $ mapM andSuperclassPredicates constraint

superclassPredicates _ = internalError "Not an instance predicate"

-- | Get a class and its superclass predicates
andSuperclassPredicates :: Predicate -> IO [Predicate]
andSuperclassPredicates p@(IsInst {}) = liftM (p:) $ superclassPredicates p
andSuperclassPredicates p@(IsEqual {}) = return [p]

-- | Get a class and its superclass equality predicates.
--   Superclass instance predicates are searched, but not included in the
--   result.
--
--   This function is used when instantiating type signatures in order to
--   find the equality constraints implied by the type signature's class
--   context.  Equality constraints implied by /instance/ contexts, on the
--   other hand, are only discovered while solving constraints.
andSuperclassEqualityPredicates :: Predicate -> IO [Predicate]
andSuperclassEqualityPredicates p@(IsInst {}) = do
  cst <- superclassPredicates p
  return $ p : filter isEqualityPredicate cst

andSuperclassEqualityPredicates p@(IsEqual {}) = return [p]

-- | Decide whether the constraint entails the predicate, which must be a class
--   instance predicate.
--   If the constraint entails the predicate, then eliminate the predicate and
--   return new, derived predicates.
--   Otherwise, return Nothing.
entailsInstancePredicate :: Constraint -> Predicate -> IO (Maybe Constraint)
ps `entailsInstancePredicate` p@(IsInst _ _) = do
  -- True if the predicate is in the context, including superclasses
  let inst_ps = filter isInstancePredicate ps
  b <- anyM p_implied_by inst_ps
  return $! if b then Just [] else Nothing
  where
    p_implied_by p' = do
      context <- andSuperclassPredicates p'
      anyM (p `uEqual`) context

_ `entailsInstancePredicate` _ =
  internalError "entailsInstancePredicate: Not an instance predicate"

-- | Decide whether the constraint entails the predicate, which must be a class
--   instance predicate.
--   If the constraint entails the predicate, then eliminate the predicate and
--   return new, derived predicates.
--   Otherwise, return Nothing.
{-entailsEqualityPredicate :: Constraint -> Predicate -> IO (Maybe Constraint)
ps `entailsEqualityPredicate` p@(IsEqual s1 t1) = do
  -- Check both the predicate and its mirrored equivalent
  b <- anyM (p `uEqual`) ps >||> anyM (IsEqual t1 s1 `uEqual`) ps
  return $! if b then Just [] else Nothing-}

-- | Determine whether a class instance predicate is in H98-style
--   head-normal form.
--
-- A predicate is in head-normal form if its head is a variable.
-- A predicate in head-normal form cannot be reduced.
--
-- A predicate that's not in head-normal form has a type constructor as
-- its head.  When instances are restricted to be H98-compatible, the
-- predicate can be reduced.  H98 limits all class instance heads to the
-- form (C a b ...) for some constructor C and variables a, b, ..., and
-- a non-HNF instance will always unify with such a term.
--
-- Pyon allows non-H98 instances, so if a predicate is not in HNF,
-- an attempt will be made to reduce it, but failure to reduce does not
-- necessarily indicate an error.
isH98Hnf :: Predicate -> IO Bool
isH98Hnf predicate = case predicate 
                     of IsInst t _    -> checkTypeHead t
                        IsEqual t1 t2 -> return False
  where
    checkTypeHead t = do
      t' <- canonicalizeHead t
      case t' of
        ConTy c     -> return $ isTyVar c
        FunTy _     -> return False
        TupleTy _   -> return False
        AppTy t'' _ -> checkTypeHead t''
        TFunAppTy _ [t''] -> checkTypeHead t''

isH98Hnf _ = internalError "isH98Hnf: Not an instance constraint"

-- | Convert a predicate to a conjunction of logically equivalent predicates
-- in head-normal form.  The list may contain duplicates.
-- A description of the conversion steps taken is also returned.
--
-- If the predicate cannot be converted to head-normal form, an error is
-- thrown.  It represents a type class error in the input program.
toHnf :: SourcePos -> Predicate -> IO (Derivation, Constraint)
toHnf pos pred = do
  -- If already in HNF, derivation is trivial
  is_hnf <- isH98Hnf pred
  if is_hnf then return (IdDerivation pred, [pred]) else
    case pred
    of IsInst {} ->
         -- Perform reduction based on the set of known class instances
         instanceReduction pos pred
       IsEqual {} -> do
         -- Perform reduction based on the set of known family instances
         cst <- equalitySimplification pos [pred]
         return (EqualityDerivation pred, cst)

-- | Convert a constraint to HNF and ignore how it was derived
toHnfConstraint :: Predicate -> IO Constraint
toHnfConstraint p = liftM snd $ toHnf noSourcePos p

-------------------------------------------------------------------------------
-- Reduction rules for predicates

-- | Context reduction for an IsInst predicate
instanceReduction :: SourcePos -> Predicate -> IO (Derivation, Constraint)
instanceReduction pos pred = do
    ip <- instancePredicates pred
    case ip of
      NotReduced -> do {-
        -- Can't derive a class dictionary for this type
        prdDoc <- runPpr $ uShow pred
        let msg = text (show pos) <> text ":" <+>
                  text "No instance for" <+> prdDoc
        fail (show msg) -}
        return (IdDerivation pred, [pred])

      InstanceReduced cls_cst inst inst_cst -> do
        -- Reduce all superclasses to HNF
        cls_hnf <- mapM (toHnf pos) cls_cst
        let cls_superclasses = map fst cls_hnf
            cls_hnf_cst = concatMap snd cls_hnf
        
        inst_hnf <- mapM (toHnf pos) inst_cst
        let inst_superclasses = map fst inst_hnf
            inst_hnf_cst = concatMap snd inst_hnf
        
        -- Return a new derivation
        let derivation = InstanceDerivation
                         { conclusion = pred 
                         , derivedInstance = inst
                         , classPremises = cls_superclasses
                         , instancePremises = inst_superclasses
                         }
        return (derivation, cls_hnf_cst ++ inst_hnf_cst)

      FunctionPassableReduced ty ->
        let derivation = FunPassConvDerivation { conclusion = pred }
        in return (derivation, [])

-------------------------------------------------------------------------------
-- Equality constraint solving

-- | Simplify a set of equality constraints as much as possible
equalitySimplification :: SourcePos -> Constraint -> IO Constraint
equalitySimplification pos csts =
  -- Simplify constraints repeatedly until no further simplification is
  -- possible
  repeat_until_convergence csts
  where
    repeat_until_convergence csts = do
      (csts', progress1) <-
        applyEqualityReductionRule equalityReductionRules pos csts
      (progress2, csts'') <- substituteConstraint csts'
      if progress1 || progress2
        then repeat_until_convergence csts''
        else return csts''

-- | Apply an equality reduction rule to all predicates in a constraint
applyEqualityReductionRule :: EqualityReductionRule
                           -> SourcePos
                           -> Constraint
                           -> IO (Constraint, Bool)
applyEqualityReductionRule rule pos cst = go False id cst
  where
    go progress new_cst (prd@(t1 `IsEqual` t2) : cst) = do
      prd_result <- runEqualityReductionRule rule pos t1 t2
      case prd_result of
        -- No change: go to next constraint
        Nothing        -> go progress (new_cst . (prd:)) cst

        -- Reduced: continue processing the reduced constraints
        Just (_, cst') -> go True new_cst (cst' ++ cst)

    go progress new_cst [] = return (new_cst [], progress)

newtype EqualityReductionRule =
  EqualityReductionRule 
  {runEqualityReductionRule :: SourcePos
                            -> HMType
                            -> HMType
                            -> IO (Maybe (Derivation, Constraint))}

equalityReductionRules =
  anyRule [decompRule, trivRule, unifyRule, funSwapRule]

-- | Try to run any rule in the list
anyRule :: [EqualityReductionRule] -> EqualityReductionRule
anyRule (r : rs) =
  EqualityReductionRule $ \ pos t1 t2 -> do
    result <- runEqualityReductionRule r pos t1 t2
    case result of
      Nothing -> runEqualityReductionRule (anyRule rs) pos t1 t2
      Just x  -> return result

anyRule [] = EqualityReductionRule $ \_ _ _ -> return Nothing

trivRule :: EqualityReductionRule
trivRule = EqualityReductionRule $ \pos t1 t2 -> do
  b <- uEqual t1 t2
  return $! if b
            then Just (EqualityDerivation (IsEqual t1 t2), [])
            else Nothing

-- | Reorient equations of the form @t ~ F t u v@, that is,
--   the RHS is a function application and the LHS appears somewhere under it.
--
--   (Other reorienting rules appear in 'decompRule').
funSwapRule :: EqualityReductionRule
funSwapRule = EqualityReductionRule $ \pos t1 t2 ->
  let swap =
        return $ Just (EqualityDerivation (IsEqual t1 t2), [t2 `IsEqual` t1])
  in do
    (t2_head, t2_args) <- inspectTypeApplication t2
    case t2_head of
      ConTy c | isTyFun c ->
        -- Does t1 appear anywhere under t2?
        ifM (anyM (subexpressionCheck t1) t2_args)
        swap
        (return Nothing)
      _ -> return Nothing

decompRule :: EqualityReductionRule
decompRule = EqualityReductionRule $ \pos t1 t2 ->
  let -- The equality predicate relates two matching data constructors:
      -- @C a b ~ C x y@.
      -- Decompose into fquality of arguments: @a ~ x, b ~ y@.
      decompose t1_args t2_args =
        let new_constraints = zipWith IsEqual t1_args t2_args
        in return (Just (EqualityDerivation (IsEqual t1 t2), new_constraints))

      -- Swap the LHS and RHS of the equality predicate so that it's usable as
      -- a left-to-right rewrite rule.
      swap =
        return (Just (EqualityDerivation (IsEqual t1 t2), [t2 `IsEqual` t1]))

      -- The predicate is unsolvable because it relates two different injective
      -- data constructors
      contradiction = do
        (t1_doc, t2_doc) <- runPpr $ liftM2 (,) (uShow t1) (uShow t2)
        print (t1_doc <+> text "=" <+> t2_doc)
        fail "Unsolvable type equality constraint detected"
  in do
    (t1_head, t1_args) <- inspectTypeApplication t1
    (t2_head, t2_args) <- inspectTypeApplication t2
    case (t1_head, t2_head) of
      _ | equalInjConstructors t1_head t2_head ->
        decompose t1_args t2_args

      (_, ConTy c)
        | isInjConstructor t1_head && (isTyVar c || isTyFun c) ->
        swap

      _ | isInjConstructor t1_head && isInjConstructor t2_head ->
        contradiction

      _ | otherwise ->
        return Nothing

unifyRule :: EqualityReductionRule
unifyRule = EqualityReductionRule $ \pos t1 t2 ->
  let success = return $ Just (EqualityDerivation (IsEqual t1 t2), [])

      -- Unify a variable with a type only if the variable does not occur in
      -- the type.  It's not an error for a variable to occur under a type
      -- function.
      unify_with_type v ty =
        -- If the variable does not occur in the type, then unify
        ifM (liftM not $ occursCheck v ty) (unifyTyVar v ty >> success) $

        -- If the variable occurs under injective type constructors, then error
        ifM (occursInjectively v ty)
          (fail "Occurs check failed in equality constraint") $

        return Nothing

  in do
    t1_c <- canonicalizeHead t1
    t2_c <- canonicalizeHead t2
    case (t1_c, t2_c) of
      (ConTy c1, ConTy c2) | isFlexibleTyVar c1 && isFlexibleTyVar c2 -> do
        unifyTyVars c1 c2
        success

      (ConTy c1, _) | isFlexibleTyVar c1 -> unify_with_type c1 t2_c
      (_, ConTy c2) | isFlexibleTyVar c2 -> unify_with_type c2 t1_c
      _ -> return Nothing

-- | Return 'True' if both arguments are equal injective constructors.
--   The arguments should be canonicalized.
--   Only injective constructors return 'True'.  Type variables, functions,
--   and applications always return 'False'.
equalInjConstructors (ConTy c1) (ConTy c2) =
  isDataCon c1 && isDataCon c2 && c1 == c2

equalInjConstructors (TupleTy n1) (TupleTy n2) = n1 == n2
equalInjConstructors (FunTy n1) (FunTy n2) = n1 == n2
equalInjConstructors (AnyTy k1) (AnyTy k2) = True
equalInjConstructors _ _ = False

-- | Return 'True' if the argument is an injective constructor and
--   not an application.
isInjConstructor (ConTy c) = isDataCon c
isInjConstructor (TupleTy _) = True
isInjConstructor (FunTy _) = True
isInjConstructor (AnyTy _) = True

-- | Perform substitution in the entire constraint.  Return True if any
--   substitution occurred.
substituteConstraint :: Constraint -> IO (Bool, Constraint)
substituteConstraint [] = return (False, [])

substituteConstraint (p:cst) = go False [] p cst
  where
    -- Process one predicate at a time
    go changed visited prd unvisited = do
      result <- substituteEqualityCoercion prd visited unvisited
      let (changed', visited', unvisited') =
            case result
            of Nothing     -> (changed, visited, unvisited)
               Just (v, u) -> (True, v, u)
      case unvisited' of
        []         -> return (changed', prd : visited')
        prd' : cst -> go changed' (prd : visited') prd' cst

-- | Given an equality coercion satisfying some criteria, exhaustively
--   apply the coercion as a rewrite rule to all other equality predicates
--   in the context.
--
--   If any substitutions were made, then return the substituted constraints.
substituteEqualityCoercion :: Predicate
                           -> Constraint
                           -> Constraint
                           -> IO (Maybe (Constraint, Constraint))
substituteEqualityCoercion (IsEqual lhs rhs) cst_l cst_r =

  -- Test whether the predicate should be applied as a rewrite rule
  -- Require that LHS is a type function application containing a type variable
  ifM (liftM not $ isTFAppOfFlexibleVar lhs) (return Nothing) $

  -- Require that LHS is not a subexpression of RHS
  ifM (subexpressionCheck lhs rhs) (return Nothing) $ do

    -- Apply the substitution to all other predicates
    (change1, cst_l') <- substitute_exhaustively_list cst_l
    (change2, cst_r') <- substitute_exhaustively_list cst_r
    return $! if change1 || change2 then Just (cst_l', cst_r') else Nothing

  where
    substitute_exhaustively_list (p:ps) = do
      (p_change, p') <- substitutePredicateExhaustively lhs rhs p
      (ps_change, ps') <- substitute_exhaustively_list ps
      return (p_change || ps_change, p' : ps')
    
    substitute_exhaustively_list [] = return (False, [])

-- Exhaustively perform substitution in a predicate.
-- Return 'True' if any substitutions have been made.
substitutePredicateExhaustively :: HMType
                                -> HMType
                                -> Predicate
                                -> IO (Bool, Predicate)
substitutePredicateExhaustively old new prd = go False prd
  where
    -- Use 'change_acc' to keep track of whether anything has changed
    go change_acc prd@(IsEqual t1 t2) = do
      (change1, t1') <- substituteType old new t1
      (change2, t2') <- substituteType old new t2

      -- If any substitutions were made this time, retry to find additional
      -- substitution opportunities
      if change1 || change2
        then go True (IsEqual t1' t2')
        else return (change_acc, prd)

    go change_acc prd@(IsInst t cls) = do
      (change, t') <- substituteType old new t

      -- If any substitutions were made this time, retry to find additional
      -- substitution opportunities
      if change
        then go True (IsInst t' cls)
        else return (change_acc, prd)

-------------------------------------------------------------------------------
-- Context reduction

-- | Perform context reduction.
--
-- A set of constraints is reduced to a constraint set that is in
-- head-normal form with no redundant constraints.
reduceContext :: Constraint -> IO Constraint
reduceContext csts = do 
  when debugContextReduction $ do
    old_context <- runPpr (pprContext csts)
    print $ text "Start context reduction:" <+> old_context

  -- Add superclass equality predicates to the constraint before solving
  superclass_csts <- mapM andSuperclassEqualityPredicates csts
  let expanded_csts = concat superclass_csts

  let (equalities, others) = partition isEqualityPredicate expanded_csts
  csts' <- fixed_point_reduce equalities others

  when debugContextReduction $ do
    old_context <- runPpr (pprContext expanded_csts)
    new_context <- runPpr (pprContext csts')
    print $ hang (text "End context reduction:" <+> old_context) 4 new_context

  return csts'
  where
    fixed_point_reduce equalities others = do
      equalities' <- equalitySimplification noSourcePos equalities
      others' <- foldM addToContext [] others

      -- If class reduction introduced new equality predicates, then repeat
      if any isEqualityPredicate others'
        then let (new_equalities, others'') =
                   partition isEqualityPredicate others'
             in fixed_point_reduce (new_equalities ++ equalities') others''
        else return (equalities' ++ others')

  -- Simplify equality constraints and other constraints using separate
  -- procedures

-- | Add the extra information from a predicate to the context.  The 
-- context must be in head-normal form.
addToContext :: Constraint -> Predicate -> IO Constraint
addToContext ctx pred = foldM addToContextHNF ctx =<< toHnfConstraint pred

-- | Add the extra information from a predicate to the context.  The 
-- context and predicate must be in head-normal form.
addToContextHNF :: Constraint -> Predicate -> IO Constraint
addToContextHNF ctx pred = do
  -- If it's a class predicate,
  -- then reduce it WRT the rest of the class context
  new_cst <- case pred
             of IsInst {} -> entailsInstancePredicate ctx pred
                IsEqual {} -> return Nothing -- entailsEqualityPredicate ctx pred
  case new_cst of
    Nothing -> do
      -- Not a redundant predicate
      debug_show_constraint [pred]
      return (pred : ctx)
    Just new_ctx -> do
      -- Predicate is redundant wrt context
      debug_show_constraint new_ctx
      return (new_ctx ++ ctx)
  where
    -- Print how context was changed 
    debug_show_constraint new_ctx
      | debugContextReduction = do
          (pred_doc, new_ctx_doc) <-
            runPpr $ liftM2 (,) (uShow pred) (pprContext new_ctx)
          print $ hang (text "addToContext" <+> pred_doc) 4 new_ctx_doc
      | otherwise = return ()

data InstanceReductionStep =
    NotReduced
  | InstanceReduced Constraint Instance Constraint
    -- | Reduction of an equality constraint to simpler constraints
  | EqualityReduced Constraint
  | FunctionPassableReduced HMType

-- | Try to satisfy a predicate with one of the known class instances.
-- If a match is found, return a list of subgoals generated for the class,
-- the matching instance, and a list of subgoals generated for the instance.
--
-- If a type family constraint is matched, some unification is performed.
instancePredicates :: Predicate -> IO InstanceReductionStep
instancePredicates (IsInst t cls) = do
  (head, _) <- uncurryTypeApplication t
  case head of
    ConTy con | isTyVar con -> 
      -- If the head is a type variable, we won't find any instances
      return NotReduced

    FunTy _ ->
      -- Function instances are handled specially
      if isPassableClass cls
      then return $ FunctionPassableReduced t
      else return NotReduced

    _ -> fmap to_reduction_step $ runMaybeT $ do
      -- Match against all instances until one succeeds
      (inst_subst, inst, inst_cst) <-
        msum $ map (matchInstancePredicate t) $ clsInstances cls

      -- Get the class constraints.  Substitute the actual instance type
      -- for the class variable.
      let class_subst = substitutionFromList [(clsParam $ clsSignature cls, t)]

      -- If an instance matched, then the class must match also
      cls_csts <-
        lift $ mapM (instantiatePredicate class_subst t) $
        clsConstraint $ clsSignature cls

      return (cls_csts, inst, inst_cst)
  where
    to_reduction_step Nothing = NotReduced
    to_reduction_step (Just (x, y, z)) = InstanceReduced x y z

    -- Instantiate a superclass predicate.  Substitute the instance type  
    -- for the class parameter.
    instantiatePredicate class_subst inst_type pred =
      rename class_subst pred

instancePredicates _ = internalError "Not an instance predicate"

-- | Attempt to match a type against a class instance
matchInstancePredicate :: HMType -> Instance
                       -> MaybeT IO (Substitution, Instance, Constraint)
matchInstancePredicate inst_type inst = do
  (subst, inst_cst) <- matchInstanceSignature inst_type (insSignature inst)
  return (subst, inst, inst_cst)

matchInstanceSignature :: HMType -> InstanceSig
                       -> MaybeT IO (Substitution, Constraint)
matchInstanceSignature inst_type sig = do
  -- Try to match this type against the instance's type
  (subst, match_cst) <- MaybeT $ match (insType sig) inst_type
  
  -- If successful, return the substituted constraints from the instance
  inst_cst <- lift $ mapM (rename subst) $ match_cst ++ insConstraint sig
  return (subst, inst_cst)

-------------------------------------------------------------------------------
-- Generalization-related functions

-- | Find variables that are dependent on a given set of variables subject to
--   a constraint.  The constraint parameter should be reduced constraint
--   returned by 'reduceContext'.
--
--   Dependent variables are those that will be resolved to ground types if
--   types are assigned to all free type variables of the first-order type. 
--
--   All free variables of the first-order type are dependent.  Additionally,
--   variables that are determined by a type equality constraint are
--   dependent.
dependentTypeVariables :: Constraint -> TyVarSet -> IO TyVarSet
dependentTypeVariables cst initial_set = do
  -- For each equality constraint, find the free variables of its LHS and RHS
  equality_freevars <-
    sequence [do fv1 <- freeTypeVariables t1
                 fv2 <- freeTypeVariables t2
                 return (fv1, fv2)
             | IsEqual t1 t2 <- cst]

  let extend_set s =
        -- Look at each equality constraint and add dependent variables
        let s' = foldl' extend_with_constraint s equality_freevars

        -- If new variables were added, new equality constraints may become
        -- relevant.  Repeat until convergence.
        in if s' == s then s' else extend_set s'

  return $ extend_set initial_set
  where
    -- Attempt to add type variables from the equality (t1 ~ t2) to the set.
    -- If all variables on one side of the equality are dependent, then add
    -- all variables on the other side.
    extend_with_constraint s (fv1, fv2)
      | fv1_subset && not fv2_subset = Set.union s fv2
      | fv2_subset && not fv1_subset = Set.union s fv1
      | otherwise                    = s
      where
        fv1_subset = fv1 `Set.isSubsetOf` s
        fv2_subset = fv2 `Set.isSubsetOf` s

-- | An action taken by splitConstraint
data SplitAction = Retain | Defer | Default | Ambiguous

-- | Partition a set of constraints into a retained set and a deferred set.
-- A constraint is retained if it mentions any variable in the given set of
-- \"bound\" variables.
--
-- TODO: Apply defaulting rules when the constraint is ambiguous
splitConstraint :: Constraint   -- ^ Constraint to partition. 
                                --   Must have been simplified
                                --   by 'reduceContext'.
                -> TyVarSet     -- ^ Free variables
                -> TyVarSet     -- ^ Bound variables
                -> IO (Constraint, Constraint)
                   -- ^ Returns (retained constraints,
                   -- deferred constraints)
splitConstraint cst fvars qvars = do
  (retained, deferred, defaulted, ambiguous) <- partitionM isRetained cst
  
  -- Need to default some constraints?
  if null defaulted
    then if null ambiguous 
         then return (retained, deferred)
         else do cst_doc <- runPpr $ pprContext ambiguous
                 fail ("Ambiguous constraint:\n" ++ show cst_doc)
    else do
    -- Apply defaulting rules, then retry
    new_csts <- mapM defaultConstraint defaulted
    cst' <- reduceContext (concat new_csts ++ cst)
    splitConstraint cst' fvars qvars
  where
    isRetained prd = do
      fv <- freeTypeVariables prd
      
      -- If only variables from the environment are mentioned, then
      -- defer this predicate.  If only variables from the environment and
      -- local context are mentioned, then retain this predicate.
      -- Otherwise the predicate is ambiguous; try to resolve it by
      -- defaulting.
      case () of
        _ | Set.null fv -> do
              -- A predicate with no free variables should have been
              -- either resolved or reported as unsatisfiable
              doc <- runPpr $ uShow prd
              internalError $
                "splitConstraint: Found unresolved\
                \ predicate with no free variables:\n" ++ show doc
          | fv `Set.isSubsetOf` fvars -> return Defer
          | fv `Set.isSubsetOf` Set.union fvars qvars -> return Retain
          | isDefaultable prd -> return Default
          | otherwise -> return Ambiguous
    
    -- Check if the dependent variable can be fixed using defaulting rules
    isDefaultable (IsInst head cls) =
      cls == tiBuiltin the_c_Traversable
    
    isDefaultable (IsEqual _ _) = False

    partitionM f xs = go xs [] [] [] []
      where
        go (x:xs) lefts rights defaults ambigs = do
          b <- f x
          case b of
            Retain    -> go xs (x:lefts) rights defaults ambigs
            Defer     -> go xs lefts (x:rights) defaults ambigs
            Default   -> go xs lefts rights (x:defaults) ambigs
            Ambiguous -> go xs lefts rights defaults (x:ambigs)

        go [] lefts rights defaults ambigs =
          return (reverse lefts, reverse rights, reverse defaults,
                  reverse ambigs)

-- | Perform defaulting on a constraint, unifying the variable mentioned in
-- the type head with some predetermined type.  The constraint must have been
-- selected for defaulting by 'splitConstraint'.  Defaulting first checks if
-- the given type was already unified (by an earlier defaulting step) and skips
-- if that is the case.
--    
-- Defaulting rules are as follows:
--
-- * @Traversable@ defaults to @list@
defaultConstraint cst =
  case cst
  of IsInst head cls
       | cls == tiBuiltin the_c_Traversable -> do
           can_head <- canonicalizeHead head
           case can_head of
             ConTy c
               | isFlexibleTyVar c ->
                 unify noSourcePos (ConTy c) (ConTy $ tiBuiltin the_con_list)
               | isTyVar c -> internalError "defaultConstraint: Unexpected rigid variable"
             _ -> return []
     _ -> internalError "Cannot default constraint"
       

-------------------------------------------------------------------------------
-- Proof derivation

-- | Prove a constraint and generate its proof derivation.
--
-- If the proof cannot be fully derived, placeholders will be returned for
-- the un-derived part.  The boolean value is true if
-- any progress was made toward a proof.
prove :: SourcePos
      -> ProofEnvironment -> Predicate -> IO (Bool, Placeholders, TIExp)
prove pos env prd = do
  -- Simplify the predicate to HNF
  (deriv, _) <- toHnf pos prd
  
  -- Generate code for this derivation
  toProof pos env deriv

-- | Generate code corresponding to a proof derivation
--
-- The return value includes a partial or complete proof derivation and 
-- placeholders for incomplete proofs.  The boolean value is true if
-- any progress was made toward a proof.
toProof :: SourcePos
        -> ProofEnvironment -> Derivation -> IO (Bool, Placeholders, TIExp)
toProof pos env derivation = 
  case derivation
  of IdDerivation {conclusion = prd} ->
       -- Get it from the environment
       lookupProof prd env >>= returnIdProof prd

     InstanceDerivation { conclusion = prd@(IsInst inst_type cls)
                        , derivedInstance = inst
                        , instancePremises = i_premises
                        , classPremises = c_premises
                        } -> do
       -- Prove class and instance premises
       (proof, placeholders) <-
         toLocalProofs c_premises env $ \c_env c_vars ->
         toLocalProofs i_premises c_env $ \i_env i_vars -> do
           dict <-
             createClassInstance pos cls inst inst_type c_vars i_env i_vars
           return (dict, [])

       return (True, placeholders, proof)

     FunPassConvDerivation { conclusion = prd@(IsInst ty _)
                           } -> do
       let con = SystemF.coreBuiltin SystemF.The_repr_Box
           prf = mkPolyCallE pos (mkVarE pos con) [convertHMType ty] []
       return (True, [], prf)
     
     EqualityDerivation { conclusion = prd@(IsEqual t1 t2) } -> do
       -- No evidence is needed.  Create a coercion value
       prf <- createCoercionValue pos t1 t2
       return (True, [], prf)
       
     MagicDerivation {} -> do
       -- Create a magic proof value
       return (True, [], mkPolyCallE pos (mkVarE noSourcePos $ SystemF.coreBuiltin SystemF.The_fun_undefined) [convertPredicate $ conclusion derivation] [])
  where
    returnIdProof prd (Just e) = return (True, [], e)
    returnIdProof prd Nothing  = do ph <- mkDictPlaceholder pos prd
                                    return (False, [ph], ph)

    -- Convert derivations to proofs, bind them to local variables, and
    -- update the environment
    toLocalProofs :: [Derivation]
                  -> ProofEnvironment
                  -> (ProofEnvironment -> [Var] -> IO (TIExp, Placeholders))
                  -> IO (TIExp, Placeholders)
    toLocalProofs derivations env k = do
      (placeholders, proofs) <- toProofs pos env derivations
      (exp, local_placeholders) <-
        addManyToProofEnv pos (zip derivations proofs) env k
      return (exp, local_placeholders ++ placeholders)

-- | Convert a list of independent derivations to proof expressions
toProofs :: SourcePos
         -> ProofEnvironment -> [Derivation] -> IO (Placeholders, [TIExp])
toProofs pos env derivations = do
  xs <- mapM (toProof pos env) derivations
  let (_, phs, values) = unzip3 xs
  return (concat phs, values)

-- | Create a local variable to stand for a proof of a derivation.  Add it to 
-- the proof environment.  Create a let-expression that binds the proof to the 
-- variable.
addToProofEnv :: SourcePos
              -> Derivation
              -> TIExp
              -> ProofEnvironment
              -> (ProofEnvironment -> Var -> IO (TIExp, a))
              -> IO (TIExp, a)
addToProofEnv pos derivation proof env k =
  withLocalAssignment pos proof (convertPredicate $ conclusion derivation) $ \v ->
    let variable = mkVarE noSourcePos v
        env' = (conclusion derivation, variable) : env
    in k env' v

addManyToProofEnv :: SourcePos
                  -> [(Derivation, TIExp)]
                  -> ProofEnvironment 
                  -> (ProofEnvironment -> [Var] -> IO (TIExp, a))
                  -> IO (TIExp, a)
addManyToProofEnv pos ((derivation, proof) : bindings) env k =
  addToProofEnv pos derivation proof env $ \env' v ->
  addManyToProofEnv pos bindings env' $ \env'' vs -> k env'' (v:vs)

addManyToProofEnv _ [] env k = k env []

-- | Assign an expression to a new local variable over the scope of
-- another expression.  A let-expression is constructed to bind the variable.
withLocalAssignment :: SourcePos -> TIExp -> TIType -> (Var -> IO (TIExp, a)) 
                    -> IO (TIExp, a)
withLocalAssignment pos rhs ty make_body = do
  -- Create new variable
  id <- withTheNewVarIdentSupply supplyValue
  let v = mkAnonymousVar id ObjectLevel
  
  -- Create body
  (body, x) <- make_body v
  
  -- Create let expression
  return (mkLetE pos (TIVarP v ty) rhs body, x)

withLocalAssignments :: SourcePos
                     -> [(TIExp, TIType)] 
                     -> ([Var] -> IO (TIExp, a)) 
                     -> IO (TIExp, a)
withLocalAssignments pos = withMany (uncurry (withLocalAssignment pos))

createClassInstance pos cls inst inst_type c_vars i_env i_vars = 
  case insCon inst
  of Nothing -> do
       -- Create instance methods
       inst_methods <- instantiateClassMethods pos inst inst_type i_env

       -- Create dictionary expression
       return $ mkDictE pos cls hmtype superclasses inst_methods
     Just con -> do
       -- Get premise types
       (_, premise_types) <- uncurryTypeApplication inst_type
       
       -- Apply the constructor to premise types and premises
       let premise_ts = map convertHMType premise_types
           premise_vs = map (mkVarE pos) i_vars
       return $ mkPolyCallE pos (mkVarE pos con) premise_ts premise_vs
  where
    hmtype = convertHMType inst_type
    superclasses = map (mkVarE pos) c_vars

-- | Create class method expressions for the given class instance, 
-- instantiated at the given type.  This is used in constructing a class
-- dictionary.
instantiateClassMethods :: SourcePos
                        -> Instance
                        -> HMType 
                        -> ProofEnvironment 
                        -> IO [TIExp]
instantiateClassMethods pos inst inst_type env = do
  -- Get the type and dictionary parameters to use for constructing
  -- instance methods
  (ty_params, constraint) <- instantiateAs pos (insScheme inst) inst_type

  -- Create instance methods
  forM (insMethods inst) $ \method ->
    let method_exp = mkVarE pos (inmName method)
    in instanceExpressionWithProofs env pos ty_params constraint method_exp

-- | Create a System F value representing a coercion from t1 to t2.
createCoercionValue :: SourcePos -> HMType -> HMType -> IO TIExp
createCoercionValue pos t1 t2 = do
  let t1' = convertHMType t1
      t2' = convertHMType t2
  let op = VarTE (SystemF.mkExpInfo pos)
           (SystemF.coreBuiltin SystemF.The_unsafeMakeCoercion)
  return $ mkPolyCallE pos op [t1', t2'] []

