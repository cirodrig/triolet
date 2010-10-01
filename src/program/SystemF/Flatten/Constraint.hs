{-| Effect constraints.

Effect constraints declare sub-effect relationships of the form
@v <: e@ for some region or effect
variable @v@ and effect @e@, where @e@ is a union of region and effect
variables.  Predicates with a more complicated expression @e1 U e2 <: e@
are first decomposed into multiple predicates.

-}

{-# LANGUAGE Rank2Types, FlexibleInstances, FlexibleContexts,
    GeneralizedNewtypeDeriving #-}
module SystemF.Flatten.Constraint
       (-- * Predicates
        Predicate,
        pprPredicate,
        subEffect,
        predicateMentions,
        
        -- * Constraints
        Constraint,
        pprConstraint,
        constraintMentions,
        evalConstraint,
        simplifyConstraint,
        mkEqualityConstraint,
        
        -- ** Constraint solving
        solveGlobalConstraint,
        eliminateRigidVariable,
        eliminatePredicate,
        makeFlexibleVariablesIndependentWithConstraint,
        clearFlexibleEffectVariables
       )
where

import Control.Monad
import Control.Monad.Trans
import qualified Data.Set as Set
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.MonadLogic
import Gluon.Common.Supply
import Gluon.Core(Var)
import Gluon.Eval.Environment
import SystemF.Flatten.Effect

-- | Set this to True to print messages related to constraint solving
debugConstraints :: Bool
debugConstraints = False

data Predicate =
  -- | @a `SubEffect` b@ => Effect @a@ is smaller than effect @b@.
  SubEffect EffectVar Effect

type Constraint = [Predicate]

-- | Create a subeffect constraint.
subEffect :: Effect -> Effect -> Constraint
subEffect e1 e2 = [SubEffect ev e2 | ev <- fromEffect e1]

-- | Determine whether a predicate mentions an effect variable.  The
-- predicate should be in head normal form.
predicateMentions :: Predicate -> EffectVar -> Bool
SubEffect lhs rhs `predicateMentions` v = lhs == v || rhs `effectMentions` v

-- | Determine whether a constraint mentions an effect variable.  The
-- constraint should be in head normal form.
constraintMentions :: Constraint -> EffectVar -> Bool
cst `constraintMentions` v = any (`predicateMentions` v) cst

-- | Expand variables that have been unified in a predicate.
evalPredicate :: Predicate -> IO Constraint
evalPredicate (SubEffect e1 e2) =
  liftM2 subEffect (evalEffectVar e1) (evalEffect e2)

-- | Expand variables that have been unified in a predicate.
evalConstraint :: Constraint -> IO Constraint
evalConstraint cst = liftM concat $ mapM evalPredicate cst

-------------------------------------------------------------------------------
-- Constraint simplification
    
-- | Decompose a flexible effect variable into two parts, one part being a
-- known variable and the other being a fresh variable.  The known variable
-- must be a subset of the effect variable.
splitVariableOnSubset :: EffectVar -- ^ Subset to separate out
                      -> EVar      -- ^ Flexible variable to split
                      -> RegionM EffectVar
splitVariableOnSubset subset_var v = trace "splitVariableOnSubset" $ assertEVar v $ do
  whenM (isRigid v) $ fail "splitVariableOnSubset: Variable is rigid"
    
  -- Create a new variable
  v' <- newEffectVar

  -- State the relationship between the new and old variables
  liftIO $ assignEffectVarD "splitVariable" v $ varsEffect [v', subset_var]
      
  return v'

splitVariablesOnSubset :: EffectVar -- ^ Subset to separate out
                       -> [EffectVar] -- ^ Variable to split
                       -> RegionM [EffectVar]
splitVariablesOnSubset subset_var vs = do
  mapM (splitVariableOnSubset subset_var) vs

-- | Attempt to simplify the predicate to an equivalent constraint;
-- throw an exception if the predicate is unsatisfiable for some choice of
-- rigid variables.  The predicate should have been evaluted to expand
-- unified variables.  In addition to the constraint, a @True@ value is
-- returned if any unification was performed.
--
-- After simplification, predicates will always have a flexible variable on
-- the LHS and at least one variable on the RHS.
simplifyPredicate :: Predicate -> RegionM (Constraint, Bool)
simplifyPredicate predicate@(SubEffect lhs_var rhs)
  | rhs `effectMentions` lhs_var =
      -- This equation is a tautology
      return ([], False)

  | not $ isSplittable lhs_var = do
      -- The LHS is not splittable.  Non-splittable variables are
      -- disjoint from one another, so they can be eliminated from the
      -- RHS by splitting all flexible variables in the RHS.
      let splittable_rhs_vars = filter isSplittable $ fromEffect rhs

      -- Split flexible variables
      _ <- splitVariablesOnSubset lhs_var splittable_rhs_vars
      return ([], True)

  | isRVar lhs_var =
      -- Region variables must be not-splittable
      internalError "simplifyPredicate"

  | null (fromEffect rhs) = do
      -- If the RHS is empty, the LHS must be the empty set
      liftIO $ assignEffectVarD "simplifyPredicate" lhs_var emptyEffect
      return ([], True)

  | otherwise = return ([predicate], False)

-- | Attempt to simplify the constraint, considering only one predicate at
-- a time.  Throw an exception if any single predicate is unsatisfiable for
-- some choice of rigid variables.
--
-- After simplification, predicates will always have a flexible variable on
-- the LHS and at least one variable on the RHS.
simplifyConstraint :: Constraint -> RegionM Constraint
simplifyConstraint cst = simplify [] cst
  where
    -- Expand, then simplify predicates one at a time.
    -- Restart if unification occurred.
    simplify simpl_cst (prd:cst) = do
      prd_cst <- liftIO $ evalPredicate prd
      simplify' simpl_cst prd_cst cst

    simplify simpl_cst [] = return simpl_cst

    simplify' simpl_cst (prd:prd_cst) cst = do
      (cst', unification_occurred) <- simplifyPredicate prd
      if unification_occurred
        then simplify [] (simpl_cst ++ cst' ++ prd_cst ++ cst)
        else simplify' (cst' ++ simpl_cst) prd_cst cst
             
    simplify' simpl_cst [] cst = simplify simpl_cst cst

-- | Simplify a constraint as much as possible.  The result is in head
-- normal form.
reduceConstraint :: Constraint -> RegionM Constraint
reduceConstraint cst = debug $ do
  -- TODO: after simplifying, detect and eliminate cycles
  simplifyConstraint cst
  where
    debug x
      | debugConstraints =
          traceShow (hang (text "reducing constraints (not yet expanded):") 4 $
                     pprConstraint cst) x
      | otherwise = x

-- | Solve a constraint where every LHS is a splittable variable.
-- The constraint is in this form at global scope (where no effect or
-- region variables are in scope), after simplifying the constraint.
--
-- The constraint is solved by making all flexible effect variables empty.
solveGlobalConstraint :: Constraint -> RegionM ()
solveGlobalConstraint cst =
  withRigidEffectVars . solve =<< reduceConstraint cst
  where
    solve cst ctx = do
      -- Get the LHS variables.  Remove duplicates.
      let lhs_vars =
            Set.toList $ Set.fromList [lhs_var | SubEffect lhs_var _ <- cst]

      -- Verify that every LHS is a flexible variable
      unless (all isSplittable lhs_vars) $
        internalError "solveGlobalConstraint: Found rigid variables in LHS"

      -- Clear all flexible variables
      forM_ lhs_vars $ \v -> assignEffectVarD "solveGlobal" v emptyEffect

-- | This function does the work of 'eliminateRigidVariable' after reducing 
-- the constraint.  See 'eliminateRigidVariable'.
doEliminateRigidVariable :: EffectVar -- ^ Variable to eliminate
                       -> Constraint
                       -> RegionM Constraint
doEliminateRigidVariable v cst = do
  unlessM (isRigid v) $ internalError "eliminateRigidVariable"

  -- Verify that the variable only appears on the RHS of constraints.
  -- This should always be true if 'reduceConstraint' is called first.
  when False $ when (or [lhs == v | SubEffect lhs _ <- cst]) $
    internalError "eliminateRigidVariable"
    
  -- Remove the variable from all RHSes.
  return $ map (remove v) cst
  where
    remove v (SubEffect lhs rhs) =
      SubEffect lhs (deleteFromEffect v rhs)

-- | Create and simplify constraints representing the fact that the given
-- effects are equal.  Unification may be performed.
mkEqualityConstraint :: Effect -> Effect -> RegionM Constraint
mkEqualityConstraint e1 e2 = do
  -- Simplify the constraint to make solving easier    
  e1_s <- liftIO $ evalEffect e1
  e2_s <- liftIO $ evalEffect e2
  
  -- Remove rigid variables found in both e1 and e2 
  let rigid_common =
        Set.filter isRigid' $
        fromEffectSet e1_s `Set.intersection` fromEffectSet e2_s
      e1_s' = deleteListFromEffect (Set.toList rigid_common) e1_s
      e2_s' = deleteListFromEffect (Set.toList rigid_common) e2_s

  -- In the common case, e1 or e2 is a single variable.
  -- Assign the variable's value now.  If assignment fails, then
  -- the constraints are unsatisfiable.
  case from_singleton e1_s' of
    Just v ->
      case from_singleton e2_s'
      of Just v' | v == v' -> return []
         _ -> do liftIO $ assignEffectVarD "assertEqual" v e2_s'
                 return []
    Nothing ->
      case from_singleton e2_s'
      of Just v -> do liftIO $ assignEffectVarD "assertEqual" v e1_s'
                      return []
         Nothing -> do
           -- Otherwise, create a pair of constraints
           return (subEffect e1 e2 ++ subEffect e2 e1)
  where
    from_singleton eff =
      case fromEffect eff
      of [v] -> Just v
         _ -> Nothing

-- | Eliminate a rigid region or effect variable from all constraints.
-- The constraint must be in head normal form, so that the rigid variable only
-- appears in upper bounds.  If this condition holds, it is safe to delete the
-- variable from all constraints.
--
-- In terms of program semantics, this operation reflects the fact that if a
-- region's lifetime is local to one part of a program, then it is independent 
-- from all side effects elsewhere in the program.  Any effect variables that
-- are visible in the rest of the program must not mention the local region.
-- Therefore, we can delete the local region from the upper bounds of variables
-- visible outside the region.
eliminateRigidVariable :: EffectVar -> Constraint -> RegionM Constraint
eliminateRigidVariable v cst =
  doEliminateRigidVariable v =<< reduceConstraint cst

-- | Eliminate a predicate where the lower bound is a flexible variable.
-- The predicate must be in head normal form.  The variables created during
-- elimination are returned.
--
-- Each splittable variable on the RHS of the constraint is split into two
-- parts, one which is part of the constraint and one which is independent.
-- Unification is performed in the process.
--
-- To eliminate a subset relation of the form
--
-- > e1 <: e2 U e3 U r1
--
-- a new variable is generated for each flexible variable on the RHS:
--
-- > e1 = e2a U e3a U r1
-- > e2 = e2a U e2b
-- > e3 = e3a U e3b
eliminatePredicate :: Predicate -> RegionM [EffectVar]
eliminatePredicate (SubEffect v vs) = do
  ctx <- getRigidEffectVars
  -- DEBUG
  liftIO $ print $ Set.map (show . pprEffectVar) ctx
  
  when (isRigid' v) $ internalError "eliminatePredicate: LHS is rigid"
  --when (v `Set.member` ctx) $ internalError "eliminatePredicate: LHS is rigid"
  when (isRVar v) $ internalError "eliminatePredicate: LHS is a region variable"

  -- Find the flexible variables on the RHS
  let (flexible_vs, rigid_vs) = Set.partition isSplittable $ fromEffectSet vs

  -- Split the flexible variables into two parts
  (dependent_flexible_vs, independent_flexible_vs) <-
    mapAndUnzipM splitEffectVar $ Set.toList flexible_vs

  -- Assign the lower-bound variable
  let v_effect = varsEffect $ dependent_flexible_vs ++ Set.toList rigid_vs
  liftIO $ assignEffectVarD "eliminatePredicate" v v_effect
  
  return (dependent_flexible_vs ++ independent_flexible_vs)

-- | Set all variables that are flexible but not free to the empty effect. 
-- The provided function returns the set of free variables.
clearFlexibleEffectVariables :: IO (Set.Set EffectVar, Set.Set EffectVar)
                             -> [EVar] -> RegionM ()
clearFlexibleEffectVariables get_free_vars vs = withRigidEffectVars $ \ctx -> do
  -- Get the set of free variables
  (pos, neg) <- get_free_vars
  let free_vars = Set.filter isFlexible' $ Set.union pos neg
  -- let free_vars = Set.union pos neg Set.\\ ctx
  
  -- Get the set of flexible variables that aren't free
  vs' <- get_effect_vars vs
  let non_free_vars = vs' Set.\\ free_vars
      
  -- Clear these variables
  forM_ (Set.toList non_free_vars) $ \v -> assignEffectVar v emptyEffect
  where
    get_effect_vars vs = fmap make_effect_vars $ mapM evalEffectVar vs
      where
        make_effect_vars xs =
          Set.fromList $ filter isEVar $ concatMap fromEffect xs

-- | Transform the constraint set into an equivalent one where all
-- flexible variables mentioned by the expression are independent.
makeFlexibleVariablesIndependentWithConstraint ::
  IO (Set.Set EffectVar, Set.Set EffectVar) -> Constraint -> RegionM Constraint
makeFlexibleVariablesIndependentWithConstraint get_free_vars cst = do
  liftIO $ print $ text "MFVI" <+> pprConstraint cst -- DEBUG
  -- simplify the constraint
  cst1 <- reduceConstraint cst
  liftIO $ print $ text "MFVI" <+> pprConstraint cst1 -- DEBUG

  -- Eliminate any constraints that involve a flexible variable on the RHS.
  -- Variables tha appear in positive instances only are replaced by their
  -- lower bounds.
  (fvs_pos, fvs_neg) <- get_flexible_vars
  cst2 <- eliminate_positive_variables cst1 $ Set.toList (fvs_pos Set.\\ fvs_neg)

  -- Constraints on other variables are eliminated by splitting them.
  (fvs_pos, fvs_neg) <- get_flexible_vars
  cst3 <- eliminate_flexible_rhs_constraints [] cst2 (fvs_pos `Set.union` fvs_neg)

  return cst2
  where
    -- Find a positive variable that never appears as part of a union on the
    -- RHS of a constraint
    eliminate_positive_variables cst (v:vs)
      | all (alone_on_rhs v) cst = do
          -- Get the lower bound of v
          let lb_constraint = filter (mentions_on_rhs v) cst
              lb = effectUnions [varEffect lhs
                                | SubEffect lhs _ <- lb_constraint]
          liftIO $ assignEffectVarD "MFVI" v lb
          
          -- Recompute the constraint
          (fvs_pos, fvs_neg) <- get_flexible_vars
          cst' <- reduceConstraint cst
          
          -- Continue
          eliminate_positive_variables cst' $ Set.toList (fvs_pos Set.\\ fvs_neg)
      | otherwise =
          eliminate_positive_variables cst vs

    eliminate_positive_variables cst [] = return cst

    -- True if 'v' is not mentioned in 'rhs', or if 'rhs' contains only one
    -- variable
    alone_on_rhs v (SubEffect _ rhs)
      | Set.size (fromEffectSet rhs) <= 1 = True
      | otherwise = not $ v `Set.member` fromEffectSet rhs
                    
    mentions_on_rhs v (SubEffect _ rhs) = v `Set.member` fromEffectSet rhs

    get_flexible_vars = withRigidEffectVars $ \ctx -> do
      (fvs_pos, fvs_neg) <- get_free_vars
      return $ (fvs_pos Set.\\ ctx, fvs_neg Set.\\ ctx)

    -- Simplify a predicate, then do elimination
    eliminate_flexible_rhs_constraints scanned_cst (prd:cst) fvs = do
      (prd_cst, unification_occurred) <- simplifyPredicate prd
      if unification_occurred
        then eliminate_flexible_rhs_constraints [] (scanned_cst ++ prd_cst ++ cst) fvs
        else eliminate_flexible_rhs_constraints' scanned_cst prd_cst cst fvs
    
    eliminate_flexible_rhs_constraints scanned_cst [] fvs =
      return scanned_cst

    eliminate_flexible_rhs_constraints'
      scanned_cst (prd@(SubEffect lhs_var rhs):prd_cst) cst fvs
      | lhs_var `Set.member` fvs ||
        not (Set.null $ fromEffectSet rhs `Set.intersection` fvs) = do
          -- Eliminate this predicate
          eliminatePredicate prd
          
          -- Recompute the flexible variable set
          (fvs_pos', fvs_neg') <- get_flexible_vars
          let fvs' = Set.union fvs_pos' fvs_neg'

          -- Restart, because unification occurred
          cst' <- reduceConstraint $ scanned_cst ++ prd_cst ++ cst
          eliminate_flexible_rhs_constraints [] cst' fvs'
      | otherwise =
          -- Leave this predicate alone
          eliminate_flexible_rhs_constraints' (prd:scanned_cst) prd_cst cst fvs

    eliminate_flexible_rhs_constraints' scanned_cst [] cst fvs =
      eliminate_flexible_rhs_constraints scanned_cst cst fvs

-------------------------------------------------------------------------------
-- Pretty-printing

pprPredicate :: Predicate -> Doc
pprPredicate (SubEffect v e) = pprEffectVar v <+> text "<:" <+> pprEffect e 

pprConstraint :: Constraint -> Doc
pprConstraint cst = vcat $ map pprPredicate cst
