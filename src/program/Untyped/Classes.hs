{- | Constraint manipulation is performed in this module.
-}

{-# LANGUAGE FlexibleContexts, TypeFamilies, ConstraintKinds, RankNTypes,
             UndecidableInstances #-}
module Untyped.Classes
       (isInstancePredicate, isEqualityPredicate,
        reduceTypeFunction,
        
        Derivation(..),
        toHnf,
        dependentTypeVariables,
        normalizePredicate,
        reduceContext,
        solveConstraint,
        solveConstraintWithContext,
        splitConstraint,
        defaultConstraint)
where

import Control.Applicative
import Control.Monad
import Control.Monad.State
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
import Common.Progress
import Common.SourcePos
import Common.Supply
import Untyped.Builtins2
import Untyped.Instantiation
import Untyped.Kind
import Untyped.Type
import Untyped.TypeUnif
import Untyped.TIMonad
import Untyped.Unif
import Untyped.Variable
import qualified SystemF.Syntax as SystemF
import qualified Builtins.Builtins as SystemF
import Type.Level
import Type.Var
import Globals

-- | Flag turns on debugging dumps during context reduction
debugContextReduction = False

mapAndUnzip3M :: Monad m => (a -> m (b, c, d)) -> [a] -> m ([b], [c], [d])
mapAndUnzip3M f xs = liftM unzip3 $ mapM f xs

isInstancePredicate (IsInst _ _) = True
isInstancePredicate _ = False

isEqualityPredicate (IsEqual _ _) = True
isEqualityPredicate _ = False

isEqualityProof = isEqualityPredicate . fromProof

-------------------------------------------------------------------------------
-- Context reduction environments

-- | A proof construction environment for constructing proofs of predicates. 
--   An environment @Derivation m d@ constructs proofs having type @d@
--   @d@ in monad @m@.
--
--   The monad maintains a proof environment that holds proofs that have been
--   previously produced.  The proof environment contains all proofs
--   created by 'hypothesis' and 'superclassDerivation', and these can be
--   looked up by 'lookupDerivation'.  The proof environment may, but does not
--   have to, contain other proofs.
class (NormalizeContext HMType m) => Derivation m d where
  -- | Lift a 'TE' computation into the derivation monad.
  --   The parameter of type @d@ is ignored and can be 'undefined'.
  liftTE :: d -> TE a -> m a

  -- | Add a hypothesis to the proof environment.
  hypothesis :: Predicate -> m d

  -- | Look up a proof of a predicate.  If found, return it.
  lookupDerivation :: Predicate -> m (Maybe d)

  -- | Derive a class predicate based on an instance declaraction.
  --   Add the predicate to the environment.
  instanceDerivation :: Predicate              -- ^ Derived predicate
                     -> Instance ClassInstance -- ^ Instance satisfying the predicate
                     -> [HMType]               -- ^ Class type arguments
                     -> [d]                    -- ^ Class premises
                     -> [HMType]               -- ^ Instance type arguments
                     -> [d]                    -- ^ Instance premises
                     -> m d
  boxedReprDerivation :: Predicate -> m d
  equalityDerivation :: Predicate -> m d
  coerceDerivation :: Predicate -> Predicate -> d -> m d
  magicDerivation :: Predicate -> m d

  -- | Derive predicates for all superclasses of the given class and add
  --   them to the environment.
  superclassDerivation :: Class       -- ^ A class
                       -> HMType      -- ^ The class's member
                       -> d           -- ^ Derivation of class membership
                       -> m [Proof d] -- ^ Get derivations of all superclasses

-- | A context reduction monad.  The monad maintains a context consisting
--   of a set of reduced predicates.
newtype Ctx a = Ctx {runCtx :: StateT Constraint TE a}

noDerivation :: Ctx a -> Constraint -> TE (a, Constraint)
noDerivation (Ctx m) cst = runStateT m cst

execNoDerivation :: Ctx () -> TE Constraint
execNoDerivation m = do
  ((), c) <- noDerivation m []
  return c

evalNoDerivation :: Ctx a -> TE a
evalNoDerivation m = do
  (x, _) <- noDerivation m []
  return x

-- | Insert a predicate into the context.  This should only be done after the
--   predicate is examined and simplified.
insertPredicate :: Predicate -> Ctx ()
insertPredicate p = Ctx $ modify (p:)

instance Functor Ctx where
  fmap f (Ctx m) = Ctx $ fmap f m

instance Applicative Ctx where
  pure x = Ctx $ pure x
  Ctx f <*> Ctx x = Ctx (f <*> x)

instance Monad Ctx where
  return x = Ctx $ return x
  Ctx m >>= k = Ctx (m >>= runCtx . k)

instance MonadIO Ctx where
  liftIO m = Ctx $ liftIO m

instance EnvMonad Ctx where
  getEnvironment = Ctx $ lift getEnvironment
  withEnvironment f (Ctx m) =
    Ctx $ StateT $ \s -> withEnvironment f (runStateT m s)

instance UMonad HMType Ctx where
  freshUVarID = liftTE () freshUVarID

-- | The 'Ctx' monad is for context reduction.  It does not construct proofs.
instance Derivation Ctx () where
  liftTE _ m = Ctx $ lift m
  hypothesis = insertPredicate

  lookupDerivation prd = Ctx $ StateT $ \ctx -> do
    eq <- anyM (prd `predicatesEqual`) ctx
    return $! if eq then (Just (), ctx) else (Nothing, ctx)

  -- Don't insert a predicate into the environment if it's derivable
  instanceDerivation _ _ _ _ _ _ = return ()
  boxedReprDerivation _ = return ()

  -- Insert equality predicates into the environment.  They will be
  -- extracted and simplified later.
  equalityDerivation = insertPredicate

  coerceDerivation _ _ _ = return ()
  magicDerivation _ = return ()

  superclassDerivation cls ty _ = do
    -- Create superclass derivations, consisting of one @()@ value
    -- for each element of the context
    InstanceType _ cls_constraint _ <- instantiateClass cls ty

    -- Add superclasses to environment
    mapM_ insertPredicate cls_constraint
    return $ asProofs cls_constraint

-------------------------------------------------------------------------------
-- Type function evalution

-- | Attempt to reduce a type function application.  If the arguments are 
--   sufficiently known, reduction will yield a new type.
reduceTypeFunction :: NormalizeContext HMType m =>
                      TyFamily  -- ^ Type function to evaluate
                   -> [HMType]  -- ^ Arguments to the type function
                   -> m (Maybe HMType) -- ^ Reduced type (if reducible)
reduceTypeFunction family [arg] = do
  inst <- findInstance (tfInstances family) arg 
  case inst of
    Nothing -> return Nothing
    Just (InstanceType _ cst (Instance _ (TyFamilyInstance reduced_type)))
      | not $ null cst ->
          -- Constraints not implemented here
          internalError "reduceTypeFunction: Unexpected constraint"
      | otherwise -> 
          return $ Just reduced_type

-------------------------------------------------------------------------------
-- Context reduction

-- | Add all superclass predicates of a given class predicate to the
--   environment
superclassPredicates :: Derivation m d => Proof d -> m ()
superclassPredicates (IsInst tycon ty, derivation) = do
  -- Derive superclasses
  Just cls <- getTyConClass tycon
  superclasses <- superclassDerivation cls ty derivation

  -- Recursively expand superclasses
  mapM_ superclassPredicates superclasses

superclassPredicates (IsEqual tycon ty, _) =
  return ()

superclassPredicates _ = internalError "Not an instance predicate"

{-
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
isH98Hnf :: Predicate -> TE Bool
isH98Hnf predicate = case predicate 
                     of IsInst _ t    -> checkTypeHead t
                        IsEqual t1 t2 -> return False
  where
    checkTypeHead t = normalize t >>= check'
    check' (VarTy _)         = return True
    check' (ConTy c)         = return $ isTyVar c
    check' (FunTy _)         = return False
    check' (TupleTy _)       = return False
    check' (AppTy t _)       = checkTypeHead t
    check' (TFunAppTy _ [t]) = checkTypeHead t

isH98Hnf _ = internalError "isH98Hnf: Not an instance constraint"
-}

-- | Attempt to derive a predicate.  Return a derivation and a constraint 
--   that is logically equivalent to the predicate.
--
--   If the predicate can be simplified, its derivation is returned along with
--   the premises that couldn't be derived.  The returned premises are in HNF.
toHnf :: Derivation m d =>
         SourcePos -> Predicate -> m (Maybe (d, Constraint))
toHnf pos pred = do
  -- If predicate is already in environment, return that
  m_deriv <- lookupDerivation pred
  case m_deriv of
    Just d  -> return $ Just (d, [])
    Nothing -> derive pos pred

-- | No preexisting derivation found; attempt to derive one
derive :: forall m d. Derivation m d =>
          SourcePos -> Predicate -> m (Maybe (d, Constraint))
derive pos pred@(IsInst cls_tycon t) = uncurryApp t >>= examine
  where
    examine (op, args) =
      case op
      of -- If op is a variable or type function, this predicate is in HNF
         VarTy {}            -> is_hnf
         ConTy c | isTyVar c -> is_hnf
         TFunAppTy {}        -> is_hnf

         -- If op is a constructor application, this predicate may be
         -- reducible.  Try to match it against known instances.
         ConTy {}            -> instance_reduction
         FunTy {}            -> instance_reduction
         TupleTy {}          -> instance_reduction

         -- There are no class instances for 'any'
         AnyTy {}            -> unsatisfiable pos pred

         -- Cannot occur: AppTy {}
      where
        is_hnf = return Nothing
        instance_reduction = instanceReduction pos cls_tycon t op args

derive pos pred@(IsEqual _ _) = do
  -- Attempt to simplify the predicate immediately
  (change, cst) <- liftTE (undefined :: d) $
                   cheapEqualitySimplification pos pred
  if change
    then do
      -- Continue processing the simplified constraint
      (_ :: [d], cst') <- toHnfs pos cst      
      d <- equalityDerivation pred
      return $ Just (d, cst')
    else do
      -- Cannot simplify this constraint further
      return Nothing

-- | Attempt to reduce an instance of a predicate whose head is a constructor.
--   Ground terms that can't be reduced are reported as errors.
--
--   The type is passed, as well as its uncurried form.
--
--   Terms with type variables are not reported as errors, since they may
--   become satisfiable later.
instanceReduction :: Derivation m d =>
                     SourcePos -> TyCon
                  -> HMType     -- ^ The type to examine
                  -> HMType     -- ^ The type's uncurried operator
                  -> [HMType]   -- ^ The type's uncurried arguments
                  -> m (Maybe (d, Constraint))
instanceReduction pos cls_tycon ty ty_op ty_args
  -- Function 'Repr' instances are handled specially
  | cls_tycon == builtinTyCon TheTC_Repr && is_FunTy ty_op = do
      d <- boxedReprDerivation pred
      return $ Just (d, [])
  | otherwise = do
      -- Search all instances for a match
      Just cls <- getTyConClass cls_tycon
      m_instance <- findInstance (clsInstances cls) ty
      case m_instance of
        Just inst_inst ->
          instance_derivation cls inst_inst ty

        Nothing ->
          ifM (isGround ty)
            (unsatisfiable pos pred) -- No instance found
            (return Nothing)         -- Cannot resolve predicate
  where
    pred = IsInst cls_tycon ty

    is_FunTy (FunTy {}) = True
    is_FunTy _ = False
    
    -- Found a matching instance.  Create a derivation for it.
    instance_derivation cls inst_inst@(InstanceType _ inst_cst _) ty = do
      -- Get the class constraint also
      cls_inst <- instantiateClassType cls ty

      -- Reduce all superclasses to HNF
      let InstanceType cls_ty_args cls_cst _ = cls_inst
      (cls_superclasses, cls_cst') <- toHnfs pos cls_cst

      let InstanceType inst_ty_args inst_cst inst = inst_inst
      (inst_superclasses, inst_cst') <- toHnfs pos inst_cst

      -- Create an instance derivation
      d <- instanceDerivation pred inst
           cls_ty_args cls_superclasses inst_ty_args inst_superclasses

      return $ Just (d, cls_cst' ++ inst_cst')

-- | Apply cheap, but incomplete, simplification rules to an equality predicate
cheapEqualitySimplification pos pred = do
  -- Simplify this predicate
  (progress, ([], cst')) <- runProgressT $ equalitySimplification pos [] [pred]
  return (progress, cst')

-- | Report that a predicate is unsatisfiable
unsatisfiable :: Derivation m d =>
                 SourcePos -> Predicate -> m (Maybe (d, Constraint))
unsatisfiable pos pred = do
  pred_doc <- runPpr $ pprPredicate pred
  error $ show (text "No instance for" <+> pred_doc)

-- | Convert a predicate to HNF and return its derivation, even if it is
--   already in HNF.
toHnf' :: Derivation m d => SourcePos -> Predicate -> m (d, Constraint)
toHnf' pos pred = do
  m_reduced <- toHnf pos pred
  case m_reduced of
    Nothing -> do
      hyp <- hypothesis pred
      doc <- runPpr (pprPredicate pred)
      liftIO $ print $ text "Inserted" <+> doc
      return (hyp, [pred])
    Just x -> return x

-- | Reduce a list of predicates to HNF
toHnfs :: Derivation m d => SourcePos -> Constraint -> m ([d], Constraint)
toHnfs pos cst = do
  hnfs <- mapM (toHnf' pos) cst
  return (map fst hnfs, concatMap snd hnfs)


-------------------------------------------------------------------------------
-- Entailment
{-
-- | Decide whether the constraint entails the predicate.
entailsPredicate :: Constraint -> Predicate -> TE Bool

-- Check if the instance predicate is in the constraint,
-- including superclasses of predicates in the constraint
entailsPredicate cst prd@(IsInst {}) =
  entailsInstancePredicate cst prd

-- Check if the equality predicate can be eliminated using the other
-- equality predicates in the constraint
entailsPredicate cst prd@(IsEqual {}) = do
  let (equalities, others) = partition isEqualityPredicate cst
  entailsEqualityPredicate equalities prd
-}

{-
-- | Decide whether the constraint entails the predicate, which must be a class
--   instance predicate.
--   If the constraint entails the predicate, then eliminate the predicate and
--   return new, derived predicates.
--   Otherwise, return Nothing.
entailsInstancePredicate :: Derivation m d =>
                            Constraint -> Predicate -> TE Bool
context `entailsInstancePredicate` p@(IsInst _ _) = do
  -- True if the predicate is in the context, including superclasses
  let inst_ps = filter isInstancePredicate context
  anyM p_implied_by inst_ps
  where
    p_implied_by p' = do
      context <- andSuperclassPredicates noDerivation (asProof p')
      anyM (p `predicatesEqual`) $ fromProofs context

_ `entailsInstancePredicate` _ =
  internalError "entailsInstancePredicate: Not an instance predicate"
-}

{-
-- | Decide whether the constraint entails the predicate, which must be a class
--   instance predicate.
--   If the constraint entails the predicate, then eliminate the predicate and
--   return new, derived predicates.
--   Otherwise, return Nothing.
entailsEqualityPredicate :: Constraint -> Predicate -> TE Bool
context `entailsEqualityPredicate` prd = do
  -- Simplify the predicate
  (change1, wanted1) <-
    runProgressT $
    applyEqualityReductionRule equalityReductionRules noSourcePos [prd]

  -- Test entailment on each simplified predicate.
  -- Entailment check succeeds if the context entails all simplified
  -- predicates.  In particular, it succeeds if wanted1 is empty.
  flip allM wanted1 $ \p -> do
    -- Substitute context into wanted predicates
    (change2, wanted2) <-
      runProgressT $ substituteWantedPredicate context p

    -- If anything changed, then retry
    -- Otherwise, entailment check failed
    if change1 || change2
      then context `entailsEqualityPredicate` wanted2
      else return False
-}

-------------------------------------------------------------------------------
-- Equality constraint solving

-- | Simplify a set of equality constraints as much as possible.
--
--   During simplification, perform substitution on a given set of class
--   constraints.  The class constraints are not otherwise modified.
equalitySimplification :: SourcePos -> Constraint -> Constraint
                       -> ProgressT TE (Constraint, Constraint)
equalitySimplification pos cls_csts csts =
  -- Simplify constraints repeatedly until no further simplification is
  -- possible
  fixedpoint simplification_step (cls_csts, csts)
  where
    simplification_step (cls_csts, csts) = do
      csts' <- applyEqualityReductionRule equalityReductionRules pos csts
      (cls_csts', csts'') <- substituteConstraint cls_csts csts'
      return (cls_csts', csts'')

-- | Apply an equality reduction rule to all predicates in a constraint
applyEqualityReductionRule :: EqualityReductionRule
                           -> SourcePos
                           -> Constraint
                           -> ProgressT TE Constraint
applyEqualityReductionRule rule pos cst = go id cst
  where
    go new_cst (prd@(t1 `IsEqual` t2) : cst) = do
      prd_result <- lift $ runEqualityReductionRule rule pos t1 t2
      case prd_result of
        -- No change: go to next constraint
        Nothing        -> go (new_cst . (prd:)) cst

        -- Reduced: continue processing the reduced constraints
        Just (_, cst') -> step >> go new_cst (cst' ++ cst)

    go new_cst [] = return (new_cst [])

newtype EqualityReductionRule =
  EqualityReductionRule 
  {runEqualityReductionRule :: SourcePos
                            -> HMType
                            -> HMType
                            -> TE (Maybe ((), Constraint))}

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
            then Just ((), [])
            else Nothing

-- | Reorient equations of the form @t ~ F t u v@, that is,
--   the RHS is a function application and the LHS appears somewhere under it.
--
--   (Other reorienting rules appear in 'decompRule').
funSwapRule :: EqualityReductionRule
funSwapRule = EqualityReductionRule $ \pos t1 t2 ->
  let swap =
        return $ Just ((), [t2 `IsEqual` t1])
  in do
    (t2_head, t2_args) <- uncurryApp t2
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
        in return (Just ((), new_constraints))

      -- Swap the LHS and RHS of the equality predicate so that it's usable as
      -- a left-to-right rewrite rule.
      swap =
        return (Just ((), [t2 `IsEqual` t1]))

      -- The predicate is unsolvable because it relates two different injective
      -- data constructors
      contradiction = do
        doc <- runPpr $ do
          t1_doc <- pprType t1
          t2_doc <- pprType t2
          return $ t1_doc <+> text "=" <+> t2_doc
        liftIO $ print doc
        fail "Unsolvable type equality constraint detected"
  in do
    (t1_head, t1_args) <- uncurryApp t1
    (t2_head, t2_args) <- uncurryApp t2
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
  let success = return $ Just ((), [])

      -- Unify a variable with a type only if the variable does not occur in
      -- the type.  It's not an error for a variable to occur under a type
      -- function.
      unify_with_type v ty =
        -- If the variable does not occur in the type, then unify
        ifM (liftM not $ occursCheck v ty) (unifyUVar v ty >> success) $

        -- If the variable occurs under injective type constructors, then error
        ifM (occursInjectively v ty)
          (fail "Occurs check failed in equality constraint") $

        return Nothing

  in do
    t1_c <- normalize t1
    t2_c <- normalize t2
    case (t1_c, t2_c) of
      (VarTy v1, VarTy v2) -> unifyUVars v1 v2 >> success
      (VarTy v1, _) -> unify_with_type v1 t2_c
      (_, VarTy v2) -> unify_with_type v2 t1_c
      _ -> return Nothing

-- | Perform substitution in the entire equality constraint.
--   Return True if any substitution occurred in the equality constraints.
--
--   Also substitute into the given non-equality constraints.
substituteConstraint :: Constraint -> Constraint
                     -> ProgressT TE (Constraint, Constraint)
substituteConstraint cls_csts cst = go cls_csts [] cst
  where
    -- Process one predicate at a time
    go cls_csts visited (prd : unvisited) = do
      (cls_csts', visisted', unvisited') <-
        substituteEqualityCoercion prd cls_csts visited unvisited

      go cls_csts' (prd : visisted') unvisited'
        
    go cls_csts visited [] = return (cls_csts, visited)

-- | Substitute the given constraint into the wanted predicate.
--   Return True if any substitution occurred.
substituteWantedPredicate :: Constraint -> Predicate
                          -> ProgressT TE Predicate
substituteWantedPredicate given wanted =
  fixedpoint (substitute_predicate_exhaustively given) wanted
  where

{-    -- Exhaustively substitute each given predicate into each wanted predicate
    substitute_exhaustively ps (w:ws) = do
      (w_change, w') <- substitute_predicate_exhaustively ps w
      (ws_change, ws') <- substitute_exhaustively ps ws
      return (w_change || ws_change, w' ++ ws')

    substitute_exhaustively ps [] =
      return (False, [])-}

    -- Exhaustively substitute each given predicate into one wanted predicate
    substitute_predicate_exhaustively (p:ps) (IsEqual lhs rhs) = do
      w' <- substitutePredicateExhaustively lhs rhs p
      substitute_predicate_exhaustively ps w'
  
    substitute_predicate_exhaustively [] p = return p

-- | Return 'True' iff this predicate should be used in a substitution
shouldSubstituteCoercion :: Predicate -> TE Bool
shouldSubstituteCoercion (IsEqual lhs rhs) = do
  -- Require that head of LHS is not injective
  lhs_injective <- headIsInjective lhs
  if lhs_injective
    then return False
    else do
      -- Require that LHS is not a subexpression of RHS
      rhs_contains_lhs <- subexpressionCheck lhs rhs
      return $ rhs_contains_lhs == False
  
shouldSubstituteCoercion _ = return False

-- | Given an equality coercion satisfying some criteria, exhaustively
--   apply the coercion as a rewrite rule to all other equality predicates
--   in the context.
--
--   If any substitutions were made, then return the substituted constraints.
substituteEqualityCoercion :: Predicate  -- ^ Equality predicate to apply
                           -> Constraint -- ^ Class constraints
                           -> Constraint -- ^ Visited constraints
                           -> Constraint -- ^ Unvisited constraints
                           -> ProgressT TE (Constraint, Constraint, Constraint)
                           -- ^ Compute new class, visited, unvisited constraints
substituteEqualityCoercion predicate@(IsEqual lhs rhs) cls_csts cst_l cst_r =
  -- Test whether the predicate should be applied as a rewrite rule
  ifM (lift $ shouldSubstituteCoercion predicate) apply skip
  where
    skip = return (cls_csts, cst_l, cst_r)

    apply = do
      -- Apply the substitution to all other predicates.
      -- Progress has been made if substitutions were made in
      -- any equality constraints.
      cls_csts' <- ignoreProgress $ substitute_exhaustively_list cls_csts
      cst_l' <- substitute_exhaustively_list cst_l
      cst_r' <- substitute_exhaustively_list cst_r
      return (cls_csts', cst_l', cst_r')

    substitute_exhaustively_list ps =
      mapM (substitutePredicateExhaustively lhs rhs) ps

-- Exhaustively perform substitution in a predicate.
-- Return 'True' if any substitutions have been made.
substitutePredicateExhaustively :: HMType
                                -> HMType
                                -> Predicate
                                -> ProgressT TE Predicate
substitutePredicateExhaustively old new prd = fixedpoint go prd
  where
    go (IsEqual t1 t2) = do
      t1' <- liftStep $ substituteType old new t1
      t2' <- liftStep $ substituteType old new t2
      return (IsEqual t1' t2')

    go (IsInst cls t) = do
      t' <- liftStep $ substituteType old new t
      return (IsInst cls t')

-- | Apply all the substitutions in the given context to a predicate
applySubstitutions :: Constraint -> Predicate -> ProgressT TE Predicate
applySubstitutions ctx prd = go ctx prd
  where
    go (p:ctx) prd = ifM (lift $ shouldSubstituteCoercion p) apply skip
      where
        IsEqual lhs rhs = p

        apply = go ctx =<< substitutePredicateExhaustively lhs rhs prd
        skip = go ctx prd
      
    go [] prd = return prd

-- | Normalize the predicate with respect to the context.
--   All the substitutions in the context are applied to the predicate.
--   Return 'True' if the predicate changed.
normalizePredicate :: Constraint -> Predicate -> TE (Bool, Predicate)
normalizePredicate c p = runProgressT $ applySubstitutions c p

-------------------------------------------------------------------------------
-- Context reduction

-- | Perform context reduction.
--
-- Given a set of constraints, context reduction creates an equivalent but  
-- simplified set of constraints.  It's possible to derive the given 
-- constraints from the simplified ones. 
-- The simplified constraints are in head-normal form with no
-- redundant constraints.
reduceContext :: Constraint -> TE Constraint
reduceContext wanted_cst = do
  when debugContextReduction $ do
    old_context <- runPpr (pprConstraint wanted_cst)
    liftIO $ print $ text "Start context reduction:" <+> old_context

  -- Add superclass equality predicates to the constraint before solving
  all_superclasses <-
    execNoDerivation $ mapM_ superclassPredicates $ asProofs wanted_cst
  let superclass_equalities = filter isEqualityPredicate all_superclasses

  c1 <- runPpr (pprConstraint superclass_equalities)
  liftIO $ print $ text "Superclasses:" <+> c1

  -- Reduce until a fixed point is reached
  cst' <- fixed_point_reduce superclass_equalities wanted_cst

  when debugContextReduction $ do
    old_context <- runPpr (pprConstraint wanted_cst)
    new_context <- runPpr (pprConstraint cst')
    liftIO $ print $ hang (text "End context reduction:" <+> old_context) 4 new_context

  return cst'
  where
    fixed_point_reduce :: Constraint -> Constraint -> TE Constraint
    fixed_point_reduce given_eq_cst cst = do
      -- Partition 'cst' into equality and class proofs
      let (eq_cst, cls_cst) = 
            let (e, c) = partition isEqualityPredicate cst
            in (e ++ given_eq_cst, c)

      -- Do equality constraint simplification
      -- Currently we don't derive proofs here; we just fabricate the
      -- necessary proof objects
      c2 <- runPpr (pprConstraint cls_cst)
      liftIO $ print $ text "Expanded:" <+> c2
      (cls_cst', eq_cst') <-
        evalProgressT $ equalitySimplification noSourcePos cls_cst eq_cst

      c3 <- runPpr (pprConstraint cls_cst')
      liftIO $ print $ text "Expanded:" <+> c3
      -- Eliminate redundant proofs
      cls_cst'' <- evalNoDerivation $ addConstraintToContext cls_cst'
      c4 <- runPpr (pprConstraint cls_cst'')
      liftIO $ print $ text "Simplified:" <+> c4

      -- If any new equality predicates were introduced by class reduction,
      -- repeat the proces
      if any isEqualityPredicate cls_cst''
        then fixed_point_reduce eq_cst' cls_cst''
        else return (eq_cst' ++ cls_cst'')

-- | Solve a constraint with respect to the context.
--   Return any leftover, unsolved constraints.
solveConstraint :: Derivation m d =>
                   SourcePos -> Constraint -> m ([d], Constraint)
solveConstraint pos wanted = toHnfs pos wanted

-- | Solve a constraint with respect to the context.
--   Return any leftover, unsolved constraints.
--
--   The given and wanted constraints are not necessarily normalized.
--   The given constraints are not necessarily a terminating rewrite system.
solveConstraintWithContext :: SourcePos -> Constraint -> Constraint
                           -> TE Constraint
solveConstraintWithContext pos context wanted = do
  -- Normalize the context 
  reduced_context <- reduceContext context

  -- Solve the wanted constraint using the context.
  -- Return the unsolved constraint.
  ((_ :: [()], residual), _) <-
    noDerivation (solveConstraint pos wanted) reduced_context
  return residual


-- | Add the extra information from a predicate to the context.
--   Get the reduced context.
addToContext :: Predicate -> Ctx Constraint
addToContext pred = trace "addToContext" $ do
  ((), cst) <- toHnf' noSourcePos pred
  return cst

addConstraintToContext cst = liftM concat $ mapM addToContext cst

-------------------------------------------------------------------------------
-- Generalization-related functions

-- | Find variables that may be dependent on a given set of variables subject to
--   a constraint.  The constraint parameter should be reduced constraint
--   returned by 'reduceContext'.
--
--   A variable is dependent if, after assigning types to all type variables in
--   the given set, the variable _may_ become equal to some other term.  It is
--   independent if it will definitely remain a variable.
--
--   Underestimating independence may lead to less useful type checking error
--   messages, but (with one important caveat) will not affect the behavior of 
--   programs.  The caveat is that defaulting is only applied to independent
--   types, so we need to determine independence at least for the class of
--   types that are involved in defaulting rules.  Those types are
--   single-parameter type classes, and equalities of the form @F a ~ t@
--   where @F@ is a type function, @a@ is a type variable, and @t@ is any type.
--
--   Currently, dependence is based on participation in equality constraints.
--   If all variables on one side of an equality constraint are in the given
--   set, then all variables on the other side are considered dependent.
dependentTypeVariables :: Constraint -> TyVarSet -> TE TyVarSet
dependentTypeVariables cst initial_set = do
  -- For each equality constraint, find the free variables of its LHS and RHS
  equality_freevars <-
    sequence [do fv1 <- freeUVars t1
                 fv2 <- freeUVars t2
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
        fv1_subset = not (Set.null fv1) && fv1 `Set.isSubsetOf` s
        fv2_subset = not (Set.null fv2) && fv2 `Set.isSubsetOf` s

-- | An action taken by splitConstraint
data SplitAction = Retain | Defer | Ambiguous

-- | Partition a set of constraints into a retained set and a deferred set.
-- A constraint is retained if it mentions any variable in the given set of
-- \"bound\" variables.
splitConstraint :: Constraint   -- ^ Constraint to partition. 
                                --   Must have been simplified
                                --   by 'reduceContext'.
                -> TyVarSet     -- ^ Free variables
                -> TyVarSet     -- ^ Bound variables
                -> TE (Constraint, Constraint)
                   -- ^ Returns (retained constraints,
                   -- deferred constraints)
splitConstraint cst fvars qvars = do
  runPpr $ do
    free_doc <- mapM pprUVar $ Set.toList fvars
    q_doc <- mapM pprUVar $ Set.toList qvars
    cst_doc <- pprConstraint cst
    liftIO $ print (hsep free_doc $$ hsep q_doc $$ cst_doc)
    
  (retained, deferred, ambiguous) <- partitionM isRetained cst
  
  -- Need to default some constraints?
  if null ambiguous
    then return (retained, deferred)
    else do
    -- Attempt to apply defaulting rules, then retry
    (default_progress, new_csts) <- defaultConstraints ambiguous
    if default_progress
      then do
      cst' <- reduceContext (new_csts ++ cst)
      splitConstraint cst' fvars qvars
      else
      -- Defaulting conditions were not met for any constraint
      ambiguity_error ambiguous
  where
    ambiguity_error xs = do
      cst_doc <- runPpr $ pprConstraint xs
      fail ("Ambiguous constraint:\n" ++ show cst_doc)
    isRetained prd = do
      fv <- predicateFreeVars prd

      -- Error if this predicate has no variables.  Such predicates 
      -- should have been eliminated by 'reduceContext'.
      when (Set.null fv) $ whenM (Set.null `liftM` freeC prd) $
        internalError "splitConstraint: Found unresolved predicate with no free variables"
      
      -- If only variables from the environment are mentioned, then
      -- defer this predicate.  If only variables from the environment and
      -- local context are mentioned, then retain this predicate.
      -- Otherwise the predicate is ambiguous; try to resolve it by
      -- defaulting.
      return $! case ()
                of _ | fv `Set.isSubsetOf` fvars                 -> Defer
                     | fv `Set.isSubsetOf` Set.union fvars qvars -> Retain
                     | otherwise                                 -> Ambiguous
    
    partitionM f xs = go xs [] [] []
      where
        go (x:xs) lefts rights ambigs = do
          b <- f x
          case b of
            Retain    -> go xs (x:lefts) rights ambigs
            Defer     -> go xs lefts (x:rights) ambigs
            Ambiguous -> go xs lefts rights (x:ambigs)

        go [] lefts rights ambigs =
          return (reverse lefts, reverse rights, reverse ambigs)

-- | Perform defaulting on a list of constraints.  Determine whether
--   at least one defaulting occurred.  Construct a new constraint list.
defaultConstraints :: Constraint -> TE (Bool, Constraint)
defaultConstraints predicates = go False [] predicates
  where
    -- Attempt to perform defaulting on each constraint, one at a time
    go change visited (p:cs) = do
      -- Try to perform defaulting for 'p'
      result <- defaultConstraint visited cs p
      case result of
        Nothing              -> go change (p:visited) cs
        Just (visited', cs') -> go True   visited'    cs'

    go change visited [] = return (change, reverse visited)

-- | Examine the given predicate and, if it is suitable for defaulting,
--   unify it with a default type.
--   The predicate is suitable for defaulting if its head is a type variable 
--   and the default choice is compatible with other constraints.
--
--   If defaulting succeeded, add new generated constraints to the
--   unvisited set.
--
--   Defaulting first checks if the given type was already unified (by
--   an earlier defaulting step) and skips if that is the case.
defaultConstraint :: Constraint -> Constraint -> Predicate
                  -> TE (Maybe (Constraint, Constraint))
defaultConstraint visited unvisited prd =
  case prd
  of IsInst cls head
       | cls == builtinTyCon TheTC_Traversable ->
           with_flexible_var_type head $
           defaultTraversableConstraint visited unvisited

     _ -> return Nothing
  where
    -- If the given type is a flexible type variable,
    -- pass the type variable to the function.
    -- If it is a rigid type variable, report an error.
    -- Otherwise, this is not a suitable candidate for defaulting.
    with_flexible_var_type ty f = do
      ty' <- normalize ty
      case ty' of
        VarTy v -> f v
        ConTy c | isTyVar c -> internalError "defaultConstraint: Unexpected rigid variable"
        _ -> can't_default

    can't_default = return Nothing

-- | Defaulting for a @Traversable@ constraint.  A traversable type defaults
--   to @list@, @array1@, @array2@ or @array3@ under suitable conditions.
--
--   The only other permitted constraints on the type variable are:
--
-- * @Repr (t _)@
-- * @Indexable t@
--
--   Additionally, the following constraints are used to choose a default
--   instance:
--
-- * @shape t ~ list_dim@ (t is 'list')
-- * @shape t ~ dim1@     (t is 'array1')
-- * @shape t ~ dim2@     (t is 'array2')
-- * @shape t ~ dim3@     (t is 'array3')
--
-- Note that constraints @Shape (shape t)@, @index (shape t) ~ _@,
-- @Cartesian (shape t)@, and @shape t ~ cartesianDomain _@ don't appear
-- when the shape is known

defaultTraversableConstraint :: Constraint -> Constraint -> TyVar
                             -> TE (Maybe (Constraint, Constraint))
defaultTraversableConstraint visited unvisited tyvar = do
  dependent_cst <- do
    d1 <- find_dependent_constraints visited
    d2 <- find_dependent_constraints unvisited
    return (d1 ++ d2)

  -- Determine the shape 
  m_shape <- find_shape_constraint dependent_cst
  case m_shape of
    Just sh
      | sh == builtinTyCon TheTC_list_dim ->
          defaultable dependent_cst (ConTy $ builtinTyCon TheTC_list)
      | sh == builtinTyCon TheTC_dim0 ->
          defaultable dependent_cst (ConTy $ builtinTyCon TheTC_array0)
      | sh == builtinTyCon TheTC_dim1 ->
          defaultable dependent_cst (ConTy $ builtinTyCon TheTC_array1)
      | sh == builtinTyCon TheTC_dim2 ->
          defaultable dependent_cst (ConTy $ builtinTyCon TheTC_array2)
      | sh == builtinTyCon TheTC_dim3 ->
          defaultable dependent_cst (ConTy $ builtinTyCon TheTC_array3)
    _ -> can't_default
  where
    -- All conditions were met.  Unify 'tyvar' with 't'
    default_to t = do
      unifyUVar tyvar t
      return $ Just (visited, unvisited)

    -- Didn't meet conditions.
    can't_default = return Nothing

    -- Chose a default type.  Verify that all constraints mentioning
    -- the type variable are permitted, so that defaulting produces no
    -- unintended effects.
    defaultable dependent_cst target_type =
      ifM (allM permitted_constraint dependent_cst)
      (default_to target_type)
      can't_default

    permitted_constraint (IsInst cls ty)
      | cls == builtinTyCon TheTC_Repr = do
          -- Type must be of the form @a t@ for any @t@
          (head, args) <- uncurryApp ty
          case head of
            VarTy v | v == tyvar -> return True
            _ -> return False

      | cls == builtinTyCon TheTC_Indexable = do
          -- Type must be @t@
          ty' <- normalize ty
          case ty' of
            VarTy v | v == tyvar -> return True
            _ -> return False

    permitted_constraint c = do
      -- If this is a shape constraint, it is permitted
      m_shape <- find_shape_constraint [c]
      return $ isJust m_shape

    -- Find the constraints that mention 'tyvar'
    find_dependent_constraints c = filterM depends c
      where
        depends prd = do
          fv <- predicateFreeVars prd
          return $ tyvar `Set.member` fv

    -- Find a constraint of the form @shape t ~ T@
    -- where @t@ is the defaulted type variable and @T@ is a type
    -- constructor.
    find_shape_constraint :: Constraint -> TE (Maybe TyCon)
    find_shape_constraint (c:cs) =
      case c
      of IsEqual t1 t2 ->
           check_shape t1 t2 $ check_shape t2 t1 $ find_shape_constraint cs
         _ -> find_shape_constraint cs
      where
        check_shape :: HMType -> HMType -> TE (Maybe TyCon) -> TE (Maybe TyCon)
        check_shape shape_term value_term k = do
          shape_matched <- is_shape shape_term
          if shape_matched
            then do
            mc <- is_tycon value_term
            case mc of
              Just x  -> return mc
              Nothing -> k
            else k

        -- Is 't' the term @shape t@ ?
        is_shape t = do
          t' <- normalize t
          case t' of
            TFunAppTy tc [arg]
              | tc == builtinTyCon TheTC_shape -> do
                  arg' <- normalize arg
                  case arg' of
                    VarTy v | v == tyvar -> return True
                    _ -> return False
            _ -> return False

        -- Is 't' a nullary type constructor?
        is_tycon t = do
          t' <- normalize t
          return $! case t'
                    of ConTy v | isTyCon v -> Just v
                       _ -> Nothing

    find_shape_constraint [] = return Nothing

