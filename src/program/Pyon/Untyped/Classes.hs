
{-# LANGUAGE TypeFamilies #-}
module Pyon.Untyped.Classes
       (entails, entailsHnf,
        isHnf, toHnf,
        reduceContext,
        splitConstraint,
        prove)
where

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Maybe
import Data.List
import Data.Function
import qualified Data.Set as Set
import Text.PrettyPrint.HughesPJ 

import Gluon.Common.Error
import Gluon.Common.MonadLogic
import Gluon.Common.SourcePos
import Gluon.Core(Level(..), Var(..))
import qualified Gluon.Core as Gluon
import Pyon.Untyped.HMType
import Pyon.Untyped.GenSystemF
import qualified Pyon.SystemF.Syntax as SystemF
import Pyon.Globals

withMany :: (a -> (b -> c) -> c) -> [a] -> ([b] -> c) -> c
withMany f xs k = go xs k
  where
    go (x:xs) k = f x $ \y -> go xs $ \ys -> k (y:ys)
    go []     k = k []

doAny :: Monad m => [MaybeT m a] -> MaybeT m a
doAny xs = MaybeT $ case xs of 
  m:ms -> do
    x <- runMaybeT m
    case x of
      Nothing -> runMaybeT $ doAny ms
      Just _  -> return x
  [] -> return Nothing

-- | Get all superclass predicates of a given class predicate
superclassPredicates :: Predicate -> [Predicate]
superclassPredicates (IsInst _ cls) = 
  concatMap andSuperclassPredicates $ clsConstraint cls

-- | Get a class and its superclass predicates
andSuperclassPredicates :: Predicate -> [Predicate]
andSuperclassPredicates p = p : superclassPredicates p

-- | Return True if the constraint entails the predicate, False otherwise
entails :: Constraint -> Predicate -> IO Bool
ps `entails` p =
  -- True if the predicate is in the context, including superclasses
  anyM (p `uEqual`) (concatMap andSuperclassPredicates ps) >||>
  
  -- True if the predicate matches an instance, and all subgoals are satisfied 
  do ip <- instancePredicates p
     case ip of
       Nothing -> return False
       Just (cls_cst, _, inst_cst) -> allM (ps `entails`) (cls_cst ++ inst_cst)

-- | A more efficient version of 'entails' assuming that all inputs are in
-- head-normal form.  Return True if the constraint entails the predicate,
-- False otherwise
entailsHnf :: Constraint -> Predicate -> IO Bool
ps `entailsHnf` p =
  -- True if the predicate is in the context, including superclasses
  anyM (p `uEqual`) (concatMap andSuperclassPredicates ps)

-- | Determine whether a predicate is in head-normal form.
--
-- If the predicate's head is a variable, it is in head-normal form.
-- Otherwise, it is a type constructor and it should be possible to reduce it.
isHnf :: Predicate -> IO Bool
isHnf (IsInst t c) = canonicalizeHead t >>= checkHead
  where
    checkHead t = 
      case t
      of ConTy c   -> return $ isTyVar c
         FunTy _   -> return False
         TupleTy _ -> return False
         AppTy t _ -> checkHead t 

-- | Convert a predicate to a conjunction of logically equivalent predicates
-- in head-normal form.  The list may contain duplicates.
-- A description of the conversion steps taken is also returned.
--
-- If the predicate cannot be converted to head-normal form, an error is
-- thrown.  It represents a type class error in the input program.
toHnf :: SourcePos -> Predicate -> IO (Derivation, Constraint)
toHnf pos pred = do
  -- If already in HNF, derivation is trivial
  is_hnf <- isHnf pred
  if is_hnf then return (IdDerivation pred, [pred]) else do
    -- Context reduction
    ip <- instancePredicates pred
    case ip of
      Nothing -> do
        -- Can't derive a class dictionary for this type
        [prdDoc] <- uShow [pred]
        let msg = text (show pos) <> text ":" <+>
                  text "No instance for" <+> prdDoc
        fail (show msg)
      Just (cls_cst, inst, inst_cst) -> do
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

-- | Convert a constraint to HNF and ignore how it was derived
toHnfConstraint :: Predicate -> IO Constraint
toHnfConstraint p = liftM snd $ toHnf noSourcePos p

-- | Simplify a constraint by removing redundant predicates.  All predicates 
-- are assumed to be in head-normal form.
simplifyContext :: Constraint -> IO Constraint
simplifyContext ps = addIfNotEntailed [] ps
  where
    -- Add each predicate to the simplified list, if it is not entailed by
    -- the rest of the context
    addIfNotEntailed simplified (pred : predicates) = do
      b <- (simplified ++ predicates) `entailsHnf` pred
      let simplified' = if b then simplified else pred : simplified
      addIfNotEntailed simplified' predicates
    
    -- Reverse the list to maintain the order of the input 
    addIfNotEntailed simplified [] = return $ reverse simplified

-- | Perform context reduction.
--
-- A set of constraints is reduced to a constraint set that is in
-- head-normal form with no redundant constraints.
reduceContext :: Constraint -> IO Constraint
reduceContext csts = simplifyContext . concat =<< mapM toHnfConstraint csts

-- | Try to satisfy a predicate with one of the known class instances.
-- If a match is found, return a list of subgoals generated for the class,
-- the matching instance, and a -- list of subgoals generated for the instance.
instancePredicates :: Predicate 
                   -> IO (Maybe (Constraint, Instance, Constraint))
instancePredicates (IsInst t cls) = do
  t' <- canonicalizeHead t
  
  runMaybeT $ do
    -- Common case shortcut: if the head is a type variable, we won't find
    -- any instances
    case t' of
      ConTy con | isTyVar con -> fail "No instances"
      _ -> return ()
    
    -- Match against all instances until one succeeds 
    (inst, inst_cst) <- doAny $ map (instancePredicate t) $ clsInstances cls
  
    -- Get the class constraints
    -- If an instance matched, then the class must match also
    cls_cst <- lift $ mapM (instantiatePredicate t) $ clsConstraint cls
    
    return (cls_cst, inst, inst_cst)
  where
    instancePredicate inst_type inst = do
      -- Try to match this type against the instance's type
      subst <- MaybeT $ match (insType inst) inst_type

      -- If successful, return the instance and its substituted constraints
      inst_cst <- lift $ mapM (rename subst) $ insConstraint inst
      return (inst, inst_cst)
    
    -- Instantiate a superclass predicate
    instantiatePredicate inst_type pred =
      case pred
      of IsInst ty' _ -> do
           -- Predicate type must match, because the instance matched
           Just subst <- match ty' inst_type
           rename subst pred

-- | Partition a set of constraints into a retained set and a deferred set.
-- A constraint is retained if it mentions any variable in the given set of
-- \"bound\" variables.
--
-- TODO: Apply defaulting rules when the constraint is ambiguous
splitConstraint :: Constraint   -- ^ Constraint to partition
                -> TyVarSet     -- ^ Free variables
                -> TyVarSet     -- ^ Bound variables
                -> IO (Constraint, Constraint) 
                   -- ^ Returns (retained constraints, deferred constraints)
splitConstraint cst fvars qvars = do
  cst' <- reduceContext cst
  partitionM isRetained cst'
  where
    isRetained cst = do
      fv <- freeTypeVariables cst
      return $! if fv `Set.isSubsetOf` fvars then False
                else if fv `Set.isSubsetOf` Set.union fvars qvars then True
                     else error "Ambiguous constraint"
    
    partitionM f xs = go xs [] []
      where
        go (x:xs) lefts rights = do
          b <- f x
          (lefts', rights') <- return $ if b
                                        then (x:lefts, rights)
                                        else (lefts, x:rights)
          go xs lefts' rights'
        go [] lefts rights =
          return (reverse lefts, reverse rights)

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
           -- Create instance methods
           inst_methods <- instantiateClassMethods pos inst inst_type i_env
           
           -- Create dictionary expression
           let hmtype = convertHMType inst_type
               superclasses = map (mkVarE pos) c_vars
               dict = mkDictE pos cls hmtype superclasses inst_methods
           return (dict, [])

       return (True, placeholders, proof)
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
  id <- getNextVarIdent
  let v = Gluon.mkAnonymousVariable id ObjectLevel
  
  -- Create body
  (body, x) <- make_body v
  
  -- Create let expression
  return (mkLetE pos (SystemF.VarP v ty) rhs body, x)

withLocalAssignments :: SourcePos
                     -> [(TIExp, TIType)] 
                     -> ([Var] -> IO (TIExp, a)) 
                     -> IO (TIExp, a)
withLocalAssignments pos = withMany (uncurry (withLocalAssignment pos))

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
    let method_exp = mkConE pos (inmName method)
    in instanceExpressionWithProofs env pos ty_params constraint method_exp
