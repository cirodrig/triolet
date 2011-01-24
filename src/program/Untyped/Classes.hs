{- | Constraint manipulation is performed in this module.
-}

{-# LANGUAGE TypeFamilies #-}
module Untyped.Classes
       (toHnf,
        reduceContext,
        splitConstraint,
        defaultConstraint,
        prove)
where

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Maybe
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

pprList :: [Doc] -> Doc
pprList xs = brackets $ sep $ punctuate (text ",") xs

doAny :: Monad m => [MaybeT m a] -> MaybeT m a
doAny xs = MaybeT $ case xs of 
  m:ms -> do
    x <- runMaybeT m
    case x of
      Nothing -> runMaybeT $ doAny ms
      Just _  -> return x
  [] -> return Nothing

mapAndUnzip3M :: Monad m => (a -> m (b, c, d)) -> [a] -> m ([b], [c], [d])
mapAndUnzip3M f xs = liftM unzip3 $ mapM f xs

isInstancePredicate (IsInst _ _) = True
isInstancePredicate _ = False

-- | Somewhat of a hack.  Decide whether this is the distinguished type class
-- for object layout information. 
isPassableClass cls = clsName cls == "Repr"

-------------------------------------------------------------------------------
-- Context reduction

-- | Get all superclass predicates of a given class predicate
superclassPredicates :: Predicate -> [Predicate]
superclassPredicates (IsInst _ cls) = 
  concatMap andSuperclassPredicates $ clsConstraint cls

superclassPredicates _ = internalError "Not an instance predicate"

-- | Get a class and its superclass predicates
andSuperclassPredicates :: Predicate -> [Predicate]
andSuperclassPredicates p = p : superclassPredicates p

-- | Decide whether the constraint entails the predicate, which must be a class
-- instance predicate.
entailsInstancePredicate :: Constraint -> Predicate -> IO Bool
ps `entailsInstancePredicate` p@(IsInst _ _) =
  -- True if the predicate is in the context, including superclasses
  let context = concatMap andSuperclassPredicates $
                filter isInstancePredicate ps
  in anyM (p `uEqual`) context

-- | Decide whether the constraint entails the predicate, which must be an
-- equality predicate.
entailsEqualityPredicate :: Constraint -> Predicate -> IO Bool
ps `entailsEqualityPredicate` p =
  -- True if the predicate is in the context
  let context = ps
  in anyM (p `uEqual`) context

-- | Determine whether a class instance predicate is in head-normal form.
--
-- If the predicate's head is a variable, it is in head-normal form.
-- Otherwise, it is a type constructor and it should be possible to reduce it.
isHnf :: Predicate -> IO Bool
isHnf (IsInst t c) = checkTypeHead t
  where
    checkTypeHead t = do
      t' <- canonicalizeHead t
      case t' of
        ConTy c     -> return $ isTyVar c
        FunTy _     -> return False
        TupleTy _   -> return False
        AppTy t'' _ -> checkTypeHead t''

isHnf _ = internalError "isHnf: Not an instance constraint"

-- | Convert a predicate to a conjunction of logically equivalent predicates
-- in head-normal form.  The list may contain duplicates.
-- A description of the conversion steps taken is also returned.
--
-- If the predicate cannot be converted to head-normal form, an error is
-- thrown.  It represents a type class error in the input program.
toHnf :: SourcePos -> Predicate -> IO (Derivation, Constraint)
toHnf pos pred =
  case pred
  of IsInst _ _ -> do
       -- If already in HNF, derivation is trivial
       is_hnf <- isHnf pred
       if is_hnf then return (IdDerivation pred, [pred]) else do
         -- Otherwise, perform reduction based on class instances
         instanceReduction pos pred

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
      NotReduced -> do
        -- Can't derive a class dictionary for this type
        prdDoc <- runPpr $ uShow pred
        let msg = text (show pos) <> text ":" <+>
                  text "No instance for" <+> prdDoc
        fail (show msg)

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
-- Context reduction

-- | Perform context reduction.
--
-- A set of constraints is reduced to a constraint set that is in
-- head-normal form with no redundant constraints.
reduceContext :: Constraint -> IO Constraint
reduceContext csts = do 
  csts' <- foldM addToContext [] csts
  return csts'

-- | Add the extra information from a predicate to the context.  The 
-- context must be in head-normal form.
addToContext :: Constraint -> Predicate -> IO Constraint
addToContext ctx pred = foldM addToContextHNF ctx =<< toHnfConstraint pred

-- | Add the extra information from a predicate to the context.  The 
-- context and predicate must be in head-normal form.
addToContextHNF :: Constraint -> Predicate -> IO Constraint
addToContextHNF ctx pred 
  | isInstancePredicate pred = do
      b <- entailsInstancePredicate ctx pred
      if b then return ctx else return (pred:ctx)
  | otherwise = internalError "addToContextHNF"

data InstanceReductionStep =
    NotReduced
  | InstanceReduced Constraint Instance Constraint
  | FunctionPassableReduced HMType

-- | Try to satisfy a predicate with one of the known class instances.
-- If a match is found, return a list of subgoals generated for the class,
-- the matching instance, and a list of subgoals generated for the instance.
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
      (inst, inst_cst) <- doAny $ map (instancePredicate t) $ clsInstances cls
    
      -- Get the class constraints
      -- If an instance matched, then the class must match also
      cls_cst <- lift $ mapM (instantiatePredicate t) $ clsConstraint cls
      
      return (cls_cst, inst, inst_cst)
  where
    to_reduction_step Nothing = NotReduced
    to_reduction_step (Just (x, y, z)) = InstanceReduced x y z

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
         _ -> internalError "Not an instance predicate"

instancePredicates _ = internalError "Not an instance predicate"

-- | An action taken by splitConstraint
data SplitAction = Retain | Defer | Default | Ambiguous

-- | Partition a set of constraints into a retained set and a deferred set.
-- A constraint is retained if it mentions any variable in the given set of
-- \"bound\" variables.
--
-- TODO: Apply defaulting rules when the constraint is ambiguous
splitConstraint :: Constraint   -- ^ Constraint to partition
                -> TyVarSet     -- ^ Free variables
                -> TyVarSet     -- ^ Bound variables
                -> IO (Constraint, Constraint)
                   -- ^ Returns (retained constraints,
                   -- deferred constraints)
splitConstraint cst fvars qvars = do
  cst' <- reduceContext cst
  (retained, deferred, defaulted, ambiguous) <- partitionM isRetained cst'
  
  -- Need to default some constraints?
  if null defaulted
    then if null ambiguous 
         then return (retained, deferred)
         else fail "Ambiguous constraint"
    else do
    -- Apply defaulting rules, then retry
    new_csts <- mapM defaultConstraint defaulted
    splitConstraint (concat new_csts ++ cst') fvars qvars
  where
    isRetained prd = do
      fv <- freeTypeVariables prd
      
      -- If only variables from the environment are mentioned, then
      -- defer this predicate.  If only variables from the environment and
      -- local context are mentioned, then retain this predicate.
      -- Otherwise the predicate is ambiguous; try to resolve it by
      -- defaulting.
      case () of
        _ | fv `Set.isSubsetOf` fvars -> return Defer
          | fv `Set.isSubsetOf` Set.union fvars qvars -> return Retain
          | isDefaultable prd -> return Default
          | otherwise -> return Ambiguous
    
    -- Check if the dependent variable can be fixed using defaulting rules
    isDefaultable (IsInst head cls) =
      cls == tiBuiltin the_Traversable

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
       | cls == tiBuiltin the_Traversable -> do
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
       let con = SystemF.pyonBuiltin SystemF.the_repr_owned
           prf = mkPolyCallE pos (mkVarE pos con) [convertHMType ty] []
       return (True, [], prf)
       
     MagicDerivation {} -> do
       -- Create a magic proof value
       return (True, [], mkPolyCallE pos (mkConE noSourcePos $ SystemF.pyonBuiltin SystemF.the_fun_undefined) [convertPredicate $ conclusion derivation] [])
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
       return $ mkPolyCallE pos (mkConE pos con) premise_ts premise_vs
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
    let method_exp = mkConE pos (inmName method)
    in instanceExpressionWithProofs env pos ty_params constraint method_exp
