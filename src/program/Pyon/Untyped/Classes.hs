{- | Constraint manipulation is performed in this module.
-}

{-# LANGUAGE TypeFamilies #-}
module Pyon.Untyped.Classes
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

import Gluon.Common.Error
import Gluon.Common.MonadLogic
import Gluon.Common.SourcePos
import Gluon.Core(Level(..), Var(..))
import qualified Gluon.Core as Gluon
import Pyon.Untyped.HMType
import Pyon.Untyped.CallConv
import Pyon.Untyped.Kind
import Pyon.Untyped.GenSystemF
import Pyon.Untyped.Builtins
import qualified Pyon.SystemF.Syntax as SystemF
import qualified Pyon.SystemF.Builtins as SystemF
import Pyon.Untyped.Unification
import Pyon.Globals

pprList :: [Doc] -> Doc
pprList xs = brackets $ sep $ punctuate (text ",") xs

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

isInstancePredicate (IsInst _ _) = True
isInstancePredicate _ = False

isPassConvPredicate (HasPassConv _ _) = True
isPassConvPredicate _ = False

isEqualityPredicate (EqPassConv _ _) = True
isEqualityPredicate (EqExecMode _ _) = True
isEqualityPredicate _ = False

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
  -- True if the predicate or its reflection is in the context
  let p' = reflection p
      context = filter isEqualityPredicate ps
  in anyM (\q -> p `uEqual` q >||> p' `uEqual` q) context
  where
    reflection (EqPassConv x y) = EqPassConv y x
    reflection (EqExecMode x y) = EqExecMode y x
    reflection (IsInst _ _) =
      internalError "reflection: not an equality predicate"

-- | Add to the context any part of the predicate that is not already
-- entailed by the context.  Unification may be performed during entailment 
-- checking.  All inputs must be in head-normal form.
addPassConvToContext :: Constraint -> Predicate -> IO Constraint
addPassConvToContext context pred@(HasPassConv p_ty p_pc) =
  -- A 'HasPassConv' predicate is uniquely determined by its type.
  -- If another such predicate is in the context, then unify their
  -- parmeter-passing conventions and then return True.
  find_or_insert context
  where
    find_or_insert (HasPassConv c_ty c_pc : ps) = do
      -- Do the types match?
      match <- uEqual p_ty c_ty
      if not match then find_or_insert ps else unify_and_insert c_pc
 
    -- Ignore other constraints 
    find_or_insert (_ : ps) = find_or_insert ps

    -- No match found: add to context
    find_or_insert [] = return (pred:context)
    
    -- Found a match; unify with the new predicate
    unify_and_insert c_pc = do
      -- Unify the passing conventions.
      new_cst <- unify noSourcePos c_pc p_pc
      
      -- Insert the new constraints
      foldM addToContext context new_cst

-- | Determine whether a predicate is in head-normal form.
--
-- If the predicate's head is a variable, it is in head-normal form.
-- Otherwise, it is a type constructor and it should be possible to reduce it.
--
-- Resolution of a 'HasPassConv' predicate is determined based on its type, so
-- only the type need be HNF.
isHnf :: Predicate -> IO Bool
isHnf (IsInst t c) = canonicalizeHead t >>= checkTypeHead
  where
    checkTypeHead t =
      case t
      of ConTy c   -> return $ isTyVar c
         FunTy _   -> return False
         TupleTy _ -> return False
         AppTy t _ -> checkTypeHead t

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
     HasPassConv _ _ -> reduceHasPassConv pos pred
     EqPassConv _ _ -> reduceEquality pos pred
     EqExecMode _ _ -> reduceEquality pos pred

-- | Convert a constraint to HNF and ignore how it was derived
toHnfConstraint :: Predicate -> IO Constraint
toHnfConstraint p = liftM snd $ toHnf noSourcePos p

-------------------------------------------------------------------------------
-- Reduction rules for predicates

-- | Context reduction for an IsInst predicate
instanceReduction pos pred = do
    ip <- instancePredicates pred
    case ip of
      Nothing -> do
        -- Can't derive a class dictionary for this type
        prdDoc <- runPpr $ uShow pred
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

reduceHasPassConv pos pred@(HasPassConv ty pc) = do
  m_new_pc <- pickPassConv pos ty
  case m_new_pc of
    Nothing         -> return (IdDerivation pred, [pred])
    Just (pc', cst) -> return (MagicDerivation pred, cst)

-- | Reduce an equality predicate to a simplified form.
reduceEquality :: SourcePos -> Predicate -> IO (Derivation, Constraint)
reduceEquality pos pred =
  case pred
  of IsInst _ _ -> no_change pred
     EqPassConv c1 c2 -> structurallyP c1 c2
     EqExecMode c1 c2 -> structurallyM c1 c2
  where
    structurallyC c1 c2 =
      case (c1, c2)
      of (pc1 :+> cc1, pc2 :+> cc2) -> do
           (d1, new_csts1) <- structurallyP pc1 pc2
           (d2, new_csts2) <- structurallyC cc1 cc2
           return (EqCallConvDerivation (c1, c2), new_csts1 ++ new_csts2)
         (Return m1 pc1, Return m2 pc2) -> do
           (d1, new_csts1) <- structurallyM m1 m2
           (d2, new_csts2) <- structurallyP pc1 pc2
           return (EqCallConvDerivation (c1, c2), new_csts1 ++ new_csts2)
    
         -- Other constraints are inconsistent
         _ -> fail "Inconsistent constraint"

    structurallyP c1 c2 = do
      -- Reduce the head of each term as much as possible
      c1' <- reducePassConv c1
      c2' <- reducePassConv c2
      let pred' = EqPassConv c1' c2'

      -- Case analysis
      case (c1', c2') of
        -- Injective terms
        (ByVal, ByVal) -> tauto pred'
        (ByRef, ByRef) -> tauto pred'
        (ByClosure x1, ByClosure x2) -> do
          (d, new_csts) <- structurallyC x1 x2
          return (MagicDerivation pred', new_csts)

        (TuplePassConv t1, TuplePassConv t2) -> do
          results <- zipWithM structurallyP t1 t2
          let derivs = map fst results
              new_csts = concatMap snd results
          return (MagicDerivation pred', new_csts)
        
        -- Unifiable terms
        (By v1, By v2) -> do unifyPCVars v1 v2
                             tauto pred'
        (By v1, _) -> do unifyPCVar v1 c2'
                         tauto pred'
        (_, By v2) -> do unifyPCVar v2 c1'
                         tauto pred'

        -- Functions
        (TypePassConv t1, TypePassConv t2) -> do
          eq <- uEqual t1 t2
          if eq then tauto pred' else no_change pred'
        (TypePassConv _, _) -> no_change pred'
        (_, TypePassConv _) -> no_change pred'
        
        -- Other constraints are inconsistent
        _ -> fail "Inconsistent constraint"

    structurallyM m1 m2 = do
      m1' <- reduceExecMode m1
      m2' <- reduceExecMode m2
      let pred' = EqExecMode m1' m2'
      case (m1', m2') of
        -- Injective terms
        (AsAction, AsAction) -> tauto pred'
        (AsStream, AsStream) -> tauto pred'
            
        -- Functions
        (PickExecMode t1, PickExecMode t2) -> do
          -- If types are equal, eliminate this constraint
          eq <- uEqual t1 t2
          if eq then tauto pred' else no_change pred'
        (_, PickExecMode _) -> no_change pred'
        (PickExecMode _, _) -> no_change pred'
                        
        -- Other possibilities are inconsistent
        _ -> fail "inconsistent constraint"

    -- Equation can't be simplified further
    no_change pred' = return (IdDerivation pred', [pred'])

    -- Equation is a tautology
    tauto pred' = return (MagicDerivation pred', [])
    
    -- Derive an equality constraint, then swap LHS and RHS
    symmetryM pred' derive = do (d, new_cst) <- derive
                                return (MagicDerivation pred', new_cst)

-- | Simplify a parameter-passing convention as much as possible
reducePassConv :: PassConv -> IO PassConv
reducePassConv conv = canonicalizePassConv conv >>= reduce
  where
    -- Evaluate functions terms here
    reduce conv = 
      case conv
      of TuplePassConv xs -> do
           -- Reduce all subterms
           xs' <- mapM reducePassConv xs

           -- Try to simplify this term
           ifM (allM isByVal xs') (return ByVal) $
              ifM (allM isByValOrRef xs') (return ByRef) $
              return conv
         TypePassConv ty -> do
           new_conv <- pickPassConv noSourcePos ty
           return $ maybe conv fst new_conv
         
         -- Other terms can't be evaluated further
         _ -> return conv
    
    isByVal pc = do
      pc' <- canonicalizePassConv pc
      case pc' of ByVal -> return True
                  _     -> return False
    
    isByValOrRef pc = do
      pc' <- canonicalizePassConv pc
      case pc' of ByVal -> return True
                  ByRef -> return True
                  _     -> return False

-- | Simplify an execution mode as much as possible
reduceExecMode :: ExecMode -> IO ExecMode
reduceExecMode mode =
  case mode
  of AsAction -> return mode
     AsStream -> return mode
     PickExecMode ty -> do 
       mode' <- pickExecMode ty
       return $ fromMaybe mode mode'

-- | Determine the execution mode implied by a type, based on the
-- type constructor and arguments.  If the type is not known enough, return
-- a @PickExecMode@ value.
pickExecMode' :: HMType -> IO ExecMode
pickExecMode' ty = pickExecMode ty >>= ret
  where
    ret Nothing  = return $ PickExecMode ty
    ret (Just m) = return m

-- | Try to determine the execution mode implied by a type, based on the
-- type constructor and arguments.  If the type is not known enough, return
-- Nothing.  A @PickExecMode@ value will never be returned.
pickExecMode :: HMType -> IO (Maybe ExecMode)
pickExecMode ty = do
  (oper, args) <- inspectTypeApplication ty
  case oper of
    ConTy c
      | isTyVar c -> return Nothing
      | otherwise -> return $ Just $ tyConExecMode c
    FunTy _   -> return (Just AsAction)
    TupleTy _ -> return (Just AsAction)
    AppTy _ _ -> internalError "pickExecMode"

-- | Try to determine a type's parameter-passing convention.  Create a 
-- variable to represent an unknown convention.
pickPassConv' :: SourcePos -> HMType -> IO (PassConv, Constraint)
pickPassConv' pos ty = pickPassConv pos ty >>= ret
  where
    ret Nothing = do pc <- anyPassConv
                     return (pc, [ty `HasPassConv` pc])
    ret (Just (conv, cst)) = return (conv, cst)

-- | Try to determine a type's parameter-passing convention.
-- Return the convention and a constraint for the parameter-passing 
-- convention of for unknown types.
pickPassConv :: SourcePos -> HMType -> IO (Maybe (PassConv, Constraint))
pickPassConv pos ty = do 
  (oper, args) <- inspectTypeApplication ty
  case oper of
    ConTy c
      | isTyVar c -> return Nothing
      | otherwise -> let conv = applyPassConvCtor (tyConPassConv c) args
                     in return $ Just (conv, [])
    FunTy _ -> do
      (cc, cst) <- pickCallConv pos (init args) (last args)
      return $ Just (ByClosure cc, cst)
    TupleTy _ -> do
      conv_csts <- mapM (pickPassConv' pos) args
      let fields = map fst conv_csts
          new_csts = concatMap snd conv_csts
      cc <- reducePassConv (TuplePassConv fields)
      return $ Just (cc, new_csts)
      
    AppTy _ _ -> internalError "pickPassConv"

pickCallConv :: SourcePos -> [HMType] -> HMType -> IO (CallConv, Constraint)
pickCallConv pos domain range = do
  mode <- pickExecMode' range
  (conv, cst) <- pickPassConv' pos range
  foldM addParameter (Return mode conv, cst) $ reverse domain
  where
    addParameter (call_conv, cst) param_type = do
      (param_conv, new_cst) <- pickPassConv' pos param_type
      return (param_conv :+> call_conv, new_cst ++ cst)

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
  | isPassConvPredicate pred = addPassConvToContext ctx pred
  | isInstancePredicate pred = do
      b <- entailsInstancePredicate ctx pred
      if b then return ctx else return (pred:ctx)
  | isEqualityPredicate pred = do
      b <- entailsEqualityPredicate ctx pred
      if b then return ctx else return (pred:ctx)

-- | Try to satisfy a predicate with one of the known class instances.
-- If a match is found, return a list of subgoals generated for the class,
-- the matching instance, and a list of subgoals generated for the instance.
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
         _ -> internalError "Not an instance predicate"

instancePredicates _ = internalError "Not an instance predicate"

-- | An action taken by splitConstraint
data SplitAction = Retain | Defer | Default

-- | Partition a set of constraints into a retained set and a deferred set.
-- A constraint is retained if it mentions any variable in the given set of
-- \"bound\" variables.
--
-- TODO: Apply defaulting rules when the constraint is ambiguous
splitConstraint :: Constraint   -- ^ Constraint to partition
                -> TyVarSet     -- ^ Free variables
                -> TyVarSet     -- ^ Bound variables
                -> IO (Constraint, Constraint, Constraint) 
                   -- ^ Returns (retained constraints,
                   -- deferred constraints,
                   -- defaulted constraints)
splitConstraint cst fvars qvars = do
  cst' <- reduceContext cst
  partitionM isRetained cst'
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
          | otherwise ->
              ifM (isDefaultablePassConv prd) (return Default) $
              fail "Ambiguous constraint"
    
    -- A predicate of the form (a HasPassConv (Type a)) is defaultable 
    isDefaultablePassConv (HasPassConv ty conv) = do
      -- Check type
      ty' <- canonicalizeHead ty
      case ty' of
        ConTy c | isTyVar c -> do
          -- Check passing convention
          conv' <- canonicalizePassConv conv 
          case conv' of
            TypePassConv ty'' -> do
              -- Check that argument matches
              uEqual ty' ty''
            _ -> return False
        _ -> return False

    isDefaultablePassConv _ = return False

    partitionM f xs = go xs [] [] []
      where
        go (x:xs) lefts rights defaults = do
          b <- f x
          case b of
            Retain  -> go xs (x:lefts) rights defaults
            Defer   -> go xs lefts (x:rights) defaults
            Default -> go xs lefts rights (x:defaults)

        go [] lefts rights defaults =
          return (reverse lefts, reverse rights, reverse defaults)

-- | Perform defaulting on a constraint.  The constraint must have been
-- selected for defaulting by 'splitConstraint'.
defaultConstraint cst =
  case cst
  of HasPassConv ty conv -> do
       -- Default this type to 'Any'
       new_csts <- unify noSourcePos ty (ConTy $ tiBuiltin the_con_Any)
       unless (null new_csts) $
         internalError "Unexpected constraint produced by defualting"
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
           -- Create instance methods
           inst_methods <- instantiateClassMethods pos inst inst_type i_env
           
           -- Create dictionary expression
           let hmtype = convertHMType inst_type
               superclasses = map (mkVarE pos) c_vars
               dict = mkDictE pos cls hmtype superclasses inst_methods
           return (dict, [])

       return (True, placeholders, proof)
     _ -> do
       -- Create a magic proof value
       return (True, [], mkTyAppE pos (mkConE noSourcePos $ SystemF.pyonBuiltin SystemF.the_fun_undefined) (convertPredicate $ conclusion derivation))
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
