{-|
Definitions of parameter-passing conventions used in effect inference.

When complete, this module will replace the old 'EffectType' module.
-}

{-# LANGUAGE Rank2Types, FlexibleInstances, FlexibleContexts,
    GeneralizedNewtypeDeriving #-}
module Pyon.SystemF.NewFlatten.PassConv
       (EffectVar(evarID), EVar, RVar,
        assertEVar, assertRVar,
        isEVar, isRVar,
        newRegionVar, newEffectVar,
        effectVarName,
        
        Effect,
        fromEffect,
        emptyEffect, isEmptyEffect, varEffect, varsEffect, maybeVarEffect,
        effectUnion, effectUnions,
        deleteRegionFromEffect,
        deleteRegionsFromEffect,
        maybeDeleteRegionFromEffect,
        PassConv(..),
        FunParam(..),
        PassType(..),
        FunPassType(..),
        PolyPassType(..),
        PassTypeAssignment(..),
        fromMonoAss,
        
        -- * Pretty-printing
        pprEffectVar,
        pprEffect,
        pprFunParam,
        pprPassType,
        pprPolyPassType,
        pprPassConv,
        pprPredicate,
        pprConstraint,
        
        -- * Monads
        RegionMonad(..),
        assumeMaybeRegion,
        RegionM, runRegionM,
        EffInf, runEffInf, liftRegionM,
        assumePassType, lookupPassType,
        addConstraint, getConstraint,
        
        -- * Constructing values in the 'RegionM' monad
        funTDep, funTRgn, funFT, funT, retT,
        appT, streamT, varT, constT, typeT,
        polyPassType, monoPassType,
        
        -- * Constraints and evaluation
        passTypeMentionsTypeVar,
        funPassTypeMentionsTypeVar,
        solveGlobalConstraint,
        
        Parametric(..),
        expandAndRenameE,
        Subtype(..),
        
        -- * Effect polymorphism
        instantiatePassType,
        clearFlexibleEffectVariables,
        makeFlexibleVariablesIndependent,
        makeFlexibleVariablesIndependent'
        )
where

import Codec.Binary.UTF8.String
import Control.Exception(throwIO)
import Control.Monad
import Control.Monad.ST
import Control.Monad.Trans
import Control.Monad.Writer
import Data.Function
import Data.IORef
import Data.List
import Data.Maybe
import qualified Data.IntMap as IntMap
import qualified Data.Set as Set
import Debug.Trace
import Text.PrettyPrint.HughesPJ
  
import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.Label
import Gluon.Common.MonadLogic
import Gluon.Common.Supply
import Gluon.Core
import Gluon.Eval.Environment

import Pyon.Core.Syntax(PassConv(..))
  
-- | Set this to True to print a message every time a variable is assigned
debugAssignments :: Bool
debugAssignments = False

-- | Set this to True to print messages related to constraint solving
debugConstraints :: Bool
debugConstraints = False

-- | Effect variables may stand for either a single region or an arbitrary
-- set of regions.
data EffectVarKind = RegionEffectVar | EffectEffectVar
                   deriving(Eq)

-- | An effect or region variable.
--
-- Effect variables represent a set of regions.  Effect variables may be
-- assigned values and generalized over.  Region variables represent
-- exactly one region, and region variables are never unified.
data EffectVar =
  EffectVar
  { evarID :: {-# UNPACK #-} !(Ident EffectVar)
  , evarName :: !(Maybe Label)
  , evarKind :: !EffectVarKind
  , evarRep :: {-# UNPACK #-}!(IORef EffectVarRep)
  }
  
effectVarName v = evarName v

-- | An effect variable
type EVar = EffectVar

-- | A region variable
type RVar = EffectVar

instance Eq EffectVar where
  (==) = (==) `on` evarID
  (/=) = (/=) `on` evarID

instance Ord EffectVar where
  compare = compare `on` evarID
  
isEVar, isRVar :: EffectVar -> Bool
isEVar v = evarKind v == EffectEffectVar
isRVar v = evarKind v == RegionEffectVar

assertRVar :: EffectVar -> a -> a
assertRVar v x
  | isRVar v = x
  | otherwise = internalError "assertRVar: not a region variable"

assertEVar :: EffectVar -> a -> a
assertEVar v x
  | isEVar v = x
  | otherwise = internalError "assertEVar: not an effect variable"

data EffectVarRep =
    EVNoRep
  | EVVarRep !EffectVar
  | EVValueRep !Effect

-- | Put a representative in canonical form.
canonicalizeEffectVarRep :: IORef EffectVarRep -> IO EffectVarRep
canonicalizeEffectVarRep ref = do
  rep <- readIORef ref
  case rep of
    EVNoRep      -> return rep
    EVVarRep v   -> update_self rep =<< canonicalizeEffectVarRep (evarRep v)
    EVValueRep e -> return rep
  where
    update_self old_rep EVNoRep = return old_rep
    update_self _       new_rep = do writeIORef ref new_rep
                                     return new_rep

canonicalizeEffectVar :: EffectVar -> IO Effect
canonicalizeEffectVar ev
  | isRVar ev = return $ varEffect ev
  | otherwise = do 
      rep <- canonicalizeEffectVarRep (evarRep ev)
      case rep of EVNoRep      -> return $ varEffect ev
                  EVVarRep v   -> return $ varEffect v
                  EVValueRep e -> canonicalizeEffect e

-- | Assign an effect variable's representative.  The variable should not
-- have been assigned already.  The effect variable must not be mentioned
-- in the given effect.
assignEffectVar :: EffectVar -> Effect -> IO ()
assignEffectVar ev e = assertEVar ev $ do
  e' <- canonicalizeEffect e
  when (e' `effectMentions` ev) $
    internalError "assignEffectVar: Occurs check failed"

  -- DEBUG
  when debugAssignments $
    print $ pprEffectVar ev <+> text ":=" <+> pprEffect e

  rep <- readIORef (evarRep ev)
  case rep of
    EVNoRep -> writeIORef (evarRep ev) (EVValueRep e')
    _ -> internalError "assignEffectVar: Already assigned"

assignEffectVarD msg ev e 
  | debugAssignments = trace msg $ assignEffectVar ev e
  | otherwise = assignEffectVar ev e

makeNewEffectVar :: (Monad m, MonadIO m, Supplies m (Ident EffectVar))
                 => EffectVarKind -> Maybe Label -> m EffectVar
makeNewEffectVar k lab = do
  id <- fresh
  rep <- liftIO $ newIORef EVNoRep
  return $ EffectVar id lab k rep

newRegionVar :: (Monad m, MonadIO m, Supplies m (Ident EffectVar))
             => Maybe Label -> m EffectVar
newRegionVar lab = makeNewEffectVar RegionEffectVar lab

newEffectVar :: (Monad m, MonadIO m, Supplies m (Ident EffectVar))
             => Maybe Label -> m EffectVar
newEffectVar lab = makeNewEffectVar EffectEffectVar lab

-- | An effect is a set of regions and effect variables
newtype Effect = Effect {effectVars :: Set.Set EffectVar}

emptyEffect :: Effect
emptyEffect = Effect Set.empty

isEmptyEffect :: Effect -> Bool
isEmptyEffect (Effect s) = Set.null s

effectContainsEffectVariables :: Effect -> Bool
effectContainsEffectVariables (Effect e) =
  any ((EffectEffectVar ==) . evarKind) $ Set.toList e

varEffect :: EffectVar -> Effect
varEffect v = Effect (Set.singleton v)

maybeVarEffect :: Maybe EffectVar -> Effect
maybeVarEffect Nothing  = emptyEffect
maybeVarEffect (Just v) = varEffect v

varsEffect :: [EffectVar] -> Effect
varsEffect vs = Effect (Set.fromList vs)

effectUnion :: Effect -> Effect -> Effect
effectUnion (Effect e1) (Effect e2) = Effect (Set.union e1 e2)
                                      
effectUnions :: [Effect] -> Effect
effectUnions es = foldr effectUnion emptyEffect es

deleteRegionFromEffect :: RVar -> Effect -> Effect
deleteRegionFromEffect v (Effect e) = assertRVar v $ Effect (Set.delete v e)

deleteRegionsFromEffect :: [RVar] -> Effect -> Effect
deleteRegionsFromEffect vs e = foldr deleteRegionFromEffect e vs

maybeDeleteRegionFromEffect :: Maybe RVar -> Effect -> Effect
maybeDeleteRegionFromEffect Nothing  e = e
maybeDeleteRegionFromEffect (Just v) e = deleteRegionFromEffect v e

canonicalizeEffect :: Effect -> IO Effect
canonicalizeEffect (Effect es) =
  liftM effectUnions $ mapM canonicalizeEffectVar $ Set.toList es

fromEffect :: Effect -> IO [EffectVar]
fromEffect e = do
  e' <- canonicalizeEffect e
  return $ Set.toList $ effectVars e'

effectMentions :: Effect -> EffectVar -> Bool 
Effect vs `effectMentions` v = v `Set.member` vs

-- | Decompose an effect variable into two parts.
splitVariable :: EffectVar -> RegionM (EffectVar, EffectVar)
splitVariable v = assertEVar v $ do
  v1 <- newEffectVar (evarName v)
  v2 <- splitVariableOnSubset v1 v
  v_effect <- liftIO $ canonicalizeEffectVar v
  -- DEBUG
  liftIO $ print (pprEffectVar v <+> text "-->" <+> pprEffect v_effect)
  return (v1, v2)

-- | Decompose a flexible effect variable into two parts, one part being a
-- known variable and the other being a fresh variable.  The known variable
-- must be a subset of the effect variable.
splitVariableOnSubset :: EffectVar -- ^ Subset to separate out
                      -> EVar      -- ^ Flexible variable to split
                      -> RegionM EffectVar
splitVariableOnSubset subset_var v = assertEVar v $ do
  whenM (isRigid v) $ fail "splitVariableOnSubset: Variable is rigid"
    
  -- Create a new variable
  v' <- newEffectVar (evarName v)

  -- State the relationship between the new and old variables
  liftIO $ assignEffectVarD "splitVariable" v $ varsEffect [v', subset_var]
      
  return v'

splitVariablesOnSubset :: EffectVar -- ^ Subset to separate out
                       -> [EffectVar] -- ^ Variable to split
                       -> RegionM [EffectVar]
splitVariablesOnSubset subset_var vs = do
  mapM (splitVariableOnSubset subset_var) vs

-- | Type variables are Gluon variables.
type TVar = Var

-------------------------------------------------------------------------------

data FunParam =
  FunParam
  { paramRegion :: !(Maybe RVar)
  , paramTyVar  :: !(Maybe TVar)
  , paramType   :: !PassType
  }

-- | A type with parameter-passing convention information.
data PassType =
    -- | An application of a type constructor to operands.
    -- The return type's passing convention is given.
    AppT PassType [PassType]
    -- | A function type.
  | FunT !FunPassType
    -- | A lazy stream type
  | StreamT !Effect PassType
    -- | A type variable
  | VarT !Var
    -- | A type that doesn't contain variables
  | ConstT RExp
    -- | A kind.  Kinds are ignored by effect inference.  It only needs to
    -- keep track of where kinds are used as parameters.
  | TypeT

data FunPassType =
    FunFT {-# UNPACK #-}!FunParam FunPassType
  | RetFT !Effect PassType

{-
-- | A type extended with effect information.
data EType =
    AppT EType [EType]
  | StreamT !Effect EType
  | VarT Var                    -- ^ A type variable
  | ConstT RExp                 -- ^ A type that doesn't contain variables
  | TypeT                       -- ^ Any kind
-}

-- | An effect-polymorphic type scheme.
data PolyPassType = PolyPassType [EVar] PassType

-- | A way of assigning a parameter-passing type to a variable or expression.
data PassTypeAssignment =
    -- | A monomorphic parameter-passing type
    MonoAss PassType
    -- | A polymorphic parameter-passing type
  | PolyAss PolyPassType
    -- | A recursively defined function with unknown parameter-passing type.
    -- The function name is included as part of the type assignment.
    -- The function is assigned a monotype.  Effect inference will eventually
    -- assign a polymorphic type.
  | RecAss !Var PassType

fromMonoAss :: PassTypeAssignment -> PassType
fromMonoAss (MonoAss ty) = ty
fromMonoAss _ =
  internalError "fromMonoAss: Expecting a monomorphic effect type assignment"

{- We cannot determine a PassType's parameter-passing convention.
   Instead, we have to look at the type that it was originally derived from.

-- | Get the parameter-passing convention to use for this type
-- FIXME: use head of AppT/ConstT to determine convention
typePassConv :: PassType -> PassConv
typePassConv (AppT _ _) = Borrowed
typePassConv (FunT _) = Owned
typePassConv (StreamT _ _) = Owned
typePassConv (VarT _) = Borrowed
typePassConv (ConstT _) = Borrowed
typePassConv TypeT = ByValue
-}

-------------------------------------------------------------------------------
-- Constraints

-- $predicates
--
-- Predicates are stored in the form @v <: e@ for some region or effect
-- variable @v@ and effect @e@, where @e@ is a union of region and effect
-- variables.  Predicates with a more complicated expression @e1 U e2 <: e@
-- are first decomposed into multiple predicates.

data Predicate =
  -- | @a `SubEffect` b@ => Effect @a@ is smaller than effect @b@.
  SubEffect EffectVar Effect

-- | Create a subeffect constraint.
subEffect :: Effect -> Effect -> Constraint
subEffect (Effect evs) eff = [SubEffect ev eff | ev <- Set.toList evs]

-- | Determine whether a predicate mentions an effect variable.  The
-- predicate should be in head normal form.
predicateMentions :: Predicate -> EffectVar -> Bool
SubEffect lhs rhs `predicateMentions` v = lhs == v || rhs `effectMentions` v

-- | Expand variables that have been unified in a predicate.
expandPredicate :: Predicate -> IO Constraint
expandPredicate (SubEffect e1 e2) =
  liftM2 subEffect (canonicalizeEffectVar e1) (canonicalizeEffect e2)

type Constraint = [Predicate]

-- | Determine whether a constraint mentions an effect variable.  The
-- constraint should be in head normal form.
constraintMentions :: Constraint -> EffectVar -> Bool
cst `constraintMentions` v = any (`predicateMentions` v) cst

-- | Expand variables that have been unified in a predicate.
expandConstraint :: Constraint -> IO Constraint
expandConstraint cst = liftM concat $ mapM expandPredicate cst

-- | Attempt to simplify the predicate to an equivalent constraint;
-- throw an exception if the predicate is unsatisfiable for some choice of
-- rigid variables.  In addition to
-- the constraint, a @True@ value is returned if any unification was performed.
--
-- After simplification, predicates will always have a flexible variable on
-- the LHS and at least one variable on the RHS.
simplifyPredicate :: Predicate -> RegionM (Constraint, Bool)
simplifyPredicate predicate@(SubEffect lhs_var rhs) = do
  ctx <- getRigidEffectVars
  
  case ()
    of _ | rhs `effectMentions` lhs_var ->
             -- This equation is a tautology
             return ([], False)

         | lhs_var `Set.member` ctx -> do
             -- The LHS is rigid.  Eliminate this equation.
             let rhs_vars = Set.toList $ effectVars rhs

             -- Rigid variables are always disjoint, so they can be eliminated 
             -- from the RHS
             let flexible_rhs_vars = filter is_flexible rhs_vars
                   where
                     is_flexible v = isEVar v && not (v `Set.member` ctx)

             -- Split flexible variables
             _ <- splitVariablesOnSubset lhs_var flexible_rhs_vars
             return ([], True)

         | isRVar lhs_var ->
             -- Region variables must be part of the context
             internalError "simplifyPredicate"

         | Set.null (effectVars rhs) -> do
             -- If the RHS is empty, the LHS must be the empty set
             liftIO $ assignEffectVarD "simplifyPredicate" lhs_var emptyEffect
             return ([], True)

         | otherwise -> return ([predicate], False)

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
      prd_cst <- liftIO $ expandPredicate prd
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

-- | Solve a constraint where every LHS is a flexible variable.
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
      when (or [v `Set.member` ctx || isRVar v | v <- lhs_vars]) $
        internalError "solveGlobalConstraint: Found rigid variables in LHS"
      
      -- Clear all flexible variables
      forM_ lhs_vars $ \v -> assignEffectVarD "solveGlobal" v emptyEffect

-- | Eliminate a rigid region or effect variable from all constraints by 
-- splitting flexible variables.  The constraint must be in head normal form.
--
-- This function relies on the variable appearing only on the right-hand-side
-- of constraints (which reduceConstraint does).
-- First, we split flexible variables that are part of an upper bound on 
-- @v@.
-- This transformation works like 'eliminatePredicate', except that it
-- eliminates all relevant predicates in one step.
eliminateRigidVariable :: EffectVar -- ^ Variable to eliminate
                       -> Constraint
                       -> RegionM Constraint
eliminateRigidVariable v cst = do
  unlessM (isRigid v) $ internalError "eliminateRigidVariable"

  -- Verify that the variable only appears on the RHS of constraints.
  -- This should always be true if 'reduceConstraint' is called first.
  when False $ when (or [lhs == v | SubEffect lhs _ <- cst]) $
    internalError "eliminateRigidVariable"
    
  -- Remove the variable from all RHSes.
  return $ map (remove v) cst
  where
    remove v (SubEffect lhs rhs) =
      SubEffect lhs (Effect $ Set.delete v $ effectVars rhs)

-- | Shorthand for calling 'reduceConstraint' and 'eliminateRigidVariable'.
reduceAndEliminateRigidVariable :: EffectVar -- ^ Variable to eliminate
                                -> Constraint
                                -> RegionM Constraint
reduceAndEliminateRigidVariable v cst =
  eliminateRigidVariable v =<< reduceConstraint cst

-- | Eliminate a predicate where the lower bound is a flexible variable.
-- The predicate must be in head normal form.  The variables created during
-- elimination are returned.
--
-- Each flexible variable on the RHS of the constraint is split into two
-- parts, one which is part of the constraint and one which is independent.
-- Unification is performed in the process.
--
-- That is, we eliminate a subset relation of the form
--
-- > e1 <: e2 U e3 U r1
--
-- by generating new variables for each flexible variable on the RHS:
--
-- > e1 = e2a U e3a U r1
-- > e2 = e2a U e2b
-- > e3 = e3a U e3b
eliminatePredicate :: Predicate -> RegionM [EffectVar]
eliminatePredicate (SubEffect v vs) = do
  ctx <- getRigidEffectVars
  
  when (v `Set.member` ctx) $ internalError "eliminatePredicate: LHS is rigid"
  when (isRVar v) $ internalError "eliminatePredicate: LHS is a region variable"
  
  -- Find the flexible variables on the RHS
  let rigid_vs = Set.intersection (effectVars vs) ctx
      flexible_vs = effectVars vs Set.\\ rigid_vs

  -- Split the flexible variables into two parts
  (dependent_flexible_vs, independent_flexible_vs) <-
    mapAndUnzipM splitVariable $ Set.toList flexible_vs

  -- Assign the lower-bound variable
  let v_effect = varsEffect $ dependent_flexible_vs ++ Set.toList rigid_vs
  liftIO $ assignEffectVarD "eliminatePredicate" v v_effect
  
  return (dependent_flexible_vs ++ independent_flexible_vs)

-- | Find the predicates that mention @v@.  Return a list of predicates 
-- whose LHS is @v@, a list of predicates whose RHS contains @v@, and 
-- in the LHS, RHS, and 
findPredicatesMentioning :: EffectVar
                         -> Constraint
                         -> (Constraint, Constraint, Constraint)
findPredicatesMentioning v cst = go id id id cst
  where
    -- Partition the constraint into three parts
    go lhs rhs none (prd@(SubEffect prd_lhs prd_rhs):cst)
      | prd_lhs == v = go (lhs . (prd:)) rhs none cst
      | prd_rhs `effectMentions` v = go lhs (rhs . (prd:)) none cst
      | otherwise = go lhs rhs (none . (prd:)) cst
                    
    go lhs rhs none [] = (lhs [], rhs [], none [])

-------------------------------------------------------------------------------
-- Pretty-printing

angles :: Doc -> Doc
angles d = text "<" <> d <> text ">"

pprEffectVar :: EffectVar -> Doc
pprEffectVar v = 
  let l = case evarKind v
          of RegionEffectVar -> 'r'
             EffectEffectVar -> 'e'
  in text (l : show (fromIdent $ evarID v))

unionDoc = text $ encodeString [toEnum 0x222a]
emptySetDoc = text $ encodeString [toEnum 0x2205]

pprEffect :: Effect -> Doc
pprEffect eff =
  let (rvars, evars) = partition isRVar $ Set.toList $ effectVars eff
      region_doc = if null rvars
                   then Nothing
                   else Just $ braces $ fsep $ punctuate comma $
                        map pprEffectVar rvars
  in if null rvars && null evars 
     then emptySetDoc
     else fsep $ intersperse unionDoc $
          maybeToList region_doc ++ map pprEffectVar evars

pprFunParam :: FunParam -> Doc
pprFunParam (FunParam rgn ty dom) =
  let dom_doc = pprPassTypeInParens dom
      lvar_doc = case ty
                 of Nothing ->
                      case rgn
                      of Nothing -> empty
                         Just rv -> text "_@" <> pprEffectVar rv
                    Just tv ->
                      case rgn
                      of Nothing -> pprVar tv
                         Just rv -> pprVar tv <> text "@" <> pprEffectVar rv
  in if isEmpty lvar_doc
     then dom_doc
     else lvar_doc <+> text ":" <+> dom_doc
pprPassTypeInParens :: PassType -> Doc
pprPassTypeInParens pt@(VarT _) = pprPassType pt
pprPassTypeInParens pt = parens $ pprPassType pt

pprPassType :: PassType -> Doc
pprPassType pt =
  case pt
  of AppT ty tys   -> pprPassType ty <+>
                      sep (map pprPassType tys)
     FunT fty      -> pprFunPassType fty
     StreamT eff t -> text "stream" <+> sep [ parens (pprEffect eff)
                                             , pprPassType t]
     VarT v        -> pprVar v
     ConstT t      -> parens (pprExp t)
     TypeT         -> text "any_type"

pprFunPassType fty =
  let clauses = ppr fty
      arrow_clauses = [c <+> text "->" | c <- init clauses] ++ [last clauses]
  in sep arrow_clauses
  where
    ppr (FunFT param ty) = pprFunParam param : ppr ty
    ppr (RetFT eff ty) = [angles (pprEffect eff) <+> pprPassType ty] 

pprPolyPassType :: PolyPassType -> Doc
pprPolyPassType (PolyPassType evars pt) =
  hang (text "forall" <+> sep (map pprEffectVar evars) <> text ".") 4 $
  pprPassType pt

{-pprEType :: EType -> Doc
pprEType pt =
  case pt
  of AppT op args   -> pprEType op <+> sep (map pprEType args)
     StreamT eff ty -> text "stream" <+> sep [ parens (pprEffect eff)
                                             , pprEType ty]
     VarT v         -> pprVar v
     ConstT e       -> parens $ pprExp e
     TypeT          -> text "any_type"-}

pprPassConv :: PassConv -> Doc
pprPassConv ByValue  = text "val"
pprPassConv Owned    = text "own"
pprPassConv Borrowed = text "bor"

pprPredicate :: Predicate -> Doc
pprPredicate (SubEffect v e) = pprEffectVar v <+> text "<:" <+> pprEffect e 

pprConstraint :: Constraint -> Doc
pprConstraint cst = vcat $ map pprPredicate cst

-------------------------------------------------------------------------------
-- Monads

-- | A monad that allows new region variables and type variables to be  
-- created, that keeps track of bound region variables, and that allows
-- effect variable unification.
class (Monad m, MonadIO m,
       Supplies m (Ident Var), Supplies m (Ident EffectVar)) =>
      RegionMonad m where
  assumeRegion :: RVar -> m a -> m a
  assumeEffect :: EVar -> m a -> m a
  
  -- | Find out what region and effect variables are rigid here
  getRigidEffectVars :: m (Set.Set EffectVar)
  
  liftPureTC :: PureTC a -> m a

assumeMaybeRegion :: RegionMonad m => Maybe RVar -> m a -> m a
assumeMaybeRegion Nothing m = m
assumeMaybeRegion (Just rgn) m = assumeRegion rgn m

withRigidEffectVars :: (Set.Set EffectVar -> IO a) -> RegionM a
withRigidEffectVars f = do
  ctx <- getRigidEffectVars
  liftIO $ f ctx

-- | Determine whether a variable is rigid in the current context.
isRigid :: RegionMonad m => EffectVar -> m Bool
isRigid v = liftM (v `Set.member`) $ getRigidEffectVars

-- | Computations performed in a region environment.
--
-- The monad can supply region and variable IDs.  It keeps track of which
-- regions are in scope.
newtype RegionM a =
  RegionM {doRegionM :: RegionEnv -> IO a}

runRegionM :: IdentSupply EffectVar -> IdentSupply Var -> RegionM a -> IO a
runRegionM evar_supply var_supply m = do
  let env = RegionEnv evar_supply var_supply Set.empty
  doRegionM m env

data RegionEnv =
  RegionEnv
  { reRegionIDs :: !(IdentSupply EffectVar)
  , reVarIDs :: !(IdentSupply Var)
  , reRegionEnv :: Set.Set EffectVar
  }

instance Monad RegionM where
  return x = RegionM (\_ -> return x)
  m >>= k = RegionM (\env -> do x <- doRegionM m env
                                doRegionM (k x) env)

instance MonadIO RegionM where
  liftIO m = RegionM (\_ -> m)

instance EvalMonad RegionM where
  liftEvaluation m = RegionM $ \env -> do
    result <- runEvalIO (reVarIDs env) m
    case result of
      Nothing -> internalError "Unexpected evaluation error in effect inference"
      Just x -> return x

instance Supplies RegionM (Ident EffectVar) where
  fresh = RegionM $ \env -> supplyValue $ reRegionIDs env
  supplyToST f = RegionM $ \env -> let new = unsafeIOToST $
                                             supplyValue $ reRegionIDs env
                                   in stToIO (f new)

instance Supplies RegionM (Ident Var) where
  fresh = RegionM $ \env -> supplyValue $ reVarIDs env
  supplyToST f = RegionM $ \env -> let new = unsafeIOToST $
                                             supplyValue $ reVarIDs env
                                   in stToIO (f new)

localRegionEnv :: (RegionEnv -> RegionEnv) -> RegionM a -> RegionM a
localRegionEnv f m = RegionM (\env -> doRegionM m (f env))

assumeEffectVariableRegionM :: EffectVar -> RegionM a -> RegionM a
assumeEffectVariableRegionM ev = localRegionEnv add_to_env
  where
    add_to_env env = env {reRegionEnv = Set.insert ev $ reRegionEnv env}

instance RegionMonad RegionM where
  assumeRegion v m = assertRVar v $ assumeEffectVariableRegionM v m
  assumeEffect v m = assertEVar v $ assumeEffectVariableRegionM v m
  
  getRigidEffectVars = RegionM (\env -> return (reRegionEnv env))

  liftPureTC m = RegionM $ \env -> do
    result <- runPureTCIO (reVarIDs env) m
    case result of
      Left errs -> fail "Unhandled type errors in effect inference"
      Right x -> return x

-- | The monad used for effect inference.  This monad extends RegionM with 
-- constraints and an effect type environment.
newtype EffInf a =
  EffInf {doEffInf :: EffectEnv -> IO (a, Constraint -> Constraint)}

data EffectEnv =
  EffectEnv
  { efRegionEnv :: {-# UNPACK #-}!RegionEnv
    
    -- | The region inhabited by a variable (if any) and its parameter-passing
    -- convention
  , efEnv :: IntMap.IntMap (PassTypeAssignment, Maybe RVar)
  }

runEffInf :: IdentSupply EffectVar -> IdentSupply Var -> EffInf a -> IO a
runEffInf evar_ids var_ids m = do
  let env = EffectEnv (RegionEnv evar_ids var_ids Set.empty) IntMap.empty
  (x, _) <- doEffInf m env
  return x

effInfReturn :: a -> IO (a, Constraint -> Constraint)
effInfReturn x = return (x, id)

liftRegionM :: RegionM a -> EffInf a
liftRegionM m = EffInf $ \env -> do x <- doRegionM m (efRegionEnv env)
                                    effInfReturn x 

instance Monad EffInf where
  return x = EffInf (\_ -> effInfReturn x) 
  m >>= k = EffInf $ \env -> do
    (x, c1) <- doEffInf m env
    (y, c2) <- doEffInf (k x) env
    return (y, c1 . c2)

instance MonadIO EffInf where
  liftIO m = EffInf (\_ -> m >>= effInfReturn)

instance Supplies EffInf (Ident Var) where
  fresh = EffInf $ \env ->
    supplyValue (reVarIDs $ efRegionEnv env) >>= effInfReturn
  supplyToST f = EffInf $ \env ->
    let get_fresh = supplyValue $ reVarIDs $ efRegionEnv env
    in effInfReturn =<< stToIO (f (unsafeIOToST get_fresh))

instance Supplies EffInf (Ident EffectVar) where
  fresh = EffInf $ \env ->
    supplyValue (reRegionIDs $ efRegionEnv env) >>= effInfReturn

instance EvalMonad EffInf where
  liftEvaluation m = EffInf $ \env -> do
    mx <- runEvalIO (reVarIDs $ efRegionEnv env) m
    case mx of Just x -> effInfReturn x
               Nothing -> internalError "EffInf: evaluation failed"

localEffInf :: (EffectEnv -> EffectEnv) -> EffInf a -> EffInf a
localEffInf f m = EffInf (\env -> doEffInf m (f env))

-- | Run a computation and transform the constraint that it produces
transformConstraint :: (Constraint -> RegionM Constraint)
                    -> EffInf a -> EffInf a
transformConstraint f m = EffInf $ \env -> do
  (x, cst) <- doEffInf m env
  cst' <- doRegionM (f (cst [])) (efRegionEnv env)
  return (x, (cst' ++))

assumeEffectVariableEffInf :: EffectVar -> EffInf a -> EffInf a
assumeEffectVariableEffInf ev = localEffInf add_to_env
  where
    add_to_env env =
      let region_env = Set.insert ev $ reRegionEnv $ efRegionEnv env
      in env {efRegionEnv = (efRegionEnv env) {reRegionEnv = region_env}}
  
instance RegionMonad EffInf where
  assumeRegion rv m =
    -- Add the region to the context.  After running the computation 'm',
    -- eliminate all constraints involving this variable.
    assertRVar rv $
    assumeEffectVariableEffInf rv $ 
    transformConstraint (reduceAndEliminateRigidVariable rv) m

  assumeEffect ev m =
    -- Add the effect to the context.  After running the computation 'm',
    -- eliminate all constraints involving this variable.
    assertEVar ev $
    assumeEffectVariableEffInf ev $
    transformConstraint (reduceAndEliminateRigidVariable ev) m    

  getRigidEffectVars = EffInf $ \env ->
    effInfReturn (reRegionEnv $ efRegionEnv env)

assumePassType :: Var -> PassTypeAssignment -> Maybe RVar -> EffInf a
               -> EffInf a
assumePassType v pt rgn m =
  assumeMaybeRegion rgn $ localEffInf add_to_env m
  where
    add_to_env env =
      let region_env =
            IntMap.insert (fromIdent $ varID v) (pt, rgn) $ efEnv env
      in env {efEnv = region_env}

lookupPassType :: Var -> EffInf (PassTypeAssignment, Maybe RVar)
lookupPassType v = EffInf $ \env -> effInfReturn $! lookup_var v (efEnv env)
  where
    lookup_var v m =
      case IntMap.lookup (fromIdent $ varID v) m
      of Nothing -> internalError $ "lookupPassType: No information for variable " ++ show v
         Just x  -> x

addConstraint :: Constraint -> EffInf ()
addConstraint cst = debug $ EffInf (\env -> return ((), (cst ++)))
  where
    debug x
      | debugConstraints =
          traceShow (text "addConstraint" <+> pprConstraint cst) x
      | otherwise = x

getConstraint :: EffInf a -> EffInf (a, Constraint)
getConstraint m = EffInf $ \env -> do
  (x, cst) <- doEffInf m env
  effInfReturn (x, cst [])

{-atomT :: PassConv -> RegionM EType -> RegionM PassType
atomT pc mk_ty = AtomT pc `liftM` mk_ty-}

-- | Create a function type that takes a type parameter
funTDep :: RegionM PassType
        -> (TVar -> RegionM FunPassType) 
        -> RegionM FunPassType
funTDep mk_dom mk_rng = do
  tv <- newVar Nothing TypeLevel
  dom <- mk_dom
  rng <- mk_rng tv
  return $ FunFT (FunParam Nothing (Just tv) dom) rng

-- | Create a function type that has a parameter region
funTRgn :: RegionM PassType
        -> (RVar -> RegionM FunPassType)
        -> RegionM FunPassType
funTRgn mk_dom mk_rng = do
  rv <- newRegionVar Nothing
  dom <- mk_dom
  rng <- mk_rng rv
  return $ FunFT (FunParam (Just rv) Nothing dom) rng

-- | Create a function type that has no parameter region
funT :: RegionM FunPassType -> RegionM PassType 
funT m = liftM FunT m

funFT :: RegionM PassType -> RegionM FunPassType -> RegionM FunPassType
funFT mk_dom mk_rng = do
  dom <- mk_dom
  rng <- mk_rng
  return $ FunFT (FunParam Nothing Nothing dom) rng

retT :: Effect -> RegionM PassType -> RegionM FunPassType
retT eff mk_ty = liftM (RetFT eff) mk_ty

appT :: RegionM PassType -> [RegionM PassType] -> RegionM PassType
appT mk_op mk_args = liftM2 AppT mk_op (sequence mk_args)

streamT :: Effect -> RegionM PassType -> RegionM PassType
streamT eff mk_ty = liftM (StreamT eff) mk_ty

-- | Create an effect inference type corresponding to a type variable.
-- All such types are passed using the 'Borrowed' convention.
varT :: Var -> RegionM PassType
varT v = return $ VarT v

constT :: RExp -> RegionM PassType
constT e = return $ ConstT e

typeT :: RegionM PassType
typeT = return TypeT

polyPassType :: Int -> ([EVar] -> RegionM PassType) -> RegionM PolyPassType
polyPassType n mk_ty = do
  vars <- replicateM n $ newEffectVar Nothing
  liftM (PolyPassType vars) (mk_ty vars)

monoPassType :: RegionM PassType -> RegionM PolyPassType
monoPassType = liftM (PolyPassType [])

-------------------------------------------------------------------------------
-- Renaming and traversal

passTypeMentionsTypeVar :: PassType -> Var -> Bool
pt `passTypeMentionsTypeVar` v =
  case pt
  of AppT op args   -> op `passTypeMentionsTypeVar` v ||
                       any (`passTypeMentionsTypeVar` v) args
     FunT t         -> t `funPassTypeMentionsTypeVar` v
     StreamT _ ty   -> ty `passTypeMentionsTypeVar` v
     VarT tyvar     -> tyvar == v
     ConstT _       -> False
     TypeT          -> False

pt `funPassTypeMentionsTypeVar` v =
  case pt
  of FunFT param range -> paramType param `passTypeMentionsTypeVar` v ||
                          range `funPassTypeMentionsTypeVar` v
     RetFT _ range -> range `passTypeMentionsTypeVar` v 
{-
eTypeMentionsTypeVar :: EType -> Var -> Bool
et `eTypeMentionsTypeVar` v =
  case et
  of AppT op args -> any (`eTypeMentionsTypeVar` v) (op:args)
     StreamT _ ty -> ty `eTypeMentionsTypeVar` v
     VarT ty_var  -> ty_var == v
     ConstT _     -> False
     TypeT        -> False-}

class Parametric exp where
  -- | Get the set of free effect variables mentioned in positive and negative
  -- positions, respectively.  A variable amy appear in both positions.
  freeEffectVars :: exp -> IO (Set.Set EffectVar, Set.Set EffectVar)
  
  -- | Expand variables that have been assigned a value
  expand :: exp -> IO exp
  
  renameT :: TVar -> TVar -> exp -> exp
  
  -- | Rename an effect variable.  The old and new variables must not have
  -- been assigned values.  The argument should be expanded before renaming.
  --
  -- Note that the caller of 'renameE' should expand its expression argument.  
  -- When renameE calls itself recursively, it's not necessary to expand the
  -- argument again.
  renameE :: EffectVar -> EffectVar -> exp -> exp
  assignT :: TVar -> PassType -> exp -> exp
  assignE :: EffectVar -> Effect -> exp -> exp
  
  -- | True if the value mentions the given effect variable;
  -- variable assignments are expanded first
  mentionsE :: exp -> EffectVar -> IO Bool
  
  -- | True if the value mentions any of the given effect variables;
  -- variable assignments are expanded first
  mentionsAnyE :: exp -> Set.Set EffectVar -> IO Bool

expandAndRenameE :: Parametric exp => EffectVar -> EffectVar -> exp -> IO exp
expandAndRenameE old_v new_v e = liftM (renameE old_v new_v) $ expand e

emptyFreeVars :: (Set.Set EffectVar, Set.Set EffectVar)
emptyFreeVars = (Set.empty, Set.empty)

contravariant, invariant :: (Set.Set EffectVar, Set.Set EffectVar)
                         -> (Set.Set EffectVar, Set.Set EffectVar)
contravariant (a, b) = (b, a)
invariant (a, b) = let u = Set.union a b in (u, u)

pairUnion :: (Set.Set EffectVar, Set.Set EffectVar)
          -> (Set.Set EffectVar, Set.Set EffectVar)
          -> (Set.Set EffectVar, Set.Set EffectVar)
pairUnion (a, b) (c, d) = (Set.union a c, Set.union b d)

pairUnions :: [(Set.Set EffectVar, Set.Set EffectVar)]
           -> (Set.Set EffectVar, Set.Set EffectVar)
pairUnions = foldr pairUnion emptyFreeVars

instance Parametric () where
  freeEffectVars () = return emptyFreeVars
  expand () = return ()
  renameT _ _ () = ()
  renameE _ _ () = ()
  assignT _ _ () = ()
  assignE _ _ () = ()
  mentionsE () _ = return False
  mentionsAnyE () _ = return False

mapParametricPair :: (Parametric a, Parametric b) =>
                     (forall c. Parametric c => c -> c)
                  -> (a, b) -> (a, b)
mapParametricPair f (x, y) = (f x, f y)

instance (Parametric a, Parametric b) => Parametric (a, b) where
  freeEffectVars (x, y) = do
    (x1, x2) <- freeEffectVars x
    (y1, y2) <- freeEffectVars y
    return (x1 `Set.union` x2, y1 `Set.union` y2)
  expand (x, y) = liftM2 (,) (expand x) (expand y)
  renameT old_v new_v = mapParametricPair (renameT old_v new_v)
  renameE old_v new_v = mapParametricPair (renameE old_v new_v)
  assignT old_v new_e = mapParametricPair (assignT old_v new_e)
  assignE old_v new_e = mapParametricPair (assignE old_v new_e)
  (x, y) `mentionsE` v = x `mentionsE` v >||> y `mentionsE` v
  (x, y) `mentionsAnyE` vs = x `mentionsAnyE` vs >||> y `mentionsAnyE` vs
  
-- | Rename two region variables to have the same name and add the region to
-- the environment over the scope of @k@.
--
-- The argument computation's first return value is something that must not
-- mention the region parameter.  If it mentions the region parameter, an
-- error is thrown.
withSameRegionParam :: Parametric exp =>
                       (Maybe RVar, exp) 
                    -> (Maybe RVar, exp)
                    -> (Maybe RVar -> exp -> exp -> EffInf a)
                    -> EffInf a
withSameRegionParam (Nothing, e1) (Nothing, e2) k = k Nothing e1 e2

withSameRegionParam (mv1, e1) (mv2, e2) k = do
  -- Create a new local region name
  rv <- newRegionVar ((evarName =<< mv1) `mplus` (evarName =<< mv2))
  
  let rename Nothing e      = return e
      rename (Just old_v) e = expandAndRenameE old_v rv e
  e1' <- liftIO $ rename mv1 e1
  e2' <- liftIO $ rename mv2 e2

  -- Add the local region to the environment
  assumeRegion rv $ do
    -- Run the computation; eliminate constraints that mention the local region
    k (Just rv) e1' e2'

-- | Rename two effect variables to have the same name and add the variable to
-- the environment over the scope of @k@.
withSameEffectParam :: Parametric exp =>
                       (EVar, exp)
                    -> (EVar, exp)
                    -> (EVar -> exp -> exp -> EffInf a)
                    -> EffInf a
withSameEffectParam (v1, e1) (v2, e2) k = assertEVar v1 $ assertEVar v2 $ do
  -- Create a new variable name
  v <- newEffectVar (evarName v1 `mplus` evarName v2)
  e1' <- liftIO $ expandAndRenameE v1 v e1
  e2' <- liftIO $ expandAndRenameE v1 v e2
  assumeEffect v $ k v e1' e2'

-- | Rename two type variables to have the same name.
withSameTypeParam :: Parametric exp =>
                     (Maybe TVar, exp)
                  -> (Maybe TVar, exp)
                  -> (Maybe TVar -> exp -> exp -> EffInf a)
                  -> EffInf a
withSameTypeParam (Nothing, e1) (Nothing, e2) k = k Nothing e1 e2

withSameTypeParam (v1, e1) (v2, e2) k = do
  -- At least one of the parameters has a level
  let level = fromJust $ fmap getLevel v1 `mplus` fmap getLevel v2
  v <- newVar ((varName =<< v1) `mplus` (varName =<< v2)) level
  
  let rename Nothing e      = e
      rename (Just old_v) e = renameT old_v v e

  k (Just v) (rename v1 e1) (rename v2 e2)

-- | Rename the region and type variables bound by the 'FunParam's
-- to have the same names.  The parameters should have compatible types.
-- The second parameter's type is used to construct
-- the renamed parameter.
withSameFunParam :: (FunParam, FunPassType)
                 -> (FunParam, FunPassType)
                 -> (FunParam -> FunPassType -> FunPassType -> EffInf a)
                 -> EffInf a
withSameFunParam (p1, t1) (p2, t2) k =
  withSameRegionParam (paramRegion p1, t1) (paramRegion p2, t2) $ \r t1' t2' ->
  withSameTypeParam (paramTyVar p1, t1') (paramTyVar p2, t2') $ \t t1'' t2'' ->
  let p' = FunParam r t (paramType p2)
  in k p' t1'' t2''

{-
mapParametricEType :: (forall a. Parametric a => a -> a) -> EType -> EType
mapParametricEType f expression =
  case expression
  of AppT op args   -> AppT (f op) (map f args)
     StreamT eff ty -> StreamT (f eff) (f ty)
     VarT v         -> expression
     ConstT c       -> expression
     TypeT          -> TypeT

instance Parametric EType where
  freeEffectVars ty =
    case ty
    of AppT op args ->
         liftM (invariant . pairUnions) $ mapM freeEffectVars (op : args)
       StreamT eff ty2 -> do
         eff_vars <- freeEffectVars eff
         ty2_vars <- freeEffectVars ty2
         return $ pairUnion eff_vars ty2_vars
       VarT _ -> return emptyFreeVars
       ConstT _ -> return emptyFreeVars
       TypeT -> return emptyFreeVars

  expand expression = 
    case expression
    of AppT op args   -> AppT `liftM` expand op `ap` mapM expand args
       StreamT eff ty -> StreamT `liftM` expand eff `ap` expand ty
       VarT v         -> return expression
       ConstT c       -> return expression
       TypeT          -> return expression

  renameT old_v new_v expression =
    case expression
    of VarT v | v == old_v -> VarT new_v 
       _ -> mapParametricEType (renameT old_v new_v) expression

  renameE old_v new_v expression =
    mapParametricEType (renameE old_v new_v) expression

  assignT old_v val expression =
    case expression
    of VarT v | v == old_v -> val
       _ -> mapParametricEType (assignT old_v val) expression

  assignE old_v val expression =
    mapParametricEType (assignE old_v val) expression
    
  expression `mentionsE` v =
    case expression
    of AppT op args   -> op `mentionsE` v >||> anyM (`mentionsE` v) args
       StreamT eff ty -> eff `mentionsE` v >||> ty `mentionsE` v
       VarT v         -> return False
       ConstT c       -> return False
       TypeT          -> return False

  expression `mentionsAnyE` vs =
    case expression
    of AppT op args   -> op `mentionsAnyE` vs >||> anyM (`mentionsAnyE` vs) args
       StreamT eff ty -> eff `mentionsAnyE` vs >||> ty `mentionsAnyE` vs
       VarT v         -> return False
       ConstT c       -> return False
       TypeT          -> return False
-}

mapParametricPassType :: (forall a. Parametric a => a -> a)
                      -> PassType -> PassType
mapParametricPassType f expression =
  case expression
  of AppT ty args   -> AppT (f ty) (map f args)
     FunT ft        -> FunT $ mapParametricFunType f ft
     StreamT eff ty -> StreamT (f eff) (f ty)
     VarT _         -> expression
     ConstT _       -> expression
     TypeT          -> expression

mapParametricFunType :: (forall a. Parametric a => a -> a)
                      -> FunPassType -> FunPassType
mapParametricFunType f expression =
  case expression
  of FunFT param ty   -> let param' = param {paramType = f $ paramType param}
                        in FunFT param' (f ty)
     RetFT eff ty     -> RetFT (f eff) (f ty)

instance Parametric PassType where
  freeEffectVars expression =
    case expression
    of AppT op args ->
         liftM (invariant . pairUnions) $ mapM freeEffectVars (op : args)
       FunT ft -> freeEffectVars ft
       StreamT eff ty2 -> do
         eff_vars <- freeEffectVars eff
         ty2_vars <- freeEffectVars ty2
         return $ pairUnion eff_vars ty2_vars
       VarT _ -> return emptyFreeVars
       ConstT _ -> return emptyFreeVars
       TypeT -> return emptyFreeVars

  expand expression = 
    case expression
    of AppT op args -> AppT `liftM` expand op `ap` mapM expand args
       FunT ft -> FunT `liftM` expand ft
       StreamT eff ty -> StreamT `liftM` expand eff `ap` expand ty
       VarT _ -> return expression
       ConstT _ -> return expression
       TypeT -> return expression

  renameT old_v new_v expression =
    case expression
    of VarT v | v == old_v -> VarT new_v
       _ -> mapParametricPassType (renameT old_v new_v) expression

  assignT old_v val expression =
    case expression
    of VarT v | v == old_v -> val
       _ -> mapParametricPassType (assignT old_v val) expression

  renameE old_v new_v expression =
    mapParametricPassType (renameE old_v new_v) expression

  assignE old_v val expression =
    mapParametricPassType (assignE old_v val) expression

  expression `mentionsE` v =
    case expression
    of AppT op args   -> op `mentionsE` v >||> anyM (`mentionsE` v) args
       FunT ft        -> ft `mentionsE` v
       StreamT eff ty -> eff `mentionsE` v >||> ty `mentionsE` v
       VarT _         -> return False
       ConstT _       -> return False
       TypeT          -> return False

  expression `mentionsAnyE` vs =
    case expression
    of AppT op args -> op `mentionsAnyE` vs >||> anyM (`mentionsAnyE` vs) args
       FunT ft      -> ft `mentionsAnyE` vs
       StreamT eff ty -> eff `mentionsAnyE` vs >||> ty `mentionsAnyE` vs
       VarT _       -> return False
       ConstT _     -> return False
       TypeT        -> return False

instance Parametric FunPassType where
  freeEffectVars expression =
    case expression
    of FunFT param rng -> do 
         fv_range <- freeEffectVars rng
         fv_dom <- freeEffectVars (paramType param)
         let fv_range_minus_param =
               case paramRegion param
               of Nothing -> fv_range
                  Just rv -> (Set.delete rv $ fst fv_range,
                              Set.delete rv $ snd fv_range)
         return $ pairUnion (contravariant fv_dom) fv_range_minus_param
       RetFT eff ty -> do
         eff_vars <- freeEffectVars eff 
         ty_vars <- freeEffectVars ty
         return $ pairUnion eff_vars ty_vars

  expand expression =
    case expression
    of FunFT param rng -> do
         param_type <- expand (paramType param)
         let param' = param {paramType = param_type}
         rng' <- expand rng
         return $ FunFT param' rng'
       RetFT eff ty -> RetFT `liftM` expand eff `ap` expand ty

  renameT old_v new_v expression =
    mapParametricFunType (renameT old_v new_v) expression

  assignT old_v val expression =
    mapParametricFunType (assignT old_v val) expression

  renameE old_v new_v expression =
    mapParametricFunType (renameE old_v new_v) expression

  assignE old_v val expression =
    mapParametricFunType (assignE old_v val) expression
    
  expression `mentionsE` v =
    case expression
    of FunFT param rng -> paramType param `mentionsE` v >||> rng `mentionsE` v
       RetFT eff ty  -> eff `mentionsE` v >||> ty `mentionsE` v

  expression `mentionsAnyE` v =
    case expression
    of FunFT param rng -> paramType param `mentionsAnyE` v >||>
                          rng `mentionsAnyE` v
       RetFT eff ty  -> eff `mentionsAnyE` v >||> ty `mentionsAnyE` v

instance Parametric Effect where
  freeEffectVars effect = do
    eff' <- canonicalizeEffect effect
    return (effectVars eff', Set.empty)

  expand = canonicalizeEffect

  -- There aren't any types inside effects
  renameT _ _ expression = expression
  assignT _ _ expression = expression
  
  renameE old_v new_v eff
    | old_v `Set.member` effectVars eff =
        Effect (Set.insert new_v $ Set.delete old_v $ effectVars eff)
    | otherwise =
        eff

  assignE old_v val eff
    | old_v `Set.member` effectVars eff =
        val `effectUnion` Effect (Set.delete old_v $ effectVars eff)
    | otherwise =
        eff

  eff `mentionsE` v = liftM (`effectMentions` v) $ canonicalizeEffect eff

  eff `mentionsAnyE` vs = do eff' <- canonicalizeEffect eff
                             return $ not $ Set.null $
                               effectVars eff `Set.intersection` vs


-------------------------------------------------------------------------------
-- Subtyping

class Subtype exp where
  assertSubtype :: exp -> exp -> EffInf ()
  assertEqual :: exp -> exp -> EffInf ()
  joinType :: exp -> exp -> EffInf exp
  meetType :: exp -> exp -> EffInf exp

-- | Report that a subtyping check failed.
-- 
-- FIXME: Include some useful information with the report!
subtypeCheckFailed :: EffInf a
subtypeCheckFailed = fail "Subtype check failed in effect inference"

-- | 'Borrowed' is the top of the PassConv lattice, because any value can 
-- be represented that way.
instance Subtype PassConv where
  assertSubtype pc1 pc2
    | pc1 == pc2 = return ()
    | pc2 == Borrowed = return ()
    | otherwise = subtypeCheckFailed

  assertEqual pc1 pc2
    | pc1 == pc2 = return ()
    | otherwise = subtypeCheckFailed

  joinType pc1 pc2
    | pc1 == pc2 = return pc1
    | otherwise = return Borrowed

  meetType pc1 pc2
    | pc1 == pc2 = return pc1
    | pc2 == Borrowed = return pc1
    | pc1 == Borrowed = return pc2
    | otherwise = subtypeCheckFailed

{-
instance Subtype EType where
  assertSubtype t1 t2 =
    case (t1, t2)
    of (AppT op1 args1, AppT op2 args2) -> do
         -- Just test for equality.
         -- We don't consider subtyping of data types.
         assertEqual op1 op2
         zipWithM_ assertEqual args1 args2

       (StreamT eff1 ret1, StreamT eff2 ret2) -> do
         -- Streams are covariant
         assertSubtype eff1 eff2
         assertSubtype ret1 ret2

       (VarT v, VarT v')
         | v == v'   -> return ()
         | otherwise -> subtypeCheckFailed
                        
       (ConstT _, ConstT _) -> do
         -- The types should be equal.  We assume that type checking
         -- has already verified this so we don't need to check it.
         return ()

       (TypeT, TypeT) -> return ()
       (_, _) -> subtypeCheckFailed

  assertEqual t1 t2 =
    case (t1, t2)
    of (AppT op1 args1, AppT op2 args2) -> do
         assertEqual op1 op2
         zipWithM_ assertEqual args1 args2

       (StreamT eff1 ret1, StreamT eff2 ret2) -> do
         assertEqual eff1 eff2
         assertEqual ret1 ret2

       (VarT v, VarT v')
         | v == v'   -> return ()
         | otherwise -> subtypeCheckFailed
                        
       (ConstT _, ConstT _) -> do
         -- The types should be equal.  We assume that type checking
         -- has already verified this so we don't need to check it.
         return ()

       (TypeT, TypeT) -> return ()
       (_, _) -> subtypeCheckFailed

  joinType t1 t2 =
    case (t1, t2)
    of (AppT op1 args1, AppT op2 args2) -> do
         assertEqual op1 op2
         zipWithM_ assertEqual args1 args2
         return $ AppT op1 args1

       (StreamT eff1 ret1, StreamT eff2 ret2) -> do
         -- Streams are covariant
         eff <- joinType eff1 eff2
         ret <- joinType ret1 ret2
         return $ StreamT eff ret

       (VarT v, VarT v')
         | v == v'   -> return t1
         | otherwise -> subtypeCheckFailed
                        
       (ConstT _, ConstT _) -> do
         -- The types should be equal.  We assume that type checking
         -- has already verified this so we don't need to check it.
         return t1

       (TypeT, TypeT) -> return t1
       (_, _) -> subtypeCheckFailed
         
  meetType t1 t2 =
    case (t1, t2)
    of (AppT op1 args1, AppT op2 args2) -> do
         assertEqual op1 op2
         zipWithM_ assertEqual args1 args2
         return $ AppT op1 args1

       (StreamT eff1 ret1, StreamT eff2 ret2) -> do
         -- Streams are covariant
         eff <- meetType eff1 eff2
         ret <- meetType ret1 ret2
         return $ StreamT eff ret

       (VarT v, VarT v')
         | v == v'   -> return t1
         | otherwise -> subtypeCheckFailed
                        
       (ConstT _, ConstT _) -> do
         -- The types should be equal.  We assume that type checking
         -- has already verified this so we don't need to check it.
         return t1

       (TypeT, TypeT) -> return t1
       (_, _) -> subtypeCheckFailed-}

instance Subtype PassType where  
  assertSubtype t1 t2 =
    case (t1, t2)
    of (AppT op1 args1, AppT op2 args2) -> do
         -- Just test for equality.
         -- We don't consider subtyping of data types.
         assertEqual op1 op2
         zipWithM_ assertEqual args1 args2

       (FunT t1, FunT t2) ->
         assertSubtype t1 t2

       (StreamT eff1 ret1, StreamT eff2 ret2) -> do
         -- Streams are covariant
         assertSubtype eff1 eff2
         assertSubtype ret1 ret2

       (VarT v, VarT v')
         | v == v' -> return ()
         | otherwise -> subtypeCheckFailed
                        
       (ConstT _, ConstT _) -> do
         -- The types should be equal.  We assume that type checking
         -- has already verified this so we don't need to check it.
         return ()

       (TypeT, TypeT) -> return ()

       (_, _) -> subtypeCheckFailed

  assertEqual t1 t2 =
    case (t1, t2)
    of (AppT op1 args1, AppT op2 args2) -> do
         assertEqual op1 op2
         zipWithM_ assertEqual args1 args2

       (FunT t1, FunT t2) ->
         assertEqual t1 t2

       (StreamT eff1 ret1, StreamT eff2 ret2) -> do
         assertEqual eff1 eff2
         assertEqual ret1 ret2

       (VarT v, VarT v')
         | v == v' -> return ()
         | otherwise -> subtypeCheckFailed
                        
       (ConstT _, ConstT _) -> do
         -- The types should be equal.  We assume that type checking
         -- has already verified this so we don't need to check it.
         return ()

       (TypeT, TypeT) -> return ()

       (_, _) -> subtypeCheckFailed

  joinType t1 t2 =
    case (t1, t2)
    of (AppT op1 args1, AppT op2 args2) -> do
         assertEqual op1 op2
         zipWithM_ assertEqual args1 args2
         return $ AppT op1 args1

       (FunT t1, FunT t2) ->
         FunT `liftM` joinType t1 t2

       (StreamT eff1 ret1, StreamT eff2 ret2) -> do
         -- Streams are covariant
         eff <- joinType eff1 eff2
         ret <- joinType ret1 ret2
         return $ StreamT eff ret

       (VarT v, VarT v')
         | v == v' -> return t1
         | otherwise -> subtypeCheckFailed
                        
       (ConstT _, ConstT _) -> do
         -- The types should be equal.  We assume that type checking
         -- has already verified this so we don't need to check it.
         return t1

       (TypeT, TypeT) -> return t1
       
       (_, _) -> subtypeCheckFailed

  meetType t1 t2 =
    case (t1, t2)
    of (AppT op1 args1, AppT op2 args2) -> do
         assertEqual op1 op2
         zipWithM_ assertEqual args1 args2
         return $ AppT op1 args1

       (FunT t1, FunT t2) ->
         FunT `liftM` meetType t1 t2
       
       (StreamT eff1 ret1, StreamT eff2 ret2) -> do
         -- Streams are covariant
         eff <- meetType eff1 eff2
         ret <- meetType ret1 ret2
         return $ StreamT eff ret

       (VarT v, VarT v')
         | v == v' -> return t1
         | otherwise -> subtypeCheckFailed
                        
       (ConstT _, ConstT _) -> do
         -- The types should be equal.  We assume that type checking
         -- has already verified this so we don't need to check it.
         return t1

       (TypeT, TypeT) -> return t1

       (_, _) -> subtypeCheckFailed

-- | Functions don't have to agree on parameter passing conventions.
instance Subtype FunPassType where
  assertSubtype t1 t2 =
    case (t1, t2)
    of (FunFT param1 rng1, FunFT param2 rng2) -> do
         -- Parameters are contravariant
         assertSubtype (paramType param2) (paramType param1)
         -- Allow any passing convention
         
         -- Range is covariant
         withSameFunParam (param1, rng1) (param2, rng2) $
           \_ rng1' rng2' -> assertSubtype rng1' rng2'

       (RetFT e1 pt1, RetFT e2 pt2) -> do
         assertSubtype e1 e2
         assertSubtype pt1 pt2

       (_, _) -> subtypeCheckFailed

  assertEqual t1 t2 =
    case (t1, t2)
    of (FunFT param1 rng1, FunFT param2 rng2) -> do
         assertEqual (paramType param2) (paramType param1)
         -- Allow any passing convention
         withSameFunParam (param1, rng1) (param2, rng2) $
           \_ rng1' rng2' -> assertEqual rng1' rng2'

       (RetFT e1 pt1, RetFT e2 pt2) -> do
         assertEqual e1 e2
         assertEqual pt1 pt2

       (_, _) -> subtypeCheckFailed

  joinType t1 t2 =
    case (t1, t2)
    of (FunFT param1 rng1, FunFT param2 rng2) -> do
         -- Parameters are contravariant
         param_ty <- meetType (paramType param1) (paramType param2)
         
         withSameFunParam (param1, rng1) (param2, rng2) $
           \p rng1' rng2' -> do
             let param' = FunParam (paramRegion p) (paramTyVar p) param_ty
             -- Range is covariant
             rng' <- joinType rng1' rng2'
             return $ FunFT param' rng'

       (RetFT e1 pt1, RetFT e2 pt2) -> do
         e <- joinType e1 e2
         pt <- joinType pt1 pt2
         return $ RetFT e pt
         
       (_, _) -> subtypeCheckFailed

  meetType t1 t2 =
    case (t1, t2)
    of (FunFT param1 rng1, FunFT param2 rng2) -> do
         -- Parameters are contravariant
         param_ty <- joinType (paramType param1) (paramType param2)
         
         withSameFunParam (param1, rng1) (param2, rng2) $
           \p rng1' rng2' -> do
             let param' = FunParam (paramRegion p) (paramTyVar p) param_ty
             -- Range is covariant
             rng' <- meetType rng1' rng2'
             return $ FunFT param' rng'

       (RetFT e1 pt1, RetFT e2 pt2) -> do
         e <- meetType e1 e2
         pt <- meetType pt1 pt2
         return $ RetFT e pt

       (_, _) -> subtypeCheckFailed

instance Subtype Effect where
  assertSubtype e1 e2 = addConstraint (subEffect e1 e2)
  assertEqual e1 e2 = do 
    -- Simplify the constraint to make solving easier    
    ctx <- getRigidEffectVars
    e1_s <- liftIO $ canonicalizeEffect e1
    e2_s <- liftIO $ canonicalizeEffect e2
    
    -- Remove rigid variables found in both e1 and e2 
    let rigid_common =
          ctx `Set.intersection` effectVars e1_s `Set.intersection`
          effectVars e2_s
        e1_s' = Effect $ effectVars e1_s Set.\\ rigid_common
        e2_s' = Effect $ effectVars e2_s Set.\\ rigid_common

    -- In the common case, e1 or e2 is a single variable.
    -- Assign the variable's value now.  If assignment fails, then
    -- the constraints are unsatisfiable.
    case from_singleton e1_s' of
      Just v ->
        case from_singleton e2_s'
        of Just v' | v == v' -> return ()
           _ -> liftIO $ assignEffectVarD "assertEqual" v e2_s'
      Nothing ->
        case from_singleton e2_s'
        of Just v -> liftIO $ assignEffectVarD "assertEqual" v e1_s'
           Nothing -> do
             -- Otherwise, create a pair of constraints
             addConstraint (subEffect e1 e2 ++ subEffect e2 e1)
    where
      from_singleton (Effect s) =
        case Set.toList s
        of [v] -> Just v
           _ -> Nothing
  
  -- Create a new effect variable that's greater than both effects
  joinType e1 e2 = do
    evar <- newEffectVar Nothing
    let eff = varEffect evar
    addConstraint (subEffect e1 eff ++ subEffect e2 eff)
    return eff

  -- Create a new effect variable that's less than both effects
  meetType e1 e2 = do
    evar <- newEffectVar Nothing
    let eff = varEffect evar
    addConstraint [SubEffect evar e1, SubEffect evar e2]
    return eff

-------------------------------------------------------------------------------
-- Instantiation

instantiatePassType :: PolyPassType -> RegionM ([EVar], PassType)
instantiatePassType (PolyPassType evars pass_type) =
  ins evars =<< liftIO (expand pass_type)
  where
    ins (v:vs) pass_type = do
      -- Rename v to a fresh variable name
      v' <- newEffectVar (evarName v)
      let pass_type' = renameE v v' pass_type
      (vs', pass_type'') <- ins vs pass_type'
      return (v':vs', pass_type'')

    ins [] body = return ([], body)

-- | Set all flexible effect variables in the expression to the empty effect
clearFlexibleEffectVariables :: Parametric exp => exp -> RegionM ()
clearFlexibleEffectVariables e = withRigidEffectVars $ \ctx -> do
  (fvs_pos, fvs_neg) <- freeEffectVars e
  let fvs = Set.union fvs_pos fvs_neg
  forM_ (Set.toList fvs) $ \v -> do
    unless (v `Set.member` ctx) $ assignEffectVarD "clearFlexible" v emptyEffect

-- | Transform the constraint set into an equivalent one where all
-- flexible, free variables mentioned by the expression are independent.
makeFlexibleVariablesIndependent :: Parametric exp =>
                                    EffInf (exp, a) -> EffInf (exp, a)
makeFlexibleVariablesIndependent mk_exp = EffInf $ \env -> do
  ((exp, x), cst) <- doEffInf mk_exp env
  cst' <- doRegionM (makeFlexibleVariablesIndependentWithConstraint exp (cst [])) (efRegionEnv env)
  return ((exp, x), (cst' ++))

makeFlexibleVariablesIndependent' :: Parametric exp => EffInf exp -> EffInf exp
makeFlexibleVariablesIndependent' m = do
  (x, ()) <- makeFlexibleVariablesIndependent $ do x <- m
                                                   return (x, ())
  return x

-- | Transform the constraint set into an equivalent one where all
-- flexible variables mentioned by the expression are independent.
makeFlexibleVariablesIndependentWithConstraint ::
  Parametric exp => exp -> Constraint -> RegionM Constraint
makeFlexibleVariablesIndependentWithConstraint exp cst = do
  -- simplify the constraint
  cst1 <- reduceConstraint cst

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
      | Set.size (effectVars rhs) <= 1 = True
      | otherwise = not $ v `Set.member` effectVars rhs
                    
    mentions_on_rhs v (SubEffect _ rhs) = v `Set.member` effectVars rhs

    get_flexible_vars = withRigidEffectVars $ \ctx -> do
      (fvs_pos, fvs_neg) <- freeEffectVars exp
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
        not (Set.null $ effectVars rhs `Set.intersection` fvs) = do
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
