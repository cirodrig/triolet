{-| Effect and region variables.
-}

{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
module SystemF.Flatten.Effect
       (-- * Effect and region variables
        EffectVar, effectVarID,
        pprEffectVar,
         
        EVar, RVar,
        isEVar, isRVar, 
        assertEVar, assertRVar,
        newEffectVar, newRegionVar,

        -- ** Unification
        assignEffectVar, assignEffectVarD,
        unifyRegionVars,
        evalRVar, evalEVar,
        evalEffectVar,
        splitEffectVar,
        
        -- * Effects
        Effect,
        pprEffect, evalAndPprEffect,
        evalEffect,
        
        -- ** Construction
        emptyEffect, varEffect, maybeVarEffect, varsEffect,
        
        -- ** Querying
        isEmptyEffect,
        effectMentions,
        effectContainsEffectVariables,

        -- ** Operations on effects
        effectUnion, effectUnions,
        deleteFromEffect, maybeDeleteFromEffect, deleteListFromEffect,
        renameInEffect,
        assignInEffect,
        
        -- ** Inspecting
        fromEffect, fromEffectSet,
        effectMembers,
        
        -- * Monad types for manipulating regions
        RegionM(doRegionM), runRegionM,
        RegionEnv(..),
        
        RegionMonad(..),
        assumeMaybeRegion,
        withRigidEffectVars,
        isRigid, isRigid', isFlexible, isFlexible', isSplittable
       )
where

import Codec.Binary.UTF8.String
import Control.Monad
import Control.Monad.ST
import Control.Monad.Trans
import Data.Function
import Data.IORef
import Data.List
import Data.Maybe
import qualified Data.Set as Set
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.Supply
import Gluon.Core(Var)
import Gluon.Eval.Environment

-- | Set this to True to print a message every time a variable is assigned
debugAssignments :: Bool
debugAssignments = True

-------------------------------------------------------------------------------
-- Effect variables

-- | An effect or region variable.
--
-- A region variable represents a memory location, distinct from all other
-- memory locations.  An effect variables represent a set of regions.  Effect
-- variables may be assigned effect values via unification and may be
-- generalized over.  Region variables represent exactly one region, and may  
-- be unified with other regions.
--
-- Variables have a flag indicating whether the variable is /flexible/.  A 
-- flexible variable may be unified, while a non-flexible or /rigid/ variable
-- cannot.  (A flexible variable may be unified with a rigid variable; the
-- rigid variable remains unchanged and the flexible variable becomes equal
-- to the rigid variable).  Flexible variables are created by type 
-- instantiation.

data EffectVar =
  EffectVar
  { _evarID :: {-# UNPACK #-} !(Ident EffectVar)
  , _evarKind :: !EffectVarKind
  , _evarIsFlexible :: {-# UNPACK #-}!Bool
  , _evarRep :: {-# UNPACK #-}!(IORef EffectVarRep)
  }
  
effectVarID v   = _evarID v

-- | Effect variables may stand for either a single region or an arbitrary
-- set of regions.
data EffectVarKind = RegionEffectVar | EffectEffectVar
                   deriving(Eq)

-- | An effect variable
type EVar = EffectVar

-- | A region variable
type RVar = EffectVar

instance Eq EffectVar where
  (==) = (==) `on` _evarID
  (/=) = (/=) `on` _evarID

instance Ord EffectVar where
  compare = compare `on` _evarID

isEVar, isRVar :: EffectVar -> Bool
isEVar v = _evarKind v == EffectEffectVar
isRVar v = _evarKind v == RegionEffectVar

assertRVar :: EffectVar -> a -> a
assertRVar v x
  | isRVar v = x
  | otherwise = internalError "assertRVar: not a region variable"

assertEVar :: EffectVar -> a -> a
assertEVar v x
  | isEVar v = x
  | otherwise = internalError "assertEVar: not an effect variable"

assertFlexible :: EffectVar -> a -> a
assertFlexible v x
  | isFlexible' v = x
  | otherwise = internalError "assertFlexible: variable is rigid"

-- | Create a new region variable
newRegionVar :: (Monad m, MonadIO m, Supplies m (Ident EffectVar))
             => Bool -> m EffectVar
newRegionVar is_flexible = makeNewEffectVar RegionEffectVar is_flexible

-- | Create a new effect variable
newEffectVar :: (Monad m, MonadIO m, Supplies m (Ident EffectVar))
             => m EffectVar
newEffectVar = makeNewEffectVar EffectEffectVar True

makeNewEffectVar :: (Monad m, MonadIO m, Supplies m (Ident EffectVar))
                 => EffectVarKind -> Bool -> m EffectVar
makeNewEffectVar k is_flexible = do
  id <- fresh
  rep <- liftIO $ newIORef EVNoRep
  return $ EffectVar id k is_flexible rep

-------------------------------------------------------------------------------
-- Effects

-- | An effect is a set of regions and effect variables
newtype Effect = Effect {effectVars :: Set.Set EffectVar}

emptyEffect :: Effect
emptyEffect = Effect Set.empty

varEffect :: EffectVar -> Effect
varEffect v = Effect (Set.singleton v)

maybeVarEffect :: Maybe EffectVar -> Effect
maybeVarEffect Nothing  = emptyEffect
maybeVarEffect (Just v) = varEffect v

varsEffect :: [EffectVar] -> Effect
varsEffect vs = Effect (Set.fromList vs)

isEmptyEffect :: Effect -> Bool
isEmptyEffect (Effect s) = Set.null s

effectMentions :: Effect -> EffectVar -> Bool 
Effect vs `effectMentions` v = v `Set.member` vs

effectContainsEffectVariables :: Effect -> Bool
effectContainsEffectVariables (Effect e) =
  any ((EffectEffectVar ==) . _evarKind) $ Set.toList e

effectUnion :: Effect -> Effect -> Effect
effectUnion (Effect e1) (Effect e2) = Effect (Set.union e1 e2)
                                      
effectUnions :: [Effect] -> Effect
effectUnions es = foldr effectUnion emptyEffect es

-- | Remove occurrences of a region or rigid effect variable from an effect.
-- The effect should be evaluated with 'evalEffect' first.
deleteFromEffect :: EffectVar -> Effect -> Effect
deleteFromEffect v (Effect e) = assertRVar v $ Effect (Set.delete v e)

-- | Call 'deleteFromEffect' on the parameter if it is a @Just@ value.
maybeDeleteFromEffect :: Maybe EffectVar -> Effect -> Effect
maybeDeleteFromEffect Nothing  e = e
maybeDeleteFromEffect (Just v) e = deleteFromEffect v e

-- | Remove occurrences of each regions and rigid effect variable in the list
-- from an effect.
-- The effect should be evaluated with 'evalEffect' first. 
deleteListFromEffect :: [EffectVar] -> Effect -> Effect
deleteListFromEffect vs e = foldr deleteFromEffect e vs

-- | Rename an effect variable in an effect.  The original and new effect
-- variables must not have been unified with anything.
renameInEffect :: EffectVar -> EffectVar -> Effect -> Effect
renameInEffect v v' (Effect vs)
  | v `Set.member` vs = Effect $ Set.insert v' $ Set.delete v vs
  | otherwise = Effect vs

assignInEffect :: EffectVar -> Effect -> Effect -> Effect
assignInEffect v value (Effect vs)
  | v `Set.member` vs = effectUnion value $ Effect $ Set.delete v vs
  | otherwise = Effect vs

-- | Get the effect and region variables mentioned in an effect.  The effect
-- is not evaluated before getting its contents; the return value may be
-- wrong if unification has been performed since the last time the effect was
-- evaluated.
fromEffect :: Effect -> [EffectVar]
fromEffect (Effect vs) = Set.toList vs

fromEffectSet :: Effect -> Set.Set EffectVar
fromEffectSet (Effect vs) = vs

-- | Get the effect and region variables mentioned in an effect.
effectMembers :: Effect -> IO [EffectVar]
effectMembers e =
  liftM (Set.toList . effectVars) $ evalEffect e

-------------------------------------------------------------------------------
-- Effect unification

-- | The representative of an effect variable, assigned by unification.
-- An effect variable may be unified with another variable or with a value.
data EffectVarRep = EVNoRep | EVVarRep !EffectVar | EVValueRep !Effect

-- | Assign an effect variable's representative.  The variable should not
-- have been assigned already.  The effect variable must not be mentioned
-- in the given effect.
assignEffectVar :: EffectVar -> Effect -> IO ()
assignEffectVar ev e = traceShow (text "assignEffectVar" <+> pprEffectVar ev) $ assertEVar ev $ assertFlexible ev $ do
  e' <- evalEffect e
  when (e' `effectMentions` ev) $
    internalError "assignEffectVar: Occurs check failed"

  -- DEBUG
  when debugAssignments $
    print $ pprEffectVar ev <+> text ":=" <+> pprEffect e

  rep <- readIORef (_evarRep ev)
  case rep of
    EVNoRep -> writeIORef (_evarRep ev) (EVValueRep e')
    _ -> internalError "assignEffectVar: Already assigned"

-- | Print a debug message, then call 'assignEffectVar'.
assignEffectVarD msg ev e
  | debugAssignments = trace msg $ assignEffectVar ev e
  | otherwise = assignEffectVar ev e

-- | Unify two region variables.  Return the representative.  One of the region
-- variables must be flexible.
unifyRegionVars :: RVar -> RVar -> IO RVar
unifyRegionVars v1 v2 = assertRVar v1 $ assertRVar v2 $ do
  v1' <- evalRVar v1
  v2' <- evalRVar v2
  if isFlexible' v1'
    then do writeIORef (_evarRep v1') (EVVarRep v2')
            trace_assignment v1' v2' $ return v2'
    else if isFlexible' v2'
         then do writeIORef (_evarRep v2') (EVVarRep v1')
                 trace_assignment v2' v1' $ return v1'
         else -- XXX: Is this only caused by compiler bugs, or can some inputs
              -- cause this error?
           internalError "unifyRegionVars: attempted to unify rigid variables"
  where
    trace_assignment assignee value k
      | debugAssignments =
          traceShow (text "Assigning " <+>
                     pprEffectVar assignee <+> text ":=" <+>
                     pprEffectVar value) k
      | otherwise = k

-- | Remove indirections from an effect variable representative
evalEffectVarRep :: IORef EffectVarRep -> IO EffectVarRep
evalEffectVarRep ref = do
  rep <- readIORef ref
  case rep of
    EVNoRep      -> return rep
    EVVarRep v   -> update_self rep =<< evalEffectVarRep (_evarRep v)
    EVValueRep e -> return rep
  where
    update_self old_rep EVNoRep = return old_rep
    update_self _       new_rep = do writeIORef ref new_rep
                                     return new_rep

-- | Get the representative of a region variable.
evalRVar :: RVar -> IO RVar
evalRVar rv
  | not $ isRVar rv = internalError "evalRVar: not a region variable"
  | otherwise = do
      rep <- evalEffectVarRep (_evarRep rv)
      case rep of EVNoRep      -> return rv
                  EVVarRep v'  -> return v'
                  EVValueRep _ -> internalError "evalRVar: Region was unified with an effect"

-- | Get the representative of an effect variable.  This call will fail if the
-- effect variable has been unified with an effect.
evalEVar :: EVar -> IO EVar
evalEVar ev
  | not $ isEVar ev = internalError "evalEVar: not an effect variable"
  | otherwise = do
      rep <- evalEffectVarRep (_evarRep ev)
      case rep of
        EVNoRep      -> return ev
        EVVarRep ev' -> return ev'
        EVValueRep _ -> internalError "evalEVar: Got an effect, not an effect variable"

-- | Get the value of an effect or region variable.  If no value has been
-- assigned by unification, the return value is equal to the original effect
-- variable.
evalEffectVar :: EffectVar -> IO Effect
evalEffectVar ev = do
  rep <- evalEffectVarRep (_evarRep ev)
  case rep of EVNoRep      -> return $ varEffect ev
              EVVarRep v   -> return $ varEffect v
              EVValueRep e -> evalEffect e

-- | Decompose an effect variable into two parts.  The effect variable must
-- not be rigid and must not have been unified with anything.
splitEffectVar :: (Monad m, MonadIO m, Supplies m (Ident EffectVar)) =>
                  EffectVar -> m (EffectVar, EffectVar)
splitEffectVar v = trace ("splitEffectVar " ++ show (pprEffectVar v)) $ assertEVar v $ do
  v1 <- newEffectVar
  v2 <- newEffectVar
  liftIO $ assignEffectVarD "splitEffectVar" v $ varsEffect [v1, v2]
  when debugAssignments $ display v
  return (v1, v2)
  where
    display v = liftIO $ do
      v_effect <- evalEffectVar v
      print (pprEffectVar v <+> text "-->" <+> pprEffect v_effect)

-- | Get the value of an effect, as computed by unification.
evalEffect :: Effect -> IO Effect
evalEffect (Effect es) =
  liftM effectUnions $ mapM evalEffectVar $ Set.toList es

-------------------------------------------------------------------------------
-- Pretty-printing

angles :: Doc -> Doc
angles d = text "<" <> d <> text ">"

pprEffectVar :: EffectVar -> Doc
pprEffectVar v = 
  let l = case _evarKind v
          of RegionEffectVar -> 'r'
             EffectEffectVar -> 'e'
  in text (l : show (fromIdent $ _evarID v))

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

evalAndPprEffect :: Effect -> IO Doc
evalAndPprEffect eff = do 
  eff' <- evalEffect eff
  return $ pprEffect eff'

-------------------------------------------------------------------------------
-- Monad definitions

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
--
-- TODO: Use a flag in the variable to determine its rigidity, instead of the
-- context
isRigid :: RegionMonad m => EffectVar -> m Bool
isRigid v = return $ not $ _evarIsFlexible v -- liftM (v `Set.member`) $ getRigidEffectVars

isFlexible :: RegionMonad m => EffectVar -> m Bool
isFlexible v = return $ _evarIsFlexible v -- liftM (not . (v `Set.member`)) $ getRigidEffectVars

isRigid' = not . isFlexible'

isFlexible' :: EffectVar -> Bool
isFlexible' v = _evarIsFlexible v
                             
-- | Determine whether a variable can be subdivided into two effect variables.
--
-- Flexible effect variables are splittable.  Rigid variables are not
-- splittable.  Region variables are not splittable.
--
-- Distinct non-splittable variables represent disjoint memory areas.
isSplittable :: EffectVar -> Bool
isSplittable v = isEVar v && isFlexible' v

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

instance Functor RegionM where
  fmap f m = return . f =<< m

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
  assumeEffect v m = trace "assumeEffect" $ assertEVar v $ assumeEffectVariableRegionM v m
  
  getRigidEffectVars = RegionM (\env -> return (reRegionEnv env))

  liftPureTC m = RegionM $ \env -> do
    result <- runPureTCIO (reVarIDs env) m
    case result of
      Left errs -> fail "Unhandled type errors in effect inference"
      Right x -> return x

