{-| This module contains a definition of unifiable variables.

Unification is parameterized over a term type to separate it from the
implementation of data types.  When this module is used, the term type
is instantiated to 'HMType'.
-}

{-# LANGUAGE FlexibleContexts, RankNTypes, ConstraintKinds #-}
module Untyped.Unif
       (newUVarIDSupply,
        UMonad(..),

        -- * Types
        UVar,
        uVarName, uVarKind,
        UVarSet,
        newUVar, newAnonymousUVar, duplicateUVar,
        assertNormalizedUVar,
        isFreeUVar,
        normalizeUVar,
        unifyUVar,
        unifyUVars,
        freeUVars,
        hasFreeUVar,

        -- ** Unification support
        NormalizeContext,
        UTerm(..),
        occursCheck,
        occursInjectively,
        subexpressionCheck,
        unify,
        semiUnify,
        match,
        uEqual,
        substituteType,

        -- * Pretty-printing support
        PprContext,
        initialPprContext,
        getUVarName,
        decorateName
       )
where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import Data.Function
import Data.IORef
import Data.List
import qualified Data.Map as Map
import Data.Monoid
import qualified Data.Set as Set
import GHC.Exts
import Text.PrettyPrint.HughesPJ

import Common.Identifier
import Common.Label
import Common.MonadLogic
import Common.Supply
import Untyped.Kind

-- | A monad in which unification can be performed
class (Applicative m, MonadIO m) => UMonad term m where
  freshUVarID :: m (Ident (UVar term))

newUVarIDSupply :: IO (IdentSupply (UVar term))
newUVarIDSupply = newIdentSupply

-- | Report a kind error.  Give very rough information about where the
--   error occurred.
kindError loc =
  error $ "Kind error in " ++ loc

-------------------------------------------------------------------------------
-- Unifiable variables

-- | A unifiable variable ranging over kinded 'term's
data UVar term =
  UVar
  { _uID  :: {-# UNPACK #-} !(Ident (UVar term)) -- ^ An ID uniquely
                                                 -- identifying this variable
  , _uName :: !(Maybe Label)       -- ^ The variable's name, if any
  , _uKind :: Kind                 -- ^ The variable's kind
  , _uRep  :: !(IORef (URep term)) -- ^ The variable's value
  }

uVarName :: UVar term -> Maybe Label
uVarName = _uName

uVarKind :: UVar term -> Kind
uVarKind = _uKind

type UVarSet term = Set.Set (UVar term)

readRep r = liftIO $ readIORef r 
writeRep r v = liftIO $ writeIORef r v

-- | Equality is based on equality of IDs.
--
--   In most cases, we care about equality modulo unification, which means
--   that a variable should be normalized before checking equality.
instance Eq (UVar term) where
  (==) = (==) `on` _uID
  (/=) = (/=) `on` _uID

-- | Variables are ordered by ID.
instance Ord (UVar term) where
  compare = compare `on` _uID

newUVar :: UMonad term m => Maybe Label -> Kind -> m (UVar term)
newUVar name kind = do
  rep <- newRep
  id <- freshUVarID
  return $ UVar id name kind rep

-- | Create an unlabeled variable
newAnonymousUVar :: UMonad term m => Kind -> m (UVar term)
newAnonymousUVar k = newUVar Nothing k

-- | Create a copy of a unification variable
duplicateUVar :: UMonad term m => UVar term -> m (UVar term)
duplicateUVar v = newUVar (_uName v) (_uKind v)

-- | Test whether a variable hasn't been unified with something else
isFreeUVar :: UMonad term m => UVar term -> m Bool
isFreeUVar v = do
  rep <- readRep $ _uRep v
  return $ isFree rep

assertNormalizedUVar :: UMonad term m => UVar term -> m ()
assertNormalizedUVar v = do
  rep <- readRep $ _uRep v
  unless (isFree rep) $ fail "Expecting a normalized unification variable"

-- | Get the variable or term value of a given unifiable variable
normalizeUVar :: NormalizeContext term m => UVar term -> m term
normalizeUVar v = make_term =<< normalizeRep (_uRep v)
  where
    make_term Free           = return $ injectU v
    make_term (Forwarded v') = return $ injectU v'
    make_term (Assigned t)   = return t

-- | Unify two type variables.  The variables should be canonical.
unifyUVars :: UMonad term m => UVar term -> UVar term -> m ()
unifyUVars v1 v2 = do
  assertNormalizedUVar v1
  assertNormalizedUVar v2
  case () of 
    () | v1 == v2               -> return ()
       | _uKind v1 /= _uKind v2 -> kindError "type unification"
       | otherwise              -> writeRep (_uRep v1) (Forwarded v2)

unifyUVar :: NormalizeContext term m => UVar term -> term -> m ()
unifyUVar v t
  | _uKind v /= kind t = kindError "type unification"
  | otherwise = do
      assertNormalizedUVar v
      whenM (occursCheck v t) $ fail "Occurs check failed"
      writeRep (_uRep v) (Assigned t)

-------------------------------------------------------------------------------
-- Values assigned to unifiable variables 

-- | The value assigned to a unifiable variable
data URep term =
    Free                          -- ^ No value assigned
  | Forwarded !(UVar term)        -- ^ Unified with another variable; see 
                                  --   its contents to get the value
  | Assigned term                 -- ^ Unified with a value

debugShowURep :: URep term -> String
debugShowURep Free          = "Free"
debugShowURep (Forwarded _) = "Forwarded"
debugShowURep (Assigned _)  = "Assigned"

isFree Free = True
isFree _    = False

isUnified = not . isFree

type NormalizeContext term m =
  (UTerm term, NormalizeMonadConstraint term m, UMonad term m)

-- | A unifiable term.
--
--   A unifiable term is a unifiable variable, a constructor applied to
--   terms, or a function applied to terms.
class Monoid (UConstraint term) => UTerm term where
  type NormalizeMonadConstraint term m :: Constraint
  type UConstraint term 

  -- | Get the term's kind
  kind :: term -> Kind

  -- | Normalize the head of a term.  Note that if the head is a variable,
  --   this function should normalize that variable as well.
  normalize :: (NormalizeMonadConstraint term m, UMonad term m) =>
               term -> m term
  
  -- | Convert a unifiable variable to a term
  injectU :: UVar term -> term

  -- | If the term is a unifiable variable, convert it to a variable
  projectU :: term -> Maybe (UVar term)

  -- | Get the subterms of a term and a reconstructor function
  listU :: term -> ([term], [term] -> term)

  -- | Unify the heads of two terms, if possible.
  --   Returns 'Nothing' if they cannot be unified.
  --   Returns generated constraints, subterms, and a reconstructor function
  --   if they can be unified.
  zipU :: term -> term
       -> Maybe (UConstraint term, [(term, term)], [term] -> term)

  -- | Return 'True' if the head term is a non-reducible function that
  --   could be unified later
  deferableU :: term -> Bool

  -- | Create a constraint representing a deferred unification of the two
  --   given terms
  deferUnification :: term -> term -> UConstraint term

elemsU = fst . listU

newRep :: UMonad term m => m (IORef (URep term))
newRep = liftIO $ newIORef Free

-- | Get the actual value of a 'URep' object.
--   The 'URep' object is updated in the process.
normalizeRep :: NormalizeContext term m =>
                IORef (URep term) -> m (URep term)
normalizeRep rep_ref = readRep rep_ref >>= follow False 
  where
    follow changed rep =
      case rep
      of Free -> update Free

         -- Normalize 'v', then update this reference
         Forwarded v -> normalizeRep (_uRep v) >>= update

         -- Normalize 't'.
         -- If it's a unifiable variable, get its representation.
         Assigned t -> do
           t' <- normalize t
           case projectU t' of
             Just v  -> follow True (Forwarded v)
             Nothing -> update (Assigned t')
      where
        update Free = do
          -- Don't save new_ref.
          -- Update this variable's representation if it has changed.
          when changed $ writeRep rep_ref rep
          return rep

        update new_rep = do
          -- Save new_ref.
          writeRep rep_ref new_rep
          return new_rep

-------------------------------------------------------------------------------
-- Substitutions

-- | A substitution of terms for unifiable variables
newtype USubstitution term = USubstitution (Map.Map (UVar term) term)

emptyUSubstitution :: USubstitution term
emptyUSubstitution = USubstitution Map.empty

insertUSubstitution :: UVar term -> term -> USubstitution term
                    -> USubstitution term
insertUSubstitution v t (USubstitution m) = USubstitution (Map.insert v t m)

lookupUSubstitution :: UVar term -> USubstitution term -> Maybe term
lookupUSubstitution v (USubstitution m) = Map.lookup v m

substituteU :: NormalizeContext term m =>
               USubstitution term -> term -> m term
substituteU subst t = go =<< normalize t
  where
    go t
      | Just v <- projectU t, Just t' <- lookupUSubstitution v subst =
          return t'
      | otherwise =
          let (subterms, rebuild) = listU t
          in rebuild `liftM` mapM (substituteU subst) subterms

-------------------------------------------------------------------------------
-- Algorithms that traverse a term

-- | Get all free unification variables in the term
freeUVars :: NormalizeContext term m => term -> m (UVarSet term)
freeUVars t = fv t
  where
    fv t = fv' =<< normalize t
    fv' t
      | Just v <- projectU t = return $ Set.singleton v
      | otherwise            = foldM (\s t -> Set.union s `liftM` fv t)
                               Set.empty $ elemsU t

-- | Test whether the term has any free unification variables
hasFreeUVar :: NormalizeContext term m => term -> m Bool
hasFreeUVar t = fv t
  where
    fv t = fv' =<< normalize t
    fv' t
      | Just _ <- projectU t = return True
      | otherwise            = anyM hasFreeUVar $ elemsU t

-- | Check whether a variable appears in the term
occursCheck :: NormalizeContext term m => UVar term -> term -> m Bool
occursCheck v t = do
  assertNormalizedUVar v
  occ t
  where
    occ t = occ' =<< normalize t
    occ' t
      | Just v2 <- projectU t = return $ v == v2
      | otherwise             = anyM occ $ elemsU t

-- | Check whether a variable (which should be in canonical form) appears
--   in the type under injective constructors (such as data type constructors).
--   This function differs from 'occursCheck' only in its handling of
--   function applications.
occursInjectively :: NormalizeContext term m => UVar term -> term -> m Bool
occursInjectively v t = do
  assertNormalizedUVar v
  occ t
  where
    occ t = occ' =<< normalize t
    occ' t
      | Just v2 <- projectU t = return $ v == v2
      | deferableU t          = return False
      | otherwise             = anyM occ $ elemsU t

-- | Check whether @t1@ is a subexpression of @t2@
subexpressionCheck :: NormalizeContext term m => term -> term -> m Bool
subexpressionCheck subterm t = check t
  where
    check t = do 
      t_c <- normalize t
      uEqual subterm t_c >||> anyM check (elemsU t_c)

-- | Unify two terms.  Return 'Nothing' if unification failed, or a new
--   constraint if it succeeded.
unify :: forall term m. NormalizeContext term m =>
         term -> term -> m (Maybe (UConstraint term))
unify t1 t2 = do
  t1_c <- normalize t1
  t2_c <- normalize t2
  case () of
    () -- Unify variables if possible
       | Just v1 <- projectU t1_c, Just v2 <- projectU t2_c ->
           unifyUVars v1 v2 >> success
       | Just v1 <- projectU t1_c ->
           unifyUVar v1 t2_c >> success
       | Just v2 <- projectU t2_c ->
           unifyUVar v2 t1_c >> success

       -- Defer unification if possible
       -- Note, this must appear before structural unification
       | deferableU t1_c || deferableU t2_c ->
           return $ Just $ deferUnification t1_c t2_c

       -- Unify other terms
       | Just (cst, subterms, _) <- zipU t1_c t2_c ->
           unify_list cst subterms

       -- Unification failed
       | otherwise -> return Nothing
  where
    success = return $ Just mempty

    -- Unify all pairs.  Stop immediately if unification fails so that
    -- it's possible to generate a useful error message.
    unify_list cst pairs = go [cst] pairs
      where
        go rcsts ((t1, t2) : pairs) = unify t1 t2 >>= next
          where
            next (Just cst) = go (cst:rcsts) pairs
            next Nothing    = return Nothing
        go rcsts [] = return $ Just $ mconcat $ reverse rcsts

-- | Find a substitution and constraint that unifies the first term with the
--   second.
semiUnify :: NormalizeContext term m =>
             USubstitution term -> term -> term
          -> m (Maybe (USubstitution term, UConstraint term))
semiUnify subst t1 t2 = do
  t1_c <- normalize t1
  t2_c <- normalize t2
  case () of
    () | Just v <- projectU t1_c,
         Just t1' <- lookupUSubstitution v subst ->
           -- This term must match without further substitution
           require =<< uEqual t1' t2_c
       | Just v <- projectU t1_c ->
           -- This variable can be unified.  Unify it with t2_c
           let subst' = insertUSubstitution v t2_c subst
           in return $ Just (subst', mempty)

       -- Defer unification of the first term if possible
       | deferableU t1_c ->
           return $ Just (subst, deferUnification t1_c t2_c)

       -- Other terms must match
       | Just (cst, subterms, _) <- zipU t1_c t2_c ->
           unify_list cst subst subterms

       -- Semi-unification failed
       | otherwise -> return Nothing
  where
    require True  = return $ Just (subst, mempty)
    require False = return Nothing

    unify_list cst subst subterms = go [cst] subst subterms
      where
        go rcsts subst ((t1, t2) : pairs) = semiUnify subst t1 t2 >>= next
          where
            next (Just (subst', cst)) = go (cst:rcsts) subst' pairs
            next Nothing              = return Nothing
        go rcsts subst [] = return $ Just (subst, mconcat $ reverse rcsts)

match :: NormalizeContext term m =>
         term -> term -> m (Maybe (USubstitution term, UConstraint term))
match = semiUnify emptyUSubstitution

-- | Decide whether the terms are equal
uEqual :: NormalizeContext term m =>
          term -> term -> m Bool
uEqual t1 t2 = do
  t1_c <- normalize t1
  t2_c <- normalize t2
  case () of
    () | Just v1 <- projectU t1_c, Just v2 <- projectU t2_c ->
           return $ v1 == v2
       | Just (_, subterms, _) <- zipU t1_c t2_c ->
           allM (uncurry uEqual) subterms
       | otherwise ->
           return False

-- | Replace one type by another wherever it appears in the given type.
--   Return the substituted type and 'True' if any substitutions were made,
--   'False' otherwise.
substituteType :: NormalizeContext term m =>
                  term -> term -> term -> m (Bool, term)
substituteType old new ty = do
  ty_c <- normalize ty

  -- Substitute if type matches.  Otherwise, substitute in subexpressions.
  ifM (uEqual old ty_c) (return (True, new)) (subexpressions ty_c)

  where
    -- Perform substitution in subexpressions
    subexpressions t = do
      let (subterms, rebuild) = listU t
      (changed, subterms') <- mapAndUnzipM (substituteType old new) subterms
      return (or changed, rebuild subterms')

-------------------------------------------------------------------------------
-- Pretty-printing support

data PprContext term =
  PprContext
  { freshNames :: ![String]
  , typeNames :: !(Map.Map (Ident (UVar term)) String)

    -- | Names that have already been used
  , usedNames :: [String]
  }

initialPprContext = PprContext names Map.empty []
  where
    names = concatMap sequence $ drop 1 $ inits $ repeat ['a' .. 'z']

getUVarName :: PprContext term -> UVar term -> (String, PprContext term)
getUVarName ctx v
  | Just doc <- Map.lookup (_uID v) $ typeNames ctx =
      (doc, ctx)
  | otherwise =
      let n:ns = freshNames ctx -- Get a name
          ctx1 = ctx {freshNames = ns}
      in if n `elem` usedNames ctx1
         then getUVarName ctx1 v -- This name is used, try another 
         else let ctx' = ctx1 {typeNames = Map.insert (_uID v) n $
                                           typeNames ctx}
              in (n, ctx')

-- | Pick a name that doesn't conflict with any already-used names
decorateName :: PprContext term -> String -> (String, PprContext term)
decorateName ctx n = pick_name 0
  where
    pick_name index =
      let decorated_name = if index == 0 then n else n ++ show index
      in if decorated_name `elem` usedNames ctx
         then pick_name (index+1)
         else let ctx' = ctx {usedNames = decorated_name : usedNames ctx}
              in (decorated_name, ctx')