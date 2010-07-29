
module Untyped.CallConv
       (mergeSubstitutions,
        PassConvVar,
        newPCVar,
        unifyPCVar, unifyPCVars,
        canonicalizePassConv,
        anyPassConv,
        PassConv(..),
        PassConvCtor(..),
        applyPassConvCtor,
        CallConv(..),
        ExecMode(..)
       )
where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import Data.Function
import Data.IORef
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Traversable hiding(mapM)
import System.IO.Unsafe
import Text.PrettyPrint.HughesPJ

import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.MonadLogic
import Gluon.Common.Supply

import Untyped.HMType
import Untyped.Unification
import Untyped.Data

-- | Merge two substitutions, if the substitutions agree on their
-- common elements; return Nothing otherwise.
mergeSubstitutions :: Substitution -> Substitution -> IO (Maybe Substitution)
mergeSubstitutions s1 s2 = do
  mtc' <- merge (substTc s1) (substTc s2)
  case mtc' of
    Nothing  -> return Nothing
    Just tc' -> do
      mcc' <- merge (substCc s1) (substCc s2)
      case mcc' of
        Nothing -> return Nothing
        Just cc' -> return $ Just $ substitution tc' cc'
  where
    merge m1 m2 = mergeElements (Map.toAscList m1) (Map.toAscList m2) id

    prepend x tl = (x:) . tl

    -- Merge two ascending association lists.  The lists must agree on their
    -- common elements.  The 
    mergeElements (x1@(k1, v1):xs1) (x2@(k2, v2):xs2) tl =
      case compare k1 k2
      of LT -> mergeElements xs1 (x2:xs2) (prepend x1 tl)
         EQ -> do eq <- uEqual v1 v2
                  if eq
                    then mergeElements xs1 xs2 (prepend x1 tl)
                    else return Nothing
         GT -> mergeElements (x1:xs1) xs2 (prepend x2 tl)

    mergeElements xs1 [] tl =
      mergeElements [] [] ((xs1 ++) . tl)

    mergeElements [] xs2 tl =
      mergeElements [] [] ((xs2 ++) . tl)

    mergeElements [] [] merged_list =
      return $ Just $ Map.fromAscList $ merged_list []


-------------------------------------------------------------------------------

pcIDSupply :: Supply (Ident PassConvVar)
{-# NOINLINE pcIDSupply #-}
pcIDSupply = unsafePerformIO newIdentSupply

newPassConvID :: IO (Ident PassConvVar)
newPassConvID = supplyValue pcIDSupply

isNoRep NoPCRep = True
isNoRep _ = False

newPCVar :: IO PassConvVar
newPCVar = do
  n <- newPassConvID
  rep <- newIORef NoPCRep
  return $ PassConvVar n rep

-- | Create a new parameter-passing convention variable and return it as a 
-- parameter-passing convention.
anyPassConv :: IO PassConv
anyPassConv = do
  v <- newPCVar
  return $ By v

applyPassConvCtor :: PassConvCtor -> [HMType] -> PassConv
applyPassConvCtor (PassConvVal pc) [] = pc
applyPassConvCtor (PassConvFun f) (t:ts) = applyPassConvCtor (f t) ts
applyPassConvCtor _ _ = internalError "applyPassConvCtor: kind mismatch"

instance Type PassConv where
  freeTypeVariables pc = 
    case pc
    of ByRef -> return Set.empty
       ByClosure cc -> callConvFreeTypeVariables cc
       TuplePassConv pcs -> liftM Set.unions $ mapM freeTypeVariables pcs
       TypePassConv t -> freeTypeVariables t
       By _ -> return Set.empty

instance Type ExecMode where
  freeTypeVariables AsAction = return Set.empty
  freeTypeVariables AsStream = return Set.empty
  freeTypeVariables (PickExecMode t) = freeTypeVariables t
       
callConvFreeTypeVariables cc =
  case cc
  of pc :+> cc2 ->
       Set.union `liftM`
       freeTypeVariables pc `ap`
       callConvFreeTypeVariables cc2
     Return mode pc ->
       Set.union `liftM`
       freeTypeVariables mode `ap`
       freeTypeVariables pc

-------------------------------------------------------------------------------
-- Unification on parameter-passing conventions

-- | Convert a PC variable to a canonical expression
canonicalizePCVar :: PassConvVar -> IO PassConv
canonicalizePCVar v = do
  return . makeConv =<< canonicalizeRep (pcRep v)
  where
    makeConv NoPCRep       = By v
    makeConv (PCVarRep v') = By v'
    makeConv (PCRep x)     = x

canonicalizeRep :: IORef PassConvVarRep -> IO PassConvVarRep
canonicalizeRep rep_ref = do
  rep <- readIORef rep_ref
  case rep of
    NoPCRep    -> return rep
    PCVarRep v -> update_self rep =<< canonicalizeRep (pcRep v)
    PCRep t    -> return rep
  where
    update_self old_rep NoPCRep = return old_rep
    update_self _       new_rep = do writeIORef rep_ref new_rep
                                     return new_rep

isCanonicalPCVar :: PassConvVar -> IO Bool
isCanonicalPCVar v = do
  rep <- readIORef $ pcRep v
  return $ isNoRep rep

-- | Require a PC variable to be in canonical form
assertCanonicalPCVar :: PassConvVar -> IO ()
assertCanonicalPCVar v = do
  rep <- readIORef $ pcRep v
  unless (isNoRep rep) $ fail "Expecting a canonical parameter-passing convention variable"

-- | Unify two variables, which must be in canonical form
unifyPCVars :: PassConvVar -> PassConvVar -> IO ()
unifyPCVars v1 v2 = do
  assertCanonicalPCVar v1
  assertCanonicalPCVar v2
  writeIORef (pcRep v1) (PCVarRep v2)

unifyPCVar :: PassConvVar -> PassConv -> IO ()
unifyPCVar v c = do
  assertCanonicalPCVar v
  writeIORef (pcRep v) (PCRep c)

canonicalizePassConv :: PassConv -> IO PassConv
canonicalizePassConv (By v) = canonicalizePCVar v
canonicalizePassConv x      = return x

instance Unifiable PassConv where
  uShow pc = do
    pc' <- liftIO $ canonicalizePassConv pc
    case pc' of
      ByRef -> pure $ text "R"
      ByClosure cc -> parens . (text "C" <+>) <$> uShow cc 
      TuplePassConv ps -> parens . (sep . (text "Tuple":)) <$>
                          traverse uShow ps
      TypePassConv t -> parens . (text "Type" <+>) <$> uShow t
      By v -> pprGetPassConvVarName (pcID v)
  
  rename substitution pc = do
    pc' <- canonicalizePassConv pc
    case pc' of
      ByRef -> return pc'
      ByClosure cc -> ByClosure `liftM` rename substitution cc
      TuplePassConv pcs -> TuplePassConv `liftM` mapM (rename substitution) pcs
      TypePassConv ty -> TypePassConv `liftM` rename substitution ty
      By v -> return $ Map.findWithDefault pc' v (substCc substitution)

  unify pos t1 t2 = do
    t1_c <- canonicalizePassConv t1
    t2_c <- canonicalizePassConv t2
    
    case (t1_c, t2_c) of

      -- Unify variables
      (By v1, By v2) -> do unifyPCVars v1 v2
                           success
      (By v1, _)     -> do unifyPCVar v1 t2_c
                           success
      (_, By v2)     -> do unifyPCVar v2 t1_c
                           success

      -- Recurse on tuple constructors
      (TuplePassConv xs1, TuplePassConv xs2) 
        | length xs1 == length xs2 ->
          return $ zipWith EqPassConv xs1 xs2
        | otherwise -> internalError "inconsistent constraint"
        
      -- Generate equality constraints for functions
      (TypePassConv t1, TypePassConv t2) -> do
        eq <- uEqual t1 t2
        if eq then success else return [EqPassConv t1_c t2_c]
      (TypePassConv _, _) -> return [EqPassConv t1_c t2_c]
      (_, TypePassConv _) -> return [EqPassConv t1_c t2_c]

      -- Compare other terms
      (ByRef, ByRef) -> success
      (ByClosure c1, ByClosure c2) -> unify pos c1 c2
      _ -> failure
    where
      success = return []
      failure = do
        (t1, t2) <- runPpr $ (,) <$> uShow t1 <*> uShow t2
        let message = text "Calling convention mismatch: " $$
                      text "Expected" <+> nest 4 t1 $$
                      text "Observed" <+> nest 4 t2
        fail $ show message
  
  match t1 t2 = matchPCSubst emptySubstitution t1 t2

  uEqual t1 t2 = do
    t1_c <- canonicalizePassConv t1
    t2_c <- canonicalizePassConv t2
    
    case (t1_c, t2_c) of
      (By v1, By v2) -> require $ v1 == v2
      (ByRef, ByRef) -> success
      (ByClosure c1, ByClosure c2) -> uEqual c1 c2
      (TuplePassConv cs1, TuplePassConv cs2)
        | length cs1 == length cs2 ->
            allM (uncurry uEqual) (zip cs1 cs2)
        | otherwise ->
            internalError "inconsistent constraint"
      (TypePassConv t1, TypePassConv t2) ->
        uEqual t1 t2
      _ -> failure
    where
      success = return True
      failure = return False
      require True = success
      require False = failure

-- | Match parameter conventions, starting with the given substitution.
-- Find a substitution that makes t1 equal to t2.
matchPCSubst subst t1 t2 = do
  t1_c <- canonicalizePassConv t1
  t2_c <- canonicalizePassConv t2

  case (t1_c, t2_c) of
    (By v, _) ->
      -- Semi-unification; look up this variable in substitution
      case Map.lookup v (substCc subst)
      of Just new_v ->
           -- Match terms without further substitution
           require =<< uEqual new_v t2_c
         Nothing ->
           -- Add the mapping v |-> t2_c and succeed
           let subst' = updateCc (Map.insert v t2_c) subst
           in return (Just subst')
          
    -- Other terms must match exactly
    (ByRef, ByRef) -> success
    (ByClosure c1, ByClosure c2) -> matchCCSubst subst c1 c2
    (TuplePassConv cs1, TuplePassConv cs2) -> matchAllPCSubst subst cs1 cs2
    (TypePassConv t1, TypePassConv t2) -> do
      subst' <- match t1 t2
      case subst' of
        Nothing -> return Nothing
        Just s  -> mergeSubstitutions subst s
    _ -> failure
  where
    success = return (Just subst)
    failure = return Nothing
    require True = success
    require False = failure

matchAllPCSubst subst (x:xs) (y:ys) = do
  msubst <- matchPCSubst subst x y
  case msubst of
    Just subst' -> matchAllPCSubst subst' xs ys
    Nothing     -> return Nothing

matchAllPCSubst subst [] [] = return (Just subst)

matchAllPCSubst _ _ _ = internalError "inconsistent constraints"

-------------------------------------------------------------------------------
-- Unification on calling conventions

instance Unifiable CallConv where
  uShow cc = parens . sep <$> show_cc cc
    where
      show_cc (pc :+> cc) = build <$> uShow pc <*> show_cc cc
        where
          build x y = (x <+> text ":+>") : y
      show_cc (Return mode pc) = build <$> show_mode mode <*> uShow pc
        where
          show_mode AsAction = pure $ text "Action" 
          show_mode AsStream = pure $ text "Stream"
          show_mode (PickExecMode t) = parens . (text "Of" <+>) <$>
                                       uShow t
          build x y = [text "Return" <+> x <+> y]
  
  rename substitution cc =
    case cc
    of pc :+> cc'  -> (:+>) `liftM`
                      rename substitution pc `ap`
                      rename substitution cc'
       Return m pc -> Return `liftM`
                      rename substitution m `ap`
                      rename substitution pc

  unify pos t1 t2 =
    case (t1, t2) of
      (pc1 :+> cc1, pc2 :+> cc2) -> do
        unify pos pc1 pc2
        unify pos cc1 cc2
      (Return m1 pc1, Return m2 pc2) -> do
        unify pos m1 m2
        unify pos pc1 pc2
      _ -> fail "Calling convention mismatch"
  
  match t1 t2 = matchCCSubst emptySubstitution t1 t2
  
  uEqual t1 t2 =
    case (t1, t2) of
      (pc1 :+> cc1, pc2 :+> cc2) ->
        uEqual pc1 pc2 >&&> uEqual cc1 cc2
      (Return m1 pc1, Return m2 pc2) ->
        uEqual m1 m2 >&&> uEqual pc1 pc2
      _ -> return False

matchCCSubst subst t1 t2 =
  case (t1, t2) of
    (pc1 :+> cc1, pc2 :+> cc2) -> do
      msubst <- matchPCSubst subst pc1 pc2
      case msubst of
        Nothing -> return Nothing
        Just subst' -> matchCCSubst subst' cc1 cc2
    (Return m1 pc1, Return m2 pc2) -> do
      msubst <- matchExecMode subst m1 m2
      case msubst of
        Nothing -> return Nothing
        Just subst' -> matchPCSubst subst' pc1 pc2
    _ -> return Nothing

-------------------------------------------------------------------------------
-- Unification on execution modes

-- TODO: Eliminate ExecMode, it serves no purpose.
instance Unifiable ExecMode where
  uShow = internalError "Not implemented: uShow"
  
  unify pos m1 m2 =
    case (m1, m2)
    of (AsStream, AsStream) -> return []
       (AsAction, AsAction) -> return []
       (PickExecMode t1, PickExecMode t2) -> unify pos t1 t2
       _ -> fail "ExecMode.unify: Incompatible modes"

  rename substitution mode =
    case mode
    of AsAction -> return AsAction
       AsStream -> return AsStream
       PickExecMode t -> PickExecMode `liftM` rename substitution t


matchExecMode subst m1 m2 = do
  case (m1, m2) of
    (AsAction, AsAction) -> success
    (AsStream, AsStream) -> success
    _ -> failure 
  where
    success = return (Just subst)
    failure = fail "matchExecMode: not implemented for these inputs"