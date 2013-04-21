
{-# LANGUAGE FlexibleInstances, FlexibleContexts, StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -no-auto #-}
module SystemF.Rename
       (Subst(..),
        PartialSubst(..),
        ValAss(..),
        ValPartialSubst(..),
        renameMany,
        emptySubst,
        isEmptySubst,
        composeSubst,
        setTypeSubst, modifyTypeSubst,
        setValueSubst, modifyValueSubst,
        emptyPartialSubst,
        isEmptyPartialSubst,
        composePartialSubst,
        setTypePartialSubst, modifyTypePartialSubst,
        setValuePartialSubst, modifyValuePartialSubst,
        emptyV,
        lookupV,
        extendV,
        singletonV,
        fromListV,
        emptyPV,
        nullPV,
        singletonPV,
        fromListPV,
        extendPV,
        excludePV,
        lookupPV,
        renameMaybePatM,
        renamePatM,
        freshenMaybePatM,
        freshenPatM,
        renamePatMs,
        freshenPatMs,
        renameTyPat,
        renameTyPats,
        renameDeConInst,
        renameHeapMap,
        freshenDeConInst,
        renameDefGroup,
        deConFreeVariables,
        defGroupFreeVariables,
        substituteMaybePatM,
        substitutePatM,
        substitutePatMs,
        substituteTyPat,
        substituteTyPats,
        substituteDeConInst,
        substituteDefGroup,
        checkForShadowingExp,
        checkForShadowingExpSet,
        checkForShadowingExpHere,
        checkForShadowingModule)
where

import Prelude hiding(mapM, sequence)
import Control.Applicative
import Control.Monad hiding(mapM, sequence)
import Control.Monad.Reader hiding(mapM, sequence)
import qualified Data.IntSet as IntSet
import Data.List hiding(mapAccumL)
import Data.Maybe
import Data.Monoid
import qualified Data.IntMap as IntMap
import qualified Data.Set as Set
import Data.Traversable
import Debug.Trace

import Common.Error
import Common.Identifier
import Common.MonadLogic
import Common.Supply
import SystemF.Syntax
import SystemF.MemoryIR
import SystemF.PrintMemoryIR
import Type.Environment
import Type.Type
import Type.Rename(Renaming, Renameable(..),
                   checkForShadowingSet,
                   assertVarIsUndefined,
                   assertVarsAreUndefined,
                   CheckForShadowing)
import qualified Type.Rename as Rename
import Type.Substitute(TypeSubst,
                       SubstitutionMap(..),
                       Substitutable(..),
                       substitute)
import qualified Type.Substitute as Substitute

-- | A value assignment of a variable.
--
--   Variables may be renamed, or replaced by a new expression.
--   Renaming preserves information associated with a 'VarE' term.
data ValAss = RenamedVar !Var
            | SubstitutedVar !ExpM

newtype ValSubst = S {unS :: IntMap.IntMap ValAss}

emptyV :: ValSubst
emptyV = S IntMap.empty

nullV :: ValSubst -> Bool
nullV (S s) = IntMap.null s

singletonV :: Var -> ValAss -> ValSubst
singletonV v t = S (IntMap.singleton (fromIdent $ varID v) t)

fromListV :: [(Var, ValAss)] -> ValSubst
fromListV xs = S $ IntMap.fromList [(fromIdent $ varID v, t) | (v, t) <- xs]

-- | Compute the union of two substitutions on disjoint sets of variables.
--
--   Disjointness is not verified.
unionV :: ValSubst -> ValSubst -> ValSubst
unionV (S r1) (S r2) = S (IntMap.union r1 r2)

-- | @s2 `composeV` s1@ is a substitution equivalent to applying @s1@, then
--   applying @s2@.
composeV :: EvalMonad m => Subst -> ValSubst -> m ValSubst
s2 `composeV` s1 = do
  -- Apply s2 to the range of s1
  s1' <- traverse substitute_in_assignment (unS s1)

  -- Combine s1 and s2, preferring elements of s1
  return $ S $ IntMap.union s1' (unS $ valueSubst s2)
  where
    substitute_in_assignment ass@(RenamedVar v) =
      return $! case lookupV v (valueSubst s2)
                of Nothing   -> ass
                   Just ass' -> ass'
                   
    substitute_in_assignment (SubstitutedVar e) =
      liftM SubstitutedVar $ substitute s2 e

extendV :: Var -> ValAss -> ValSubst -> ValSubst
extendV v t (S s) = S (IntMap.insert (fromIdent $ varID v) t s)

excludeV :: Var -> ValSubst -> ValSubst
excludeV v (S s) = S (IntMap.delete (fromIdent $ varID v) s)

lookupV :: Var -> ValSubst -> Maybe ValAss
lookupV v (S m) = IntMap.lookup (fromIdent $ varID v) m

-------------------------------------------------------------------------------

-- | A partial substitution on values.
--   These partial substitutions are used for analysis information that cannot 
--   represent all possible values.  Unrepresentable values are 'Nothing'.
newtype ValPartialSubst = PS {unPS :: IntMap.IntMap (Maybe Var)}

emptyPV :: ValPartialSubst
emptyPV = PS IntMap.empty

nullPV :: ValPartialSubst -> Bool
nullPV (PS s) = IntMap.null s

singletonPV :: Var -> Maybe Var -> ValPartialSubst
singletonPV v t = PS (IntMap.singleton (fromIdent $ varID v) t)

fromListPV :: [(Var, Maybe Var)] -> ValPartialSubst
fromListPV xs = PS $ IntMap.fromList [(fromIdent $ varID v, t) | (v, t) <- xs]

-- | Compute the union of two substitutions on disjoint sets of variables.
--
--   Disjointness is not verified.
unionPV :: ValPartialSubst -> ValPartialSubst -> ValPartialSubst
unionPV (PS r1) (PS r2) = PS (IntMap.union r1 r2)

-- | @s2 `composeV` s1@ is a substitution equivalent to applying @s1@, then
--   applying @s2@.
composePV :: EvalMonad m => PartialSubst -> ValPartialSubst -> m ValPartialSubst
s2 `composePV` s1 = do
  -- Apply s2 to the range of s1
  s1' <- traverse substitute_in_assignment (unPS s1)

  -- Combine s1 and s2, preferring elements of s1
  return $ PS $ IntMap.union s1' (unPS $ partialValueSubst s2)
  where
    substitute_in_assignment ass@(Just v) =
      return $! case lookupPV v (partialValueSubst s2)
                of Nothing   -> ass
                   Just ass' -> ass'
                   
    substitute_in_assignment Nothing = return Nothing

extendPV :: Var -> Maybe Var -> ValPartialSubst -> ValPartialSubst
extendPV v t (PS s) = PS (IntMap.insert (fromIdent $ varID v) t s)

excludePV :: Var -> ValPartialSubst -> ValPartialSubst
excludePV v (PS s) = PS (IntMap.delete (fromIdent $ varID v) s)

lookupPV :: Var -> ValPartialSubst -> Maybe (Maybe Var)
lookupPV v (PS m) = IntMap.lookup (fromIdent $ varID v) m

-------------------------------------------------------------------------------

-- | A combined value and type substitution
data Subst = Subst {typeSubst :: !TypeSubst, valueSubst :: !ValSubst}

emptySubst = Subst Substitute.empty emptyV

isEmptySubst (Subst t v) = Substitute.null t && nullV v

composeSubst :: EvalMonad m =>
                Subst -> Subst -> m Subst
s2 `composeSubst` Subst ts1 vs1 = liftTypeEvalM $ do
  -- Compute the effect of applying vs1 followed by s2 on values
  vs1' <- s2 `composeV` vs1
  -- Compute the effect of applying ts1 followed by typeSubst s2 on types
  type_subst <- typeSubst s2 `Substitute.compose` ts1
  return $ Subst type_subst vs1'

setTypeSubst :: TypeSubst -> Subst -> Subst
setTypeSubst x s = s {typeSubst = x}

modifyTypeSubst :: (TypeSubst -> TypeSubst) -> Subst -> Subst
modifyTypeSubst f s = s {typeSubst = f $ typeSubst s}

setValueSubst :: ValSubst -> Subst -> Subst
setValueSubst x s = s {valueSubst = x}

modifyValueSubst :: (ValSubst -> ValSubst) -> Subst -> Subst
modifyValueSubst f s = s {valueSubst = f $ valueSubst s}

instance SubstitutionMap Subst where
  emptySubstitution = emptySubst
  isEmptySubstitution = isEmptySubst

-------------------------------------------------------------------------------

-- | A combined partial value and type substitution
data PartialSubst = PartialSubst
                    { partialTypeSubst :: !TypeSubst
                    , partialValueSubst :: !ValPartialSubst}

emptyPartialSubst = PartialSubst Substitute.empty emptyPV

-- | Convert a 'Subst' to a 'PartialSubst'.  All unrepresentable values become
--   'Nothing'.
mkPartialSubst :: Subst -> PartialSubst
mkPartialSubst (Subst ts vs) = let partial_vs = IntMap.map to_partial (unS vs)
                               in PartialSubst ts (PS partial_vs)
  where
    to_partial (RenamedVar v)     = Just v
    to_partial (SubstitutedVar _) = Nothing
    

isEmptyPartialSubst (PartialSubst t v) = Substitute.null t && nullPV v

composePartialSubst :: EvalMonad m =>
                       PartialSubst -> PartialSubst -> m PartialSubst
s2 `composePartialSubst` PartialSubst ts1 vs1 = liftTypeEvalM $ do
  -- Compute the effect of applying vs1 followed by s2 on values
  vs1' <- s2 `composePV` vs1
  -- Compute the effect of applying ts1 followed by typeSubst s2 on types
  type_subst <- partialTypeSubst s2 `Substitute.compose` ts1
  return $ PartialSubst type_subst vs1'

setTypePartialSubst :: TypeSubst -> PartialSubst -> PartialSubst
setTypePartialSubst x s = s {partialTypeSubst = x}

modifyTypePartialSubst :: (TypeSubst -> TypeSubst) -> PartialSubst -> PartialSubst
modifyTypePartialSubst f s = s {partialTypeSubst = f $ partialTypeSubst s}

setValuePartialSubst :: ValPartialSubst -> PartialSubst -> PartialSubst
setValuePartialSubst x s = s {partialValueSubst = x}

modifyValuePartialSubst :: (ValPartialSubst -> ValPartialSubst)
                        -> PartialSubst -> PartialSubst
modifyValuePartialSubst f s = s {partialValueSubst = f $ partialValueSubst s}

instance SubstitutionMap PartialSubst where
  emptySubstitution = emptyPartialSubst
  isEmptySubstitution = isEmptyPartialSubst

-------------------------------------------------------------------------------

renameMany :: (st -> a -> (st -> a -> b) -> b)
           -> st -> [a] -> (st -> [a] -> b) -> b
renameMany f rn (x:xs) k =
  f rn x $ \rn' x' -> renameMany f rn' xs $ \rn'' xs' -> k rn'' (x':xs')

renameMany _ rn [] k = k rn []

-- | Apply a renaming to a type pattern. If necessary, rename the pattern
--   variable to avoid name shadowing.
renameTyPat :: Renaming -> TyPat -> (Renaming -> TyPat -> a) -> a
renameTyPat rn (TyPat binder) k =
  Rename.renameBinder rn binder $ \rn' binder' ->
  k rn' (TyPat binder')

renameTyPats = renameMany renameTyPat

-- | Apply a renaming to a pattern.  If necessary, rename the pattern
--   variable to avoid name shadowing.
renamePatM :: Renaming -> PatM -> (Renaming -> PatM -> a) -> a
renamePatM rn (PatM binding uses) k =
  Rename.renameBinder rn binding $ \rn' binding' ->
  k rn' (PatM binding' (rename rn uses))

renameMaybePatM rn Nothing k = k rn Nothing
renameMaybePatM rn (Just p) k = renamePatM rn p $ \rn' p' -> k rn' (Just p')

freshenMaybePatM Nothing = return (Nothing, Rename.empty)
freshenMaybePatM (Just p) = do (p', rn) <- freshenPatM p
                               return (Just p', rn)

-- | Replace the pattern variable with a fresh name
freshenPatM :: Supplies m (Ident Var) => PatM -> m (PatM, Renaming)
freshenPatM pat = do
  let old_var = patMVar pat
      ty = patMType pat
      dmd = patMDmd pat
  new_var <- newClonedVar old_var
  return (setPatMDmd dmd $ patM (new_var ::: ty),
          Rename.singleton old_var new_var)

freshenPatMs :: Supplies m (Ident Var) => [PatM] -> m ([PatM], Renaming)
freshenPatMs pats = do
  (pats', rns) <- mapAndUnzipM freshenPatM pats
  return (pats', foldr Rename.union Rename.empty rns)

renamePatMs :: Renaming -> [PatM] -> (Renaming -> [PatM] -> a) -> a
renamePatMs = renameMany renamePatM

renameDefGroup :: Renaming
               -> DefGroup (FDef Mem)
               -> (Renaming -> DefGroup (FDef Mem) -> a)
               -> a
renameDefGroup rn group k =
  -- Rename the function definitions and exclude bound variables from the
  -- renaming process
  case group
  of NonRec def ->
       let def' = rename_def rn def
           rn' = Rename.exclude (definiendum def) rn
       in k rn' (NonRec def')
     Rec defs ->
       let rn' = foldr Rename.exclude rn $ map definiendum defs
           defs' = map (rename_def rn') defs
       in k rn' (Rec defs')
  where
  rename_def rn def =
    def {definiens = rename rn $ definiens def}

defGroupFreeVariables :: DefGroup (FDef Mem) -> Set.Set Var -> Set.Set Var
defGroupFreeVariables (NonRec def) fv =
  freeVariables (definiens def) `Set.union` Set.delete (definiendum def) fv
  
defGroupFreeVariables (Rec defs) fv =
  let group_fv = freeVariables (map definiens defs) `Set.union` fv
  in foldr Set.delete group_fv (map definiendum defs)

renameDeConInst :: Renaming -> DeConInst -> (Renaming -> DeConInst -> a) -> a
renameDeConInst rn decon k =
  case decon
  of VarDeCon op ty_args ex_types ->
       let ty_args' = rename rn ty_args
       in Rename.renameBinders rn ex_types $ \rn' ex_types' ->
          k rn' (VarDeCon op ty_args' ex_types')
     TupleDeCon ty_args ->
       let ty_args' = rename rn ty_args
       in k rn (TupleDeCon ty_args')

-- | Rename each bound variable to a fresh name
freshenDeConInst :: (Supplies m (Ident Var)) =>
                    DeConInst -> m (DeConInst, Renaming)
freshenDeConInst decon =
  case decon
  of VarDeCon con ty_args ex_types -> do
       new_vars <- mapM (newClonedVar . binderVar) ex_types
       let renaming = Rename.fromList $ zip (map binderVar ex_types) new_vars
           ex_types' = [v ::: t | (v, _ ::: t) <- zip new_vars ex_types]
       return (VarDeCon con ty_args ex_types', renaming)
     TupleDeCon _ ->
       return (decon, Rename.empty)

deConFreeVariables :: DeConInst -> Set.Set Var -> Set.Set Var
deConFreeVariables (VarDeCon op ty_args ex_types) fv =
  let ex_fv = foldr Set.delete fv [a | a ::: _ <- ex_types]
      type_fv = freeVariables $ ty_args ++ [t | _ ::: t <- ex_types]
  in Set.union ex_fv type_fv

deConFreeVariables (TupleDeCon ty_args) fv =
  Set.union (freeVariables ty_args) fv

substituteTypeBinder :: EvalMonad m =>
                        Subst -> Binder
                     -> (Subst -> Binder -> m a)
                     -> m a
substituteTypeBinder s binder k =
  Substitute.substituteBinder (typeSubst s) binder $ \ts' binder' ->
  k (setTypeSubst ts' s) binder'

substituteTypeBinders :: EvalMonad m =>
                         Subst -> [Binder]
                      -> (Subst -> [Binder] -> m a)
                      -> m a
substituteTypeBinders = renameMany substituteTypeBinder

-- | Apply a substitution to a type pattern
substituteTyPat :: EvalMonad m =>
                   Subst -> TyPat
                -> (Subst -> TyPat -> m a)
                -> m a
substituteTyPat s (TyPat binder) k =
  substituteTypeBinder s binder $ \s' binder' -> k s' (TyPat binder')

substituteTyPats :: EvalMonad m =>
                    Subst -> [TyPat]
                 -> (Subst -> [TyPat] -> m a)
                 -> m a
substituteTyPats = renameMany substituteTyPat
  
-- | Apply a substitution to a binder that binds a value to a variable.
--
-- See 'substituteBinder'.
substituteValueBinder :: EvalMonad m =>
                         Subst -> Binder
                       -> (Subst -> Binder -> m a)
                       -> m a
substituteValueBinder s (x ::: t) k = do
  t' <- substitute (typeSubst s) t
  
  -- Is the bound variable in scope?
  type_assignment <- lookupType x
  case type_assignment of
    Nothing -> do
      -- Not in scope: remove from the substitution.
      -- This seems unnecessary, but can happen --
      -- "Secrets of the GHC Inliner" section 3.2.
      let s' = modifyValueSubst (excludeV x) s
      assume x t' $ k s' (x ::: t')
    Just _  -> do
      -- In scope: rename and add to the substitution
      x' <- newClonedVar x
      let s' = modifyValueSubst (extendV x (RenamedVar x')) s
      assume x' t' $ k s' (x' ::: t')

substituteMaybePatM s Nothing  k = k s Nothing
substituteMaybePatM s (Just p) k =
  substitutePatM s p $ \s' p' -> k s' (Just p')

-- | Apply a substitution to a pattern
substitutePatM :: EvalMonad m =>
                  Subst -> PatM -> (Subst -> PatM -> m a) -> m a
substitutePatM s (PatM binder uses) k = do
  uses' <- substitute (mkPartialSubst s) uses
  substituteValueBinder s binder $ \s' binder' -> k s' (PatM binder' uses')

substitutePatMs :: EvalMonad m =>
                   Subst -> [PatM] -> (Subst -> [PatM] -> m a) -> m a
substitutePatMs = renameMany substitutePatM

substituteDefGroup :: forall m a s. EvalMonad m =>
                      (Subst -> Fun Mem -> m (Fun s))
                      -- ^ How to perform substitution on a function
                   -> Subst     -- ^ Substitution to apply
                   -> DefGroup (FDef Mem) -- ^ Definition group
                   -> (Subst -> DefGroup (FDef s) -> m a)
                      -- ^ Code over which the definitions are in scope
                   -> m a
substituteDefGroup subst_fun s g k =
  case g
  of NonRec def -> do
       -- Get function type
       fun_type <- substitute (typeSubst s) $ functionType (definiens def)

       -- No new variables in scope over function body
       def1 <- mapMDefiniens (subst_fun s) def
       
       -- Rename the bound variable if appropriate
       (s', v') <- rename_if_bound s (definiendum def)
       let def' = def1 {definiendum = v'}
       
       -- Add function to environment
       assume v' fun_type $ k s' (NonRec def')

     Rec defs -> do
       -- Get the functions' types.  Function types cannot refer to
       -- local variables.
       function_types <-
         mapM (substitute (typeSubst s) . functionType . definiens) defs

       -- Rename variables that shadow existing names
       let definienda = map definiendum defs
       (s', renamed_definienda) <- mapAccumM rename_if_bound s definienda

       -- Rename functions
       assumeBinders (zipWith (:::) renamed_definienda function_types) $ do
         defs' <- mapM (mapMDefiniens (subst_fun s')) defs
         let new_defs = [def {definiendum = v}
                        | (def, v) <- zip defs' renamed_definienda]
         k s' (Rec new_defs)
  where
    rename_if_bound :: Subst -> Var -> m (Subst, Var)
    rename_if_bound s v = do
       type_assignment <- lookupType v
       case type_assignment of
         Nothing ->
           let s' = modifyValueSubst (excludeV v) s
           in return (s', v)
         Just _ -> do
           v' <- newClonedVar v
           let s' = modifyValueSubst (extendV v (RenamedVar v')) s
           return (s', v')

substituteDeConInst :: (EvalMonad m) =>
                       TypeSubst -> DeConInst
                    -> (TypeSubst -> DeConInst -> m a)
                    -> m a 
substituteDeConInst s decon k =
  case decon
  of VarDeCon con ty_args ex_types -> do
       ty_args' <- mapM (substitute s) ty_args
       Substitute.substituteBinders s ex_types $ \s' ex_types' ->
         k s' (VarDeCon con ty_args' ex_types')
     TupleDeCon ty_args -> do
       ty_args' <- mapM (substitute s) ty_args
       k s (TupleDeCon ty_args')
       
-------------------------------------------------------------------------------
       
-- | A 'Dmd' can be renamed by renaming its specificity.
--   The 'multiplicity' field does not mention variable names.
instance Renameable Dmd where
  rename rn dmd = dmd {specificity = rename rn $ specificity dmd}
  freeVariables dmd = freeVariables $ specificity dmd

instance Substitutable Dmd where
  type Substitution Dmd = PartialSubst
  substituteWorker s dmd = do
    spc <- substituteWorker s $ specificity dmd
    return $ Dmd (multiplicity dmd) spc

instance Renameable Specificity where
  rename rn spc =
    case spc
    of Decond decon spcs ->
         renameDeConInst rn decon $ \rn' decon' ->
         let spcs' = rename rn' spcs
         in Decond decon' spcs'

       Written v m -> 
         -- Remove the bound variable from the environment; it is shadowed
         let rn' = Rename.exclude v rn
         in Written v (renameHeapMap rn' m)

       Read m -> Read $ renameHeapMap rn m
       
       -- Other constructors don't mention variables
       _ -> spc

  freeVariables spc =
    case spc
    of Used              -> Set.empty
       Inspected         -> Set.empty
       Copied            -> Set.empty
       Decond decon spcs -> deConFreeVariables decon $ freeVariables spcs
       Written v spc     -> Set.delete v $ fvHeapMap spc
       Unused            -> Set.empty

renameHeapMap :: Renameable a => Renaming -> HeapMap a -> HeapMap a
renameHeapMap rn (HeapMap xs) = HeapMap $ map rename_assoc xs
  where rename_assoc (addr, val) =
          (fromMaybe addr $ Rename.lookup addr rn, rename rn val)

fvHeapMap (HeapMap xs) =
  Set.unions [Set.insert v $ freeVariables s | (v, s) <- xs]

instance Substitutable Specificity where
  type Substitution Specificity = PartialSubst
  substituteWorker s spc =
    case spc
    of Decond decon spcs ->
         substituteDeConInst (partialTypeSubst s) decon $ \ts' decon' -> do
           let s' = setTypePartialSubst ts' s
           spcs' <- mapM (substitute s') spcs
           return $ Decond decon' spcs'
       
       Written v heap_map -> do
         -- Rename 'v' if it's in scope
         type_assignment <- lookupType v
         (s', v') <- case type_assignment of
           Nothing -> return (modifyValuePartialSubst (excludePV v) s, v)
           Just _  -> do
             v' <- newClonedVar v
             let s' = modifyValuePartialSubst (extendPV v (Just v')) s
             return (s', v')

         -- Substitute the rest
         m_heap_map' <- substituteHeapMap s' heap_map
         return $! case m_heap_map'
                   of Just heap_map' -> Written v' heap_map'
                      Nothing        -> Used -- Not representable

       Read _ -> internalError "substitute: Not implemented"
       
       -- Other terms don't mention variables
       Used -> return spc
       Inspected -> return spc
       Copied -> return spc
       Unused -> return spc

substituteHeapMap :: EvalMonad m =>
                     PartialSubst -> HeapMap Specificity
                  -> m (Maybe (HeapMap Specificity))
substituteHeapMap s (HeapMap xs) = do 
  substituted_entries <- mapM substitute_entry xs
  return $ fmap HeapMap $ sequence substituted_entries
  where
    substitute_entry (k, spc) =
      -- Try to rename 'k'
      case lookupPV k $ partialValueSubst s
      of Just (Just v') -> continue v'
         Just Nothing   -> return Nothing
         Nothing        -> continue k
      where
        continue k' = do
          spc' <- substitute s spc
          return $ Just (k', spc')

instance Renameable ConInst where
  rename rn (VarCon con ty_args ex_types) =
    let ty_args' = rename rn ty_args
        ex_types' = rename rn ex_types
    in VarCon con ty_args' ex_types'
  rename rn (TupleCon ty_args) =
    let ty_args' = rename rn ty_args
    in TupleCon ty_args'

  freeVariables con = freeVariables $ conTypes con

instance Renameable (Exp Mem) where
  rename rn (ExpM expression) = ExpM $
    {-# SCC "Renameable/Exp.rename" #-}
    case expression
    of VarE inf v ->
         case Rename.lookup v rn
         of Just v' -> VarE inf v'
            Nothing -> expression
       LitE {} -> expression
       ConE inf op ty_ob sps args ->
         ConE inf (rename rn op) (rename rn ty_ob) (rename rn sps) (rename rn args)
       AppE inf op ts es ->
         AppE inf (rename rn op) (rename rn ts) (rename rn es)
       LamE inf f ->
         LamE inf (rename rn f)
       LetE inf p val body ->
         renamePatM rn p $ \rn' p' ->
         LetE inf p' (rename rn val) (rename rn' body)
       LetfunE inf defs body ->
         renameDefGroup rn defs $ \rn' defs' ->
         LetfunE inf defs' (rename rn' body)
       CaseE inf scr sps alts ->
         CaseE inf (rename rn scr) (rename rn sps) (rename rn alts)
       ExceptE inf rty ->
         ExceptE inf (rename rn rty)
       CoerceE inf t1 t2 e ->
         CoerceE inf (rename rn t1) (rename rn t2) (rename rn e)
       ArrayE inf ty es ->
         ArrayE inf (rename rn ty) (rename rn es)

  freeVariables (ExpM expression) =
    {-# SCC "Renameable/Exp.freeVariables" #-}
    case expression
    of VarE _ v -> Set.singleton v
       LitE _ _ -> Set.empty
       ConE _ op ty_ob sps args ->
         freeVariables op `Set.union`
         freeVariables ty_ob `Set.union`
         freeVariables sps `Set.union`
         freeVariables args
       AppE _ op ty_args args -> Set.union (freeVariables op) $
                                 Set.union (freeVariables ty_args) $
                                 freeVariables args
       LamE _ f -> freeVariables f
       LetE _ pat rhs body ->
         let use_fv = freeVariables $ patMDmd pat
         in freeVariables rhs `Set.union`
            Rename.binderFreeVariables (patMBinder pat) (freeVariables body)
       LetfunE _ defs body -> 
         defGroupFreeVariables defs $ freeVariables body
       LetfunE _ (Rec defs) body ->
         let local_functions = map definiendum defs
             fn_fv = Set.unions $ map (freeVariables . definiens) defs
             body_fv = freeVariables body
         in foldr Set.delete (Set.union fn_fv body_fv) local_functions
       CaseE _ scr sps alts ->
         freeVariables scr `Set.union` freeVariables sps `Set.union` freeVariables alts
       ExceptE _ rty ->
         freeVariables rty
       CoerceE _ t1 t2 e ->
         freeVariables t1 `Set.union` freeVariables t2 `Set.union` freeVariables e
       ArrayE _ ty es ->
         freeVariables ty `Set.union` freeVariables es

instance Renameable (Alt Mem) where
  rename rn (AltM (Alt con ty_ob params body)) =
    renameDeConInst rn con $ \rn' con' ->
    renameMaybePatM rn' ty_ob $ \rn'' ty_ob' ->
    renamePatMs rn'' params $ \rn''' params' ->
    AltM $ Alt con' ty_ob' params' (rename rn''' body)

  freeVariables (AltM (Alt decon ty_ob params body)) =
    deConFreeVariables decon $
    let uses_fv = freeVariables (map patMDmd params) `Set.union`
                  freeVariables (fmap patMDmd ty_ob)
        params_fv = Rename.bindersFreeVariables (map patMBinder params) $
                    maybe id (Rename.binderFreeVariables . patMBinder) ty_ob $
                    freeVariables body
    in Set.union uses_fv params_fv

instance Renameable (Fun Mem) where
  rename rn (FunM fun) =
    renameTyPats rn (funTyParams fun) $ \rn' ty_params -> 
    renamePatMs rn' (funParams fun) $ \rn'' params ->
    let ret = rename rn'' $ funReturn fun
        body = rename rn'' $ funBody fun
    in FunM $ Fun { funInfo = funInfo fun
                  , funTyParams = ty_params
                  , funParams = params
                  , funReturn = ret
                  , funBody = body}

  freeVariables (FunM fun) =
    Rename.bindersFreeVariables [p | TyPat p <- funTyParams fun] $
    let uses_fv = freeVariables (map patMDmd $ funParams fun)
        params_fv = Rename.bindersFreeVariables (map patMBinder $ funParams fun) $
                    freeVariables (funBody fun) `Set.union`
                    freeVariables (funReturn fun)
    in Set.union uses_fv params_fv

instance Substitutable ConInst where
  type Substitution ConInst = TypeSubst
  substituteWorker s (VarCon op ty_args ex_types) =
    VarCon op `liftM`
    mapM (substitute s) ty_args `ap`
    mapM (substitute s) ex_types

  substituteWorker s (TupleCon ty_args) =
    TupleCon `liftM` mapM (substitute s) ty_args

instance Substitutable (Exp Mem) where
  type Substitution (Exp Mem) = Subst
  substituteWorker s (ExpM expression) =
    {-# SCC "Substitutable/Exp.substituteWorker" #-}
    case expression
    of VarE inf v ->
         case lookupV v $ valueSubst s
         of Just (RenamedVar v')    -> return (ExpM (VarE inf v'))
            Just (SubstitutedVar e) -> return e
            Nothing                 -> return (ExpM expression)
       LitE {} -> return (ExpM expression)
       ConE inf con ty_ob sps args -> do
         con' <- substitute (typeSubst s) con
         ty_ob' <- substitute s ty_ob
         sps' <- substitute s sps
         args' <- substitute s args
         return $ ExpM $ ConE inf con' ty_ob' sps' args'
       AppE inf op ts es -> do
         op' <- substitute s op
         ts' <- substitute (typeSubst s) ts
         es' <- substitute s es
         return $ ExpM $ AppE inf op' ts' es'
       LamE inf f -> do
         f' <- substitute s f
         return $ ExpM $ LamE inf f'
       LetE inf p val body -> do
         val' <- substitute s val
         substitutePatM s p $ \s' p' -> do
           body' <- substitute s' body
           return $ ExpM $ LetE inf p' val' body'
       LetfunE inf defs body ->
         substituteDefGroup substitute s defs $ \s' defs' -> do
           body' <- substitute s' body
           return $ ExpM $ LetfunE inf defs' body'
       CaseE inf scr sps alts -> do
         scr' <- substitute s scr
         sps' <- substitute s sps
         alts' <- mapM (substitute s) alts
         return $ ExpM $ CaseE inf scr' sps' alts'
       ExceptE inf ty -> do
         ty' <- substitute (typeSubst s) ty
         return $ ExpM $ ExceptE inf ty'
       CoerceE inf t1 t2 e -> do
         t1' <- substitute (typeSubst s) t1
         t2' <- substitute (typeSubst s) t2
         e' <- substitute s e
         return $ ExpM $ CoerceE inf t1' t2' e'
       ArrayE inf ty es -> do
         ty' <- substitute (typeSubst s) ty
         es' <- substitute s es
         return $ ExpM $ ArrayE inf ty' es'

instance Substitutable (Alt Mem) where
  type Substitution (Alt Mem) = Subst
  substituteWorker s (AltM (Alt con ty_ob params body)) =
    substituteDeConInst (typeSubst s) con $ \ts' con' ->
    substituteMaybePatM (setTypeSubst ts' s) ty_ob $ \s' ty_ob' -> do
    substitutePatMs s' params $ \s'' params' -> do
      body' <- substitute s'' body
      return $ AltM $ Alt con' ty_ob' params' body'

instance Substitutable (Fun Mem) where
  type Substitution (Fun Mem) = Subst
  substituteWorker s (FunM fun) =
    substituteTyPats s (funTyParams fun) $ \s' ty_params ->
    substitutePatMs s' (funParams fun) $ \s'' params -> do
      body <- substitute s'' $ funBody fun
      ret <- substitute (typeSubst s'') $ funReturn fun
      return $ FunM $ Fun { funInfo = funInfo fun
                          , funTyParams = ty_params
                          , funParams = params
                          , funReturn = ret
                          , funBody = body}

-------------------------------------------------------------------------------

-- | Search for instances of name shadowing in the expression.
--   If found, raise an exception.
checkForShadowingExp :: ITypeEnvBase a -> ExpM -> ()
checkForShadowingExp tenv e =
  let all_kinds = getAllKinds tenv
  in checkForShadowingExpSet (IntMap.keysSet all_kinds) e

checkForShadowingExpSet :: CheckForShadowing ExpM
checkForShadowingExpSet in_scope e =
  {-# SCC checkForShadowingExpSet #-}
  case fromExpM e
  of VarE {} -> ()
     LitE {} -> ()
     ConE _ con sps ty_ob args ->
       checkForShadowingConSet in_scope con `seq`
       continues sps `seq`
       maybe () continue ty_ob `seq`
       continues args
     AppE _ op ty_args args ->
       continue op `seq`
       (foldr seq () $ map (checkForShadowingSet in_scope) ty_args) `seq`
       continues args
     LamE _ f ->
       checkForShadowingFunSet in_scope f
     LetE _ pat rhs body ->
       assertVarIsUndefined in_scope (patMVar pat) `seq`
       continue rhs `seq`
       checkForShadowingSet in_scope (patMType pat) `seq`
       checkForShadowingExpSet (insert (patMVar pat) in_scope) body
     LetfunE _ defs body ->
       checkForShadowingGroupSet checkForShadowingFunSet checkForShadowingExpSet body in_scope defs
     CaseE _ scr sps alts ->
       continue scr `seq`
       continues sps `seq`
       (foldr seq () $ map (checkForShadowingAltSet in_scope) alts)
     ExceptE _ ty ->
       checkForShadowingSet in_scope ty
     CoerceE _ t1 t2 body ->
       checkForShadowingSet in_scope t1 `seq`
       checkForShadowingSet in_scope t2 `seq`
       continue body
     ArrayE _ ty es ->
       checkForShadowingSet in_scope ty `seq`
       continues es
  where
    continue e = checkForShadowingExpSet in_scope e
    continues es = foldr seq () $ map continue es
    insert v scope = IntSet.insert (fromIdent $ varID v) scope

checkForShadowingGroupSet :: CheckForShadowing (t Mem)
                          -> CheckForShadowing a
                          -> a
                          -> CheckForShadowing (DefGroup (Def t Mem))
checkForShadowingGroupSet check_def check body in_scope defs =
  let definienda = map definiendum $ defGroupMembers defs
      definientia = map definiens $ defGroupMembers defs
      augmented_scope = inserts definienda in_scope
      
      -- Determine which variables are in scope over the function
      -- definitions 
      local_scope =
        case defs
        of NonRec _ -> in_scope
           Rec _    -> augmented_scope
  in assertVarsAreUndefined in_scope definienda `seq`
     (foldr seq (check augmented_scope body) $
      map (check_def local_scope) definientia)
  where
    insert v scope = IntSet.insert (fromIdent $ varID v) scope
    inserts vs scope = foldr insert scope vs

checkForShadowingConSet :: CheckForShadowing ConInst
checkForShadowingConSet in_scope con =
  foldr seq () $ map (checkForShadowingSet in_scope) (conTypes con)

checkForShadowingDeConSet :: CheckForShadowing DeConInst
checkForShadowingDeConSet in_scope con =
  assertVarsAreUndefined in_scope [v | v ::: _ <- deConExTypes con] `seq`
  (foldr seq () $ map (checkForShadowingSet in_scope) types)
  where
    types = deConTyArgs con ++ [k | _ ::: k <- deConExTypes con]

checkForShadowingFunSet :: CheckForShadowing FunM
checkForShadowingFunSet in_scope (FunM (Fun _ typarams params return body)) =
  let ty_vars = map tyPatVar typarams
      kinds = map tyPatKind typarams
      ty_scope = inserts ty_vars in_scope
      param_vars = map patMVar params
      param_types = map patMType params
      body_scope = inserts param_vars ty_scope
  in (foldr seq () $ map (checkForShadowingSet in_scope) kinds) `seq`
     assertVarsAreUndefined in_scope ty_vars `seq`
     (foldr seq () $ map (checkForShadowingSet ty_scope) param_types) `seq` 
     assertVarsAreUndefined ty_scope param_vars `seq`
     checkForShadowingSet body_scope return `seq`
     checkForShadowingExpSet body_scope body
  where
    insert v scope = IntSet.insert (fromIdent $ varID v) scope
    inserts vs scope = foldr insert scope vs

checkForShadowingDataSet in_scope (Constant inf ty e) =
  checkForShadowingSet in_scope ty `seq`
  checkForShadowingExpSet in_scope e

checkForShadowingGlobalDefSet :: CheckForShadowing (Ent Mem)
checkForShadowingGlobalDefSet in_scope (FunEnt f) =
  checkForShadowingFunSet in_scope f

checkForShadowingGlobalDefSet in_scope (DataEnt d) =
  checkForShadowingDataSet in_scope d

checkForShadowingAltSet :: CheckForShadowing AltM
checkForShadowingAltSet in_scope (AltM (Alt decon ty_ob params body)) =
  let ex_vars = map binderVar $ deConExTypes decon
      kinds = deConTyArgs decon ++ map binderType (deConExTypes decon)
      ty_scope = inserts ex_vars in_scope
      param_vars = map patMVar params
      param_types = map patMType params
      body_scope = inserts param_vars ty_scope
  in (foldr seq () $ map (checkForShadowingSet in_scope) kinds) `seq`
     assertVarsAreUndefined in_scope ex_vars `seq`
     (foldr seq () $ map (checkForShadowingSet ty_scope) param_types) `seq` 
     assertVarsAreUndefined ty_scope param_vars `seq`
     checkForShadowingExpSet body_scope body
  where
    insert v scope = IntSet.insert (fromIdent $ varID v) scope
    inserts vs scope = foldr insert scope vs

-- | Check whether any variables from the current type environment
--   are shadowed in the expression
checkForShadowingExpHere :: TypeEnvMonad m => ExpM -> m ()
checkForShadowingExpHere e = do
  tenv <- freezeTypeEnv
  return $! checkForShadowingExp tenv e

checkForShadowingModule :: Module Mem -> ()
checkForShadowingModule (Module _ imports defss exports) =
  {-# SCC checkForShadowingModule #-}
  checkForShadowingGroupSet
  checkForShadowingGlobalDefSet check_globals defss IntSet.empty (Rec imports)
  where
    check_globals env (defs : defss) =
      checkForShadowingGroupSet checkForShadowingGlobalDefSet check_globals defss env defs
    
    check_globals env [] =
      foldr seq () $ map (checkForShadowingFunSet env . exportFunction) exports