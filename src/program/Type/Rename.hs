
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
module Type.Rename where

import Prelude hiding(mapM)
import Control.Monad hiding(mapM)
import Data.Maybe
import Data.Monoid
import Data.Traversable(traverse, mapM)

import Common.Identifier
import Common.Supply
import Type.Type
import Type.Environment

import qualified Data.IntMap as IntMap
import qualified Data.Set as Set

newtype Renaming = R {unR :: IntMap.IntMap Var}

instance Monoid Renaming where
  mempty = R mempty
  mappend x y = R (mappend (unR x) (unR y))

renaming :: [(Var, Var)] -> Renaming
renaming xs = R $ IntMap.fromList [(fromIdent $ varID v1, v2) | (v1, v2) <- xs]

singletonRenaming :: Var -> Var -> Renaming
singletonRenaming v1 v2 = renaming [(v1, v2)]

insertRenaming :: Var -> Var -> Renaming -> Renaming
insertRenaming v1 v2 (R rn) = R $ IntMap.insert (fromIdent $ varID v1) v2 rn

renameVar :: Var -> Renaming -> Maybe Var
renameVar v (R m) = IntMap.lookup (fromIdent $ varID v) m

renameBinding :: Renaming -> Binder -> (Renaming -> Binder -> a) -> a
renameBinding rn (x ::: t) k =
  -- Remove the bound variable from the environment; it is shadowed  
  let rn' = R $ IntMap.delete (fromIdent $ varID x) (unR rn)
  in k rn' (x ::: rename rn t)

class Renameable a where
  -- | Rename an expression using the given renaming
  rename :: Renaming -> a -> a
  
  -- | Rename variables bound in the outermost term to new, fresh names
  freshen :: (Monad m, Supplies m VarID) => a -> m a
  
  -- | Find the variables that are used in, but not defined in, the expression
  freeVariables :: a -> Set.Set Var

instance Renameable a => Renameable (Maybe a) where
  rename rn x = fmap (rename rn) x
  freshen Nothing  = return Nothing
  freshen (Just x) = liftM Just $ freshen x
  freeVariables x = maybe Set.empty freeVariables x

instance Renameable a => Renameable [a] where
  rename rn xs = map (rename rn) xs
  freshen xs = mapM freshen xs
  freeVariables xs = Set.unions $ map freeVariables xs

instance Renameable Var where
  rename rn v = fromMaybe v $ renameVar v rn
  freshen v = return v
  freeVariables v = Set.singleton v

instance Renameable Type where
  rename rn ty =
    case ty
    of VarT v           -> case renameVar v rn
                           of Nothing -> ty
                              Just v' -> VarT v'
       IntT _           -> ty
       AppT op arg      -> AppT (rename rn op) (rename rn arg)
       FunT dom rng     -> FunT (rename rn dom) (rename rn rng)
       LamT binder body ->
         renameBinding rn binder $ \rn' binder' ->
         LamT binder' $ rename rn' body
       AllT binder rng  ->
         renameBinding rn binder $ \rn' binder' ->
         AllT binder' $ rename rn' rng
       AnyT _           -> ty    -- Kinds are not renameable

  freshen ty =
    case ty
    of LamT (v ::: dom) body -> do
         v' <- newClonedVar v
         let rn = singletonRenaming v v'
         return $ LamT (v' ::: dom) (rename rn body)
       AllT (v ::: dom) rng -> do
         v' <- newClonedVar v
         let rn = singletonRenaming v v'
         return $ AllT (v' ::: dom) (rename rn rng)
       -- Other terms don't bind variables
       _ -> return ty

  freeVariables ty =
    case ty
    of VarT v -> Set.singleton v
       IntT _ -> Set.empty
       AppT op arg -> Set.union (freeVariables op) (freeVariables arg)
       FunT dom rng ->
         let fv_dom = freeVariables dom 
             fv_rng = freeVariables rng
         in Set.union fv_dom fv_rng
       LamT (v ::: dom) body ->
         let fv_dom = freeVariables dom
             fv_body = freeVariables body
         in Set.union fv_dom (Set.delete v fv_body)
       AllT (v ::: dom) rng ->
         let fv_dom = freeVariables dom
             fv_rng = freeVariables rng
         in Set.union fv_dom (Set.delete v fv_rng)
       AnyT k -> freeVariables k

-- | Freshen variables bound in the types such that the same variable is 
--   bound by the outermost term in both types.  The outermost term is always
--   freshened.
unifyBoundVariables :: (Monad m, Supplies m VarID) =>
                       Type -> Type -> m (Type, Type)
unifyBoundVariables (LamT (v1 ::: dom1) body1) (LamT (v2 ::: dom2) body2) = do
  v' <- newClonedVar v1
  let rn1 = singletonRenaming v1 v'
      rn2 = singletonRenaming v2 v'
      t1 = LamT (v' ::: dom1) (rename rn1 body1)
      t2 = LamT (v' ::: dom2) (rename rn2 body2)
  return (t1, t2)
      
unifyBoundVariables (AllT (v1 ::: dom1) rng1) (AllT (v2 ::: dom2) rng2) = do
  v' <- newClonedVar v1
  let rn1 = singletonRenaming v1 v'
      rn2 = singletonRenaming v2 v'
      t1 = AllT (v' ::: dom1) (rename rn1 rng1)
      t2 = AllT (v' ::: dom2) (rename rn2 rng2)
  return (t1, t2)

-- Otherwise, they don't bind a common variable
unifyBoundVariables t1 t2 = do
  t1' <- freshen t1
  t2' <- freshen t2
  return (t1', t2')

-- | Like 'unifyBoundVariables', but variables from the first type are not
--   renamed.  Variables bound in the second type are renamed to match the
--   corresponding variables bound in the first type.
leftUnifyBoundVariables :: (Monad m, Supplies m VarID) =>
                       Type -> Type -> m (Type, Type)
leftUnifyBoundVariables t1@(LamT (v1 ::: _) _) (LamT (v2 ::: dom2) body2) =
  let rn2 = singletonRenaming v2 v1
      t2 = LamT (v1 ::: dom2) (rename rn2 body2)
  in return (t1, t2)
      
leftUnifyBoundVariables t1@(AllT (v1 ::: _) _) (AllT (v2 ::: dom2) rng2) =
  let rn2 = singletonRenaming v2 v1
      t2 = AllT (v1 ::: dom2) (rename rn2 rng2)
  in return (t1, t2)

-- Otherwise, they don't bind a common variable
leftUnifyBoundVariables t1 t2 = do
  t2' <- freshen t2
  return (t1, t2')

-------------------------------------------------------------------------------

newtype Substitution = S {unS :: IntMap.IntMap Type}

substitution :: [(Var, Type)] -> Substitution
substitution xs = S $ IntMap.fromList [(fromIdent $ varID v, t) | (v, t) <- xs]

substitutionFromMap :: IntMap.IntMap Type -> Substitution
substitutionFromMap = S

emptySubstitution :: Substitution
emptySubstitution = S IntMap.empty

singletonSubstitution :: Var -> Type -> Substitution
singletonSubstitution v t = insertSubstitution v t emptySubstitution

insertSubstitution :: Var -> Type -> Substitution -> Substitution
insertSubstitution v t (S s) = S (IntMap.insert (fromIdent $ varID v) t s)

substituteVar :: Var -> Substitution -> Maybe Type
substituteVar v (S m) = IntMap.lookup (fromIdent $ varID v) m

substituteBinding :: EvalMonad m =>
                     Substitution
                  -> Binder
                  -> (Substitution -> Binder -> m a)
                  -> m a
substituteBinding rn (x ::: t) k = do
  tenv <- getTypeEnv
  
  -- If the bound variable is in scope, then rename it to avoid name capture
  case lookupType x tenv of
    Nothing -> do t' <- substitute rn t
                  k rn (x ::: t')
    Just _  -> do
      t' <- substitute rn t
      x' <- newClonedVar x
      let rn' = insertSubstitution x (VarT x') rn
      k rn' (x' ::: t')

substituteBindings :: EvalMonad m =>
                      Substitution
                   -> [Binder]
                   -> (Substitution -> [Binder] -> m a)
                   -> m a
substituteBindings s (b:bs) k =
  substituteBinding s b $ \s' b' ->
  substituteBindings s' bs $ \s'' bs' ->
  k s'' (b':bs')

substituteBindings s [] k = k s []

class Substitutable a where
  substitute :: EvalMonad m => Substitution -> a -> m a

instance Substitutable a => Substitutable (Maybe a) where
  substitute s x = mapM (substitute s) x

instance Substitutable a => Substitutable [a] where
  substitute s xs = mapM (substitute s) xs

instance Substitutable Type where
  substitute sb ty =
    case ty
    of VarT v ->
         return $ fromMaybe ty $ substituteVar v sb
       AppT op arg ->
         liftM2 AppT (substitute sb op) (substitute sb arg)
       FunT dom rng ->
         liftM2 FunT (substitute sb dom) (substitute sb rng)
       AllT binder rng ->
         substituteBinding sb binder $ \sb' binder' -> do
           rng' <- substitute sb' rng
           return $ AllT binder' rng'
       LamT binder body ->
         substituteBinding sb binder $ \sb' binder' -> do
           body' <- substitute sb' body
           return $ LamT binder' body'
       AnyT _ -> return ty             -- Kinds are not substitutable
       IntT _ -> return ty 

