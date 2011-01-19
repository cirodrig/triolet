
{-# LANGUAGE FlexibleContexts #-}
module Type.Rename where

import Data.Maybe

import Gluon.Common.Identifier
import Gluon.Common.Supply
import Type.Var
import Type.Type

import qualified Data.IntMap as IntMap

newtype Renaming = R {unR :: IntMap.IntMap Var}

renaming :: [(Var, Var)] -> Renaming
renaming xs = R $ IntMap.fromList [(fromIdent $ varID v1, v2) | (v1, v2) <- xs]

singletonRenaming :: Var -> Var -> Renaming
singletonRenaming v1 v2 = renaming [(v1, v2)]

renameVar :: Var -> Renaming -> Maybe Var
renameVar v (R m) = IntMap.lookup (fromIdent $ varID v) m

renameBinding :: Renaming -> a ::: Type -> a ::: Type
renameBinding rn (x ::: t) = x ::: rename rn t

class Renameable a where
  -- | Rename an expression using the given renaming
  rename :: Renaming -> a -> a
  
  -- | Rename variables bound in the outermost term to new, fresh names
  freshen :: (Monad m, Supplies m VarID) => a -> m a

instance Renameable Var where
  rename rn v = fromMaybe v $ renameVar v rn
  freshen v = return v

instance Renameable Type where
  rename rn ty =
    case ty
    of VarT v ->
         case renameVar v rn
         of Nothing -> ty
            Just v' -> VarT v'
       AppT op arg ->
         AppT (rename rn op) (rename rn arg)
       FunT (arg ::: dom) (ret ::: rng) ->
         FunT (arg ::: rename rn dom) (ret ::: rename rn rng)

  freshen ty =
    case ty
    of FunT (ValPT (Just v) ::: dom) result -> do
         v' <- newClonedVar v
         let rn = singletonRenaming v v'
         return $ FunT (ValPT (Just v') ::: dom) (renameBinding rn result)
       -- Other terms don't bind variables
       _ -> return ty

-- | Freshen variables bound in the types such that the same variable is 
--   bound by the outermost term in both types.  The outermost term is always
--   freshened.
unifyBoundVariables :: (Monad m, Supplies m VarID) =>
                       Type -> Type -> m (Type, Type)
unifyBoundVariables (FunT param1 result1) (FunT param2 result2)
  | ValPT (Just v1) ::: dom1 <- param1,
    ValPT (Just v2) ::: dom2 <- param2 = do
      v' <- newClonedVar v1
      let rn1 = singletonRenaming v1 v'
      let rn2 = singletonRenaming v2 v'
      let t1 = FunT (ValPT (Just v') ::: dom1) (renameBinding rn1 result1)
      let t2 = FunT (ValPT (Just v') ::: dom2) (renameBinding rn2 result2)
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
leftUnifyBoundVariables t1@(FunT param1 result1) (FunT param2 result2)
  | ValPT (Just v1) ::: dom1 <- param1,
    ValPT (Just v2) ::: dom2 <- param2 =
      let rn2 = singletonRenaming v2 v1
          t2 = FunT (ValPT (Just v1) ::: dom2) (renameBinding rn2 result2)
      in return (t1, t2)
      
-- Otherwise, they don't bind a common variable
leftUnifyBoundVariables t1 t2 = do
  t2' <- freshen t2
  return (t1, t2')

-------------------------------------------------------------------------------
  
newtype Substitution = S {unS :: IntMap.IntMap Type}

substitution :: [(Var, Type)] -> Substitution
substitution xs = S $ IntMap.fromList [(fromIdent $ varID v, t) | (v, t) <- xs]

emptySubstitution :: Substitution
emptySubstitution = S IntMap.empty

singletonSubstitution :: Var -> Type -> Substitution
singletonSubstitution v t = insertSubstitution v t emptySubstitution

insertSubstitution :: Var -> Type -> Substitution -> Substitution
insertSubstitution v t (S s) = S (IntMap.insert (fromIdent $ varID v) t s)

substituteVar :: Var -> Substitution -> Maybe Type
substituteVar v (S m) = IntMap.lookup (fromIdent $ varID v) m

substituteBinding :: Substitution -> a ::: Type -> a ::: Type
substituteBinding rn (x ::: t) = x ::: substitute rn t

class Substitutable a where
  substitute :: Substitution -> a -> a

instance Substitutable Type where
  substitute sb ty =
    case ty
    of VarT v ->
         fromMaybe ty $ substituteVar v sb
       AppT op arg ->
         AppT (substitute sb op) (substitute sb arg)
       FunT (arg ::: dom) result ->
         FunT (arg ::: substitute sb dom) (substituteBinding sb result)

