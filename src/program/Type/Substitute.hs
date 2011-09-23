
{-# LANGUAGE FlexibleContexts #-}
module Type.Substitute where

import Prelude hiding(lookup, null, mapM)
import Control.Monad hiding(mapM)
import qualified Data.IntSet as IntSet
import Data.List(tails)
import Data.Maybe
import Data.Monoid
import Data.Traversable(traverse, mapM)

import Common.Error
import Common.Identifier
import Common.Supply
import Type.Type
import Type.Environment
import qualified Type.Rename as Rename
import Type.Rename(Renaming, Renameable(..))

import qualified Data.IntMap as IntMap
import qualified Data.Set as Set

-- | A substitution of types for type variables
data TypeSubst = S {unS :: IntMap.IntMap Type}

empty :: TypeSubst
empty = S IntMap.empty

null :: TypeSubst -> Bool
null (S s) = IntMap.null s

singleton :: Var -> Type -> TypeSubst
singleton v t = S (IntMap.singleton (fromIdent $ varID v) t)

fromList :: [(Var, Type)] -> TypeSubst
fromList xs = S $ IntMap.fromList [(fromIdent $ varID v, t) | (v, t) <- xs]

-- | Compute the union of two substitutions on disjoint sets of variables.
--
--   Disjointness is not verified.
union :: TypeSubst -> TypeSubst -> TypeSubst
union (S r1) (S r2) = S (IntMap.union r1 r2)

fromMap :: IntMap.IntMap Type -> TypeSubst
fromMap = S

extend :: Var -> Type -> TypeSubst -> TypeSubst
extend v t (S s) = S (IntMap.insert (fromIdent $ varID v) t s)

exclude :: Var -> TypeSubst -> TypeSubst
exclude v (S s) = S (IntMap.delete (fromIdent $ varID v) s)

lookup :: Var -> TypeSubst -> Maybe Type
lookup v (S m) = IntMap.lookup (fromIdent $ varID v) m

-- | Push a substitution through a binder.  The substitution is applied to the
--   binder, and the binder is renamed if there is a name conflict with the
--   environment.  Renaming is performed even if the substitution is empty.
substituteBinder :: EvalMonad m =>
                    TypeSubst
                 -> Binder
                 -> (TypeSubst -> Binder -> m a)
                 -> m a
{-# SPECIALIZE substituteBinder :: TypeSubst -> Binder
                                -> (TypeSubst -> Binder -> TypeEvalM a) 
                                -> TypeEvalM a #-}
substituteBinder rn (x ::: t) k = do
  t' <- substitute rn t
  
  -- Is the bound variable in scope?
  type_assignment <- askTypeEnv (lookupType x)
  case type_assignment of
    Nothing -> do
      -- Not in scope: remove from the substitution.
      -- This seems unnecessary, but can happen --
      -- "Secrets of the GHC Inliner" section 3.2.
      let rn' = exclude x rn
      assume x t' $ k rn' (x ::: t')
    Just _  -> do
      -- In scope: rename and add to the substitution
      x' <- newClonedVar x
      let rn' = extend x (VarT x') rn
      assume x' t' $ k rn' (x' ::: t')

substituteBinders :: EvalMonad m =>
                      TypeSubst
                   -> [Binder]
                   -> (TypeSubst -> [Binder] -> m a)
                   -> m a
{-# SPECIALIZE substituteBinders :: TypeSubst -> [Binder]
                                 -> (TypeSubst -> [Binder] -> TypeEvalM a) 
                                 -> TypeEvalM a #-}
substituteBinders s (b:bs) k =
  substituteBinder s b $ \s' b' ->
  substituteBinders s' bs $ \s'' bs' ->
  k s'' (b':bs')

substituteBinders s [] k = k s []

substituteVar v x a = substitute (singleton v x) a

class Substitutable a where
  -- | A substitution of variables in a value
  type Substitution a

  -- | Produce an empty substitution.  The argument should be ignored.
  emptySubstitution :: a -> Substitution a
  
  -- | Decide whether the substitution is empty.
  -- The first argument should be ignored.
  isEmptySubstitution :: a -> Substitution a -> Bool

  -- | Apply the substitution to the argument, and rename any variable 
  --   bindings in the outermost term that shadow an in-scope variable.
  substituteWorker :: EvalMonad m => Substitution a -> a -> m a

-- | Rename variables bound in the outermost term to new, fresh names
--   if they would shadow the in-scope variables.
freshen :: forall m a. (EvalMonad m, Substitutable a) => a -> m a
{-# SPECIALIZE freshen :: Substitutable a => a -> TypeEvalM a #-}
freshen = substituteWorker (emptySubstitution (undefined :: a))

-- | Apply the substitution to the argument.
substitute :: forall m a. (EvalMonad m, Substitutable a) =>
              Substitution a -> a -> m a
{-# SPECIALIZE substitute :: Substitutable a => Substitution a -> a -> TypeEvalM a #-}
substitute s x 
  | isEmptySubstitution (undefined :: a) s = return x
  | otherwise = substituteWorker s x 

instance Substitutable a => Substitutable (Maybe a) where
  type Substitution (Maybe a) = Substitution a
  emptySubstitution x = emptySubstitution (undefined `asTypeOf` fromJust x)
  isEmptySubstitution x s =
    isEmptySubstitution (undefined `asTypeOf` fromJust x) s
  substituteWorker s x = mapM (substituteWorker s) x

instance (Substitutable a, Substitutable b, Substitution a ~ Substitution b) =>
         Substitutable (a, b) where
  type Substitution (a, b) = Substitution a
  emptySubstitution x = emptySubstitution (undefined `asTypeOf` fst x)
  isEmptySubstitution x s = isEmptySubstitution (undefined `asTypeOf` fst x) s
  substituteWorker s (x, y) =
    liftM2 (,) (substituteWorker s x) (substituteWorker s y)

instance Substitutable a => Substitutable [a] where
  type Substitution [a] = Substitution a
  emptySubstitution x = emptySubstitution (head x)
  isEmptySubstitution x s =
    isEmptySubstitution (undefined `asTypeOf` head x) s
  substituteWorker s xs = mapM (substituteWorker s) xs

instance Substitutable Type where
  type Substitution Type = TypeSubst
  emptySubstitution _ = empty
  isEmptySubstitution _ = null

  substituteWorker sb ty =
    case ty
    of VarT v ->
         return $ fromMaybe ty $ lookup v sb
       AppT op arg ->
         liftM2 AppT (substitute sb op) (substitute sb arg)
       FunT dom rng ->
         liftM2 FunT (substitute sb dom) (substitute sb rng)
       AllT binder rng ->
         substituteBinder sb binder $ \sb' binder' -> do
           rng' <- substitute sb' rng
           return $ AllT binder' rng'
       LamT binder body ->
         substituteBinder sb binder $ \sb' binder' -> do
           body' <- substitute sb' body
           return $ LamT binder' body'
       AnyT k -> liftM AnyT $ substitute sb k
       IntT _ -> return ty 
       UTupleT _ -> return ty
       CoT _ -> return ty

-- | Rename variables bound in the types such that the same variable is 
--   bound by the outermost term in both types.
--   The outermost term is always freshened.
unifyBoundVariables :: EvalMonad m =>
                       Type -> Type -> m (Type, Type)
{-# SPECIALIZE unifyBoundVariables :: Type -> Type -> TypeEvalM (Type, Type) #-}
unifyBoundVariables (LamT (v1 ::: dom1) body1) (LamT (v2 ::: dom2) body2) = do
  v' <- newClonedVar v1
  let t1 = LamT (v' ::: dom1) (rename (Rename.singleton v1 v') body1)
      t2 = LamT (v' ::: dom2) (rename (Rename.singleton v2 v') body2)
  return (t1, t2)
      
unifyBoundVariables (AllT (v1 ::: dom1) rng1) (AllT (v2 ::: dom2) rng2) = do
  v' <- newClonedVar v1
  let t1 = AllT (v' ::: dom1) (rename (Rename.singleton v1 v') rng1)
      t2 = AllT (v' ::: dom2) (rename (Rename.singleton v2 v') rng2)
  return (t1, t2)

-- Otherwise, they don't bind a common variable
unifyBoundVariables t1 t2 = do
  t1' <- freshen t1
  t2' <- freshen t2
  return (t1', t2')

-- | Like 'unifyBoundVariables', but variables from the first type are not
--   renamed.  Variables bound in the second type are renamed to match the
--   corresponding variables bound in the first type.
leftUnifyBoundVariables :: EvalMonad m =>
                           Type -> Type -> m (Type, Type)
{-# SPECIALIZE leftUnifyBoundVariables :: Type -> Type -> TypeEvalM (Type, Type) #-}
leftUnifyBoundVariables t1@(LamT (v1 ::: _) _) (LamT (v2 ::: dom2) body2) =
  let t2 = LamT (v1 ::: dom2) (rename (Rename.singleton v2 v1) body2)
  in return (t1, t2)
      
leftUnifyBoundVariables t1@(AllT (v1 ::: _) _) (AllT (v2 ::: dom2) rng2) =
  let t2 = AllT (v1 ::: dom2) (rename (Rename.singleton v2 v1) rng2)
  in return (t1, t2)

-- Otherwise, they don't bind a common variable
leftUnifyBoundVariables t1 t2 = do
  t2' <- freshen t2
  return (t1, t2')
