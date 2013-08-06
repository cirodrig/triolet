
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -no-auto #-}
module Type.Substitute where

import Prelude hiding(lookup, null, mapM)
import Control.DeepSeq
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

class SubstitutionMap a where
  -- | Produce an empty substitution
  emptySubstitution :: a
  
  -- | Decide whether the substitution is empty.
  -- The first argument should be ignored.
  isEmptySubstitution :: a -> Bool

-- | A substitution of types for type variables
data TypeSubst = S {unS :: IntMap.IntMap Type}

instance NFData TypeSubst where rnf (S m) = rnf m

empty :: TypeSubst
empty = S IntMap.empty

null :: TypeSubst -> Bool
null (S s) = IntMap.null s

singleton :: Var -> Type -> TypeSubst
singleton v t = rnf t `seq` S (IntMap.singleton (fromIdent $ varID v) t)

fromList :: [(Var, Type)] -> TypeSubst
fromList xs = S $ IntMap.fromList [rnf t `seq` (fromIdent $ varID v, t) | (v, t) <- xs]

fromBinderList :: [(Binder, Type)] -> TypeSubst
fromBinderList xs = fromList [rnf t `seq` (v, t) | (v ::: _, t) <- xs]

-- | Compute the union of two substitutions on disjoint sets of variables.
--
--   Disjointness is not verified.
union :: TypeSubst -> TypeSubst -> TypeSubst
union (S r1) (S r2) = S (IntMap.union r1 r2)

-- | @s2 `compose` s1@ is a substitution equivalent to applying @s1@, then
--   applying @s2@.
compose :: BoxingMode b =>
           TypeSubst -> TypeSubst -> TypeEvalM b TypeSubst
s2 `compose` s1 = do
  -- Apply s2 to the range of s1
  s1' <- traverse (substitute s2) (unS s1)
  
  -- Take the union of s1 and s2, with s1 overriding s2
  return $ S $ IntMap.union s1' (unS s2)

fromMap :: IntMap.IntMap Type -> TypeSubst
fromMap = S

extend :: Var -> Type -> TypeSubst -> TypeSubst
extend v t (S s) = rnf t `seq` S (IntMap.insert (fromIdent $ varID v) t s)

exclude :: Var -> TypeSubst -> TypeSubst
exclude v (S s) = S (IntMap.delete (fromIdent $ varID v) s)

lookup :: Var -> TypeSubst -> Maybe Type
lookup v (S m) = IntMap.lookup (fromIdent $ varID v) m

instance SubstitutionMap TypeSubst where
  emptySubstitution = empty
  isEmptySubstitution = null

-- | Push a substitution through a binder.  The substitution is applied to the
--   binder, and the binder is renamed if there is a name conflict with the
--   environment.  Renaming is performed even if the substitution is empty.
substituteBinder :: EvalMonad m =>
                    TypeSubst
                 -> Binder
                 -> (TypeSubst -> Binder -> m a)
                 -> m a
{-# SPECIALIZE substituteBinder :: BoxingMode b => TypeSubst -> Binder
                                -> (TypeSubst -> Binder -> TypeEvalM b a) 
                                -> TypeEvalM b a #-}
substituteBinder rn (x ::: t) k = do
  t' <- substitute rn t
  
  -- Is the bound variable in scope?
  type_assignment <- lookupType x
  case type_assignment of
    Nothing -> do
      -- Not in scope: remove from the substitution.
      -- This seems unnecessary, but can happen --
      -- "Secrets of the GHC Inliner" section 3.2.
      let !rn' = exclude x rn
      assume x t' $ rn' `seq` k rn' (x ::: t')
    Just _  -> do
      -- In scope: rename and add to the substitution
      x' <- newClonedVar x
      let !rn' = extend x (VarT x') rn
      assume x' t' $ rn' `seq` k rn' (x' ::: t')

substituteBinders :: EvalMonad m =>
                      TypeSubst
                   -> [Binder]
                   -> (TypeSubst -> [Binder] -> m a)
                   -> m a
{-# SPECIALIZE substituteBinders :: BoxingMode b =>
                                    TypeSubst -> [Binder]
                                 -> (TypeSubst -> [Binder] -> TypeEvalM b a)
                                 -> TypeEvalM b a #-}
substituteBinders s (b:bs) k =
  substituteBinder s b $ \s' b' ->
  substituteBinders s' bs $ \s'' bs' ->
  k s'' (b':bs')

substituteBinders s [] k = k s []

substituteVar v x a = substitute (singleton v x) a

class SubstitutionMap (Substitution a) => Substitutable a where
  -- | A substitution of variables in a value
  type Substitution a

  -- | Apply the substitution to the argument, and rename any variable 
  --   bindings in the outermost term that shadow an in-scope variable.
  substituteWorker :: BoxingMode b =>
                      Substitution a -> a -> TypeEvalM b a

-- | Rename variables bound in the outermost term to new, fresh names
--   if they would shadow the in-scope variables.
freshen :: forall m a. (EvalMonad m, Substitutable a) => a -> m a
freshen x = {-# SCC freshen #-}
  liftTypeEvalM $ substituteWorker emptySubstitution x

-- | Apply the substitution to the argument.
substitute :: forall m a. (EvalMonad m, Substitutable a) =>
              Substitution a -> a -> m a
substitute s x 
  | isEmptySubstitution s = return x
  | otherwise = {-# SCC substitute #-} liftTypeEvalM $ substituteWorker s x 

instance Substitutable a => Substitutable (Maybe a) where
  type Substitution (Maybe a) = Substitution a
  substituteWorker s x = mapM (substituteWorker s) x

instance (Substitutable a, Substitutable b, Substitution a ~ Substitution b) =>
         Substitutable (a, b) where
  type Substitution (a, b) = Substitution a
  substituteWorker s (x, y) =
    liftM2 (,) (substituteWorker s x) (substituteWorker s y)

instance Substitutable a => Substitutable [a] where
  type Substitution [a] = Substitution a
  substituteWorker s xs = mapM (substituteWorker s) xs

-- | A data type that does not mention any variables in the domain of
--   substitution 's'
newtype Nameless s a = Nameless a

instance SubstitutionMap s => Substitutable (Nameless s a) where
  type Substitution (Nameless s a) = s
  substituteWorker _ x = return x

instance Substitutable KindedType where
  type Substitution KindedType = TypeSubst
  substituteWorker sb (KindedType k t) =
    KindedType k `liftM` substituteWorker sb t

instance Substitutable Type where
  type Substitution Type = TypeSubst
  substituteWorker sb ty =
    case ty
    of VarT v ->
         return $! fromMaybe ty $ lookup v sb
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
--   The given types are assuemd to be in WHNF.
--   The outermost term is always freshened.
unifyBoundVariables :: EvalMonad m =>
                       Type -> Type -> m (Type, Type)
{-# INLINABLE unifyBoundVariables #-}
{-# SPECIALIZE unifyBoundVariables :: Type -> Type -> BoxedTypeEvalM (Type, Type) #-}
{-# SPECIALIZE unifyBoundVariables :: Type -> Type -> UnboxedTypeEvalM (Type, Type) #-}
unifyBoundVariables t1 t2 = {-# SCC "unifyBoundVariables" #-} liftTypeEvalM $
  case (t1, t2)
  of (LamT (v1 ::: dom1) body1, LamT (v2 ::: dom2) body2) -> do
       v' <- newClonedVar v1
       let t1' = LamT (v' ::: dom1) (rename (Rename.singleton v1 v') body1)
           t2' = LamT (v' ::: dom2) (rename (Rename.singleton v2 v') body2)
       return (t1', t2')
      
     (AllT (v1 ::: dom1) rng1, AllT (v2 ::: dom2) rng2) -> do
       v' <- newClonedVar v1
       let t1' = AllT (v' ::: dom1) (rename (Rename.singleton v1 v') rng1)
           t2' = AllT (v' ::: dom2) (rename (Rename.singleton v2 v') rng2)
       return (t1', t2')

     -- Otherwise, they don't bind a common variable
     _ -> do
       t1' <- freshen t1
       t2' <- freshen t2
       return (t1', t2')

-- | Like 'unifyBoundVariables', but variables from the first type are not
--   renamed.  Variables bound in the second type are renamed to match the
--   corresponding variables bound in the first type.
leftUnifyBoundVariables :: EvalMonad m =>
                           Type -> Type -> m (Type, Type)
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
