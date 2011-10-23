
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
module Type.Rename
       (-- * Renaming
        Renaming,
        empty,
        null,
        singleton,
        fromList,
        union,
        extend,
        compose,
        exclude,
        lookup,
        renameBinder,
        renameBinders,
        binderFreeVariables,
        bindersFreeVariables,
        Renameable(..),
        
        -- * Correctness checking
        assertVarIsUndefined,
        assertVarsAreUndefined,
        CheckForShadowing,
        checkForShadowing,
        checkForShadowingSet,
        checkForShadowingHere
       )
where

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

import qualified Data.IntMap as IntMap
import qualified Data.Set as Set

-- | A renaming of a set of variables.
--   Renaming may result in name shadowing.
newtype Renaming = R {unR :: IntMap.IntMap Var}

empty :: Renaming
empty = R IntMap.empty

null :: Renaming -> Bool
null (R rn) = IntMap.null rn

singleton :: Var -> Var -> Renaming
singleton v1 v2 = R $ IntMap.singleton (fromIdent $ varID v1) v2

fromList :: [(Var, Var)] -> Renaming
fromList xs = R $ IntMap.fromList [(fromIdent $ varID v1, v2) | (v1, v2) <- xs]

-- | Compute the union of two renamings on disjoint sets of variables.
--
--   Disjointness is not verified.
union :: Renaming -> Renaming -> Renaming
union (R r1) (R r2) = R (IntMap.union r1 r2)

extend :: Var -> Var -> Renaming -> Renaming
extend v1 v2 (R r) = R (IntMap.insert (fromIdent $ varID v1) v2 r)

-- | @r2 `compose` r1@ is a renaming equivalent to applying @r1@, then
--   applying @r2@.
compose :: Renaming -> Renaming -> Renaming
r2 `compose` r1 =
  -- Apply r2 to the range of r1
  let r1' = IntMap.map (rename r2) (unR r1)
  
  -- Take the union of r1 and r2, with r1 overriding r2
  in R $ IntMap.union r1' (unR r2)

exclude :: Var -> Renaming -> Renaming
exclude v (R r) = R (IntMap.delete (fromIdent $ varID v) r)

-- | Apply a renaming to a variable.  Return the renamed variable, or
--   @Nothing@ if it's not renamed.
lookup :: Var -> Renaming -> Maybe Var
lookup v (R m) = IntMap.lookup (fromIdent $ varID v) m

-- | Rename a variable binding.
--   Remove the bound variable from the renaming because it is shadowed.
renameBinder :: Renaming -> Binder -> (Renaming -> Binder -> a) -> a
renameBinder rn (x ::: t) k =
  -- Remove the bound variable from the environment; it is shadowed  
  let rn' = R $ IntMap.delete (fromIdent $ varID x) (unR rn)
  in k rn' (x ::: rename rn t)

renameBinders :: Renaming -> [Binder] -> (Renaming -> [Binder] -> a) -> a
renameBinders rn (b:bs) k =
  renameBinder rn b $ \rn' b' ->
  renameBinders rn' bs $ \rn'' bs' ->
  k rn'' (b':bs')

renameBinders rn [] k = k rn []

-- | Given a binder and the free variables of the term over which a variable
--   is bound, get the free variables of the combined term.
binderFreeVariables :: Binder -> Set.Set Var -> Set.Set Var
binderFreeVariables (x ::: t) s =
  Set.delete x $ freeVariables t `Set.union` s

-- | Given a binder and the free variables of the term over which a variable
--   is bound, get the free variables of the combined term.
bindersFreeVariables :: [Binder] -> Set.Set Var -> Set.Set Var
bindersFreeVariables bs s =
  foldr binderFreeVariables s bs

class Renameable a where
  -- | Rename an expression using the given renaming
  rename :: Renaming -> a -> a
  
  -- | Find the variables that are used in, but not defined in, the expression
  freeVariables :: a -> Set.Set Var

instance Renameable a => Renameable (Maybe a) where
  rename rn x = fmap (rename rn) x
  freeVariables x = maybe Set.empty freeVariables x

instance (Renameable a, Renameable b) => Renameable (a, b) where
  rename rn (x, y) = (rename rn x, rename rn y) 
  freeVariables (x, y) = freeVariables x `Set.union` freeVariables y

instance Renameable a => Renameable [a] where
  rename rn xs = map (rename rn) xs
  freeVariables xs = Set.unions $ map freeVariables xs

instance Renameable Var where
  rename rn v = fromMaybe v $ lookup v rn
  freeVariables v = Set.singleton v

instance Renameable Type where
  rename rn ty =
    case ty
    of VarT v           -> case lookup v rn
                           of Nothing -> ty
                              Just v' -> VarT v'
       IntT _           -> ty
       AppT op arg      -> rename rn op `AppT` rename rn arg
       FunT dom rng     -> rename rn dom `FunT` rename rn rng
       LamT binder body ->
         renameBinder rn binder $ \rn' binder' ->
         LamT binder' $ rename rn' body
       AllT binder rng  ->
         renameBinder rn binder $ \rn' binder' ->
         AllT binder' $ rename rn' rng
       AnyT k           -> AnyT $ rename rn k
       UTupleT _        -> ty
       CoT _            -> ty

  freeVariables ty =
    case ty
    of VarT v -> Set.singleton v
       IntT _ -> Set.empty
       AppT op arg -> freeVariables op `Set.union` freeVariables arg
       FunT dom rng -> freeVariables dom `Set.union` freeVariables rng
       LamT binder body -> binderFreeVariables binder $ freeVariables body
       AllT binder rng -> binderFreeVariables binder $ freeVariables rng
       AnyT k -> freeVariables k
       UTupleT _ -> Set.empty
       CoT _ -> Set.empty

-------------------------------------------------------------------------------

-- | Check for name shadowing in the type.  If any in-scope variables
--   are redefined, raise an error.
checkForShadowing :: TypeEnv -> Type -> ()
checkForShadowing tenv ty =
  checkForShadowingSet (IntMap.keysSet $ getAllTypes tenv) ty

type CheckForShadowing a = IntSet.IntSet -> a -> ()

-- | Check whether a variable has been defined
assertVarIsUndefined :: CheckForShadowing Var
assertVarIsUndefined in_scope v
  | fromIdent (varID v) `IntSet.member` in_scope =
      internalError $ "Variable is shadowed: " ++ show v
  | otherwise = ()

-- | Check whether a list of variables has been defined or whether any two
--   variables in the list are equal.
assertVarsAreUndefined :: CheckForShadowing [Var]
assertVarsAreUndefined in_scope vs =
  -- Find variables that are repeated in the list.
  -- Error if any such variable is found.
  case [x | x : xs <- tails vs, y <- xs, x == y]
  of x : _ ->
       internalError $ "Conflicting definitions of variable: " ++ show x
     [] ->
       -- Error if any existential variable shadows a name 
       foldr seq () $ map (assertVarIsUndefined in_scope) vs

checkForShadowingSet :: CheckForShadowing Type
checkForShadowingSet in_scope ty =
  case ty
  of VarT _ -> ()
     AppT t1 t2 -> continue t1 `seq` continue t2
     LamT (a ::: k) t1 ->
       check_in_scope a $
       continue k `seq`
       checkForShadowingSet (insert a in_scope) t1
     FunT t1 t2 -> continue t1 `seq` continue t2
     AllT (a ::: k) t1 ->
       check_in_scope a $
       continue k `seq`
       checkForShadowingSet (insert a in_scope) t1
     AnyT k -> continue k
     IntT _ -> ()
     CoT _ -> ()
     UTupleT _ -> ()
  where
    check_in_scope a k = assertVarIsUndefined in_scope a `seq` k
    continue t = checkForShadowingSet in_scope t
    insert v scope = IntSet.insert (fromIdent $ varID v) scope

-- | Check for name shadowing using the current type environment.
--   The caller must force evaluation of the return value.
checkForShadowingHere :: TypeEnvMonad m => Type -> m ()
checkForShadowingHere ty = askTypeEnv (\tenv -> checkForShadowing tenv ty)