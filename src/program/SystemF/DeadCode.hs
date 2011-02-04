
module SystemF.DeadCode where

import Control.Monad.Writer
import qualified Data.Set as Set
import Data.Set(Set)

import Common.SourcePos
import Common.Error
import SystemF.Syntax
import Type.Type

-- | Dead code elimination on a value produces a new value and a set of
-- all variable names referenced by the value.
type EDC a = a -> GetMentionsSet a
type GetMentionsSet a = Writer (Set VarID) a

evalEDC :: (a -> GetMentionsSet b) -> a -> b
evalEDC f x = case runWriter $ f x of (x', _) -> x'

-- | Mention a variable.  This prevents the assignment of this variable from
-- being eliminated.
mention :: Var -> GetMentionsSet ()
mention v = tell (Set.singleton (varID v))

-- | Filter out a mention of a variable.  The variable will not appear in
-- the returned mentions set.
mask :: Var -> GetMentionsSet a -> GetMentionsSet a
mask v m = pass $ do x <- m
                     return (x, Set.delete (varID v))

-- | Filter out a mention of a variable, and also check whether the variable
-- is mentioned.  Return True if the variable is mentioned.
maskAndCheck :: Var -> GetMentionsSet a -> GetMentionsSet (Bool, a)
maskAndCheck v m = pass $ do
  (x, mentions_set) <- listen m
  return ( (varID v `Set.member` mentions_set, x)
         , Set.delete (varID v))

masks :: Set VarID -> GetMentionsSet a -> GetMentionsSet a
masks vs m = pass $ do x <- m
                       return (x, (`Set.difference` vs))

-- | Find variables that are mentioned in the type
edcType :: Type -> GetMentionsSet ()
edcType (VarT v) = mention v
edcType (AppT t1 t2) = edcType t1 >> edcType t2
edcType (FunT (ValPT (Just v) ::: dom) (_ ::: rng)) = do
  edcType dom
  mask v $ edcType rng
edcType (FunT (_ ::: dom) (_ ::: rng)) = do
  edcType dom
  edcType rng
