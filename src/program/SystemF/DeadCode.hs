
module SystemF.DeadCode where

import Control.Monad.Writer
import qualified Data.Graph as Graph
import qualified Data.Set as Set
import Data.Set(Set)

import Common.Identifier
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

-- | Given the members of a definition group, the variables mentioned by them, 
--   and the set of members that are referenced by the rest of the program,
--   partition the group into a list of minimal definition groups.  Dead 
--   members are removed, and each group is only referenced by subsequent
--   members of the list.
partitionDefGroup :: [(a, VarID, Set VarID)]
                     -- ^ The members of the definition group, their IDs, and
                     -- the IDs of the variables they reference
                  -> Set VarID  -- ^ References to members of definition group
                  -> [DefGroup a] -- ^ The partitioned definition group
partitionDefGroup members external_refs =
  let member_ids = [n | (_, n, _) <- members]
      member_id_set = Set.fromList member_ids
      
      -- Restrict set 's' to the members of the definition group
      restrict s = Set.intersection s member_id_set

      -- Create a dummy variable ID for the graph node that represents 
      -- external references to the definition group
      dummy_id = toIdent $ 1 + fromIdent (maximum member_ids)

      graph = (Nothing, dummy_id, Set.toList $ restrict external_refs) :
              [(Just x, n, Set.toList $ restrict ys) | (x, n, ys) <- members]
      
      sccs = Graph.stronglyConnComp graph
  in to_defgroups sccs
  where
    to_defgroups sccs =
      -- Only save the definitions that precede the dummy node,
      -- meaning that they're referenced by something external
      map to_defgroup $ fst $ break is_dummy_node sccs

    to_defgroup (Graph.AcyclicSCC (Just x)) =
      NonRec x
    to_defgroup (Graph.AcyclicSCC _) =
      internalError "partitionDefGroup"
    to_defgroup (Graph.CyclicSCC xs) =
      case sequence xs
      of Just xs' -> Rec xs'
         _ -> internalError "partitionDefGroup"
    
    is_dummy_node (Graph.AcyclicSCC Nothing) = True
    is_dummy_node _ = False

