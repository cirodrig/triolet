
module SystemF.DeadCode where

import Control.Monad.Reader
import Control.Monad.Writer
import qualified Data.Graph as Graph
import qualified Data.IntMap as IntMap
import qualified Data.Set as Set

import Common.Identifier
import Common.SourcePos
import Common.Error
import SystemF.Syntax
import Type.Environment
import Type.Rename
import Type.Type

-- | The number of times a variable is mentioned, stored in a 'MentionsSet'.
--   If a variable is not mentioned at all, it's not stored in the set.
data Mentions = One | Many deriving(Show)

type MentionsSet = IntMap.IntMap Mentions

newtype MSet = MSet MentionsSet

-- When taking the set union, we need to add mentions together
instance Monoid MSet where
  mempty = MSet mempty
  mappend (MSet s1) (MSet s2) = MSet (msetUnion s1 s2)

msetUnion :: MentionsSet -> MentionsSet -> MentionsSet
msetUnion s1 s2 = IntMap.unionWith (\_ _ -> Many) s1 s2 

-- | Create a set where each variable is mentioned once.
mentionsSet :: [Var] -> MentionsSet
mentionsSet vs = idMentionsSet (map varID vs)

idMentionsSet :: [VarID] -> MentionsSet
idMentionsSet ids = IntMap.fromList [(fromIdent id, One) | id <- ids]

type EDC a = a -> GetMentionsSet a

-- | Dead code elimination takes the global type environment as a parameter,
--   which is used to look up type and data constructors only.
--   It returns information on what variable references were observed.
type GetMentionsSet a = ReaderT TypeEnv (Writer MSet) a

evalEDC :: TypeEnv -> (a -> GetMentionsSet b) -> a -> b
evalEDC tenv f x = case runWriter (runReaderT (f x) tenv) of (x', _) -> x'

-- | Mention a variable.  This prevents the assignment of this variable from
-- being eliminated.
mention :: Var -> GetMentionsSet ()
mention v = tell (MSet $ IntMap.singleton (fromIdent $ varID v) One)

-- | Mention a variable as it it was mentioned many times.
mentionMany :: Var -> GetMentionsSet ()
mentionMany v = tell (MSet $ IntMap.singleton (fromIdent $ varID v) Many)

mentions :: [Var] -> GetMentionsSet ()
mentions vs =
  tell (MSet $ IntMap.fromList [(fromIdent $ varID v, One) | v <- vs])

-- | Filter out a mention of a variable.  The variable will not appear in
-- the returned mentions set.
mask :: Var -> GetMentionsSet a -> GetMentionsSet a
mask v m = pass $ do
  x <- m
  return (x, \(MSet s) -> MSet $ IntMap.delete (fromIdent $ varID v) s)

-- | Filter out a mention of a variable, and also check whether the variable
--   is mentioned.  Return @Nothing@ if the variable is not mentioned,
--   @Just One@ if it's mentioned exactly once, or @Just Many@ if it's
--   mentioned more than once.
maskAndCheck :: Var -> GetMentionsSet a -> GetMentionsSet (Maybe Mentions, a)
maskAndCheck v m = pass $ do
  (x, MSet mentions_set) <- listen m
  return ( (IntMap.lookup (fromIdent (varID v)) mentions_set, x)
         , \(MSet s) -> MSet $ IntMap.delete (fromIdent $ varID v) s)

masks :: MentionsSet -> GetMentionsSet a -> GetMentionsSet a
masks vs m = pass $ do x <- m
                       return (x, \(MSet s) -> MSet (s `IntMap.difference` vs))

-- | Find variables that are mentioned in the type
edcType :: Type -> GetMentionsSet ()
edcType t = mentions $ Set.toList $ freeVariables t

-- | Given the members of a definition group, the variables mentioned by them, 
--   and the set of members that are referenced by the rest of the program,
--   partition the group into a list of minimal definition groups.  Dead 
--   members are removed, and each group is only referenced by subsequent
--   members of the list.
partitionDefGroup :: [(a, VarID, MentionsSet)]
                     -- ^ The members of the definition group, their IDs, and
                     -- the IDs of the variables they reference
                  -> MentionsSet -- ^ References to members of definition group
                  -> [DefGroup a] -- ^ The partitioned definition group
partitionDefGroup members external_refs =
  let member_id_set = idMentionsSet [n | (_, n, _) <- members]
      
      -- Restrict set 's' to the members of the definition group
      restrict s = IntMap.intersection s member_id_set

      -- Create a dummy variable ID for the graph node that represents 
      -- external references to the definition group
      dummy_id = toIdent $ 1 + fst (IntMap.findMax member_id_set)

      graph = (Nothing, dummy_id, nodes $ restrict external_refs) :
              [(Just x, n, nodes $ restrict ys) | (x, n, ys) <- members]
      
      sccs = Graph.stronglyConnComp graph
  in to_defgroups sccs
  where
    nodes :: MentionsSet -> [VarID]
    nodes = map toIdent . IntMap.keys

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

