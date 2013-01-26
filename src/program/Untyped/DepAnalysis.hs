{-| Type inference dependency analysis on a definition group.

The input to dependency analysis is a minimal recursive definition
group, i.e. one where every definition directly or indirectly references
every other definition in the group such that the group can't be split into
a sequence of independent definitions.  The definition group is decomposed
into SCCs based on type inference dependences.
A binding @b1@ /immediately depends on/ a binding @b2@ iff @b1@ mentions
the variable bound by @b2@ and @b2@ doesn't have a complete type signature.
Type inference dependences are the transitive closure of the immediate 
dependence relation.

The output is a list of SCCs.  The SCCs will be type checked or inferred
in the order they are given.

-}

module Untyped.DepAnalysis
       (depAnalysis)
where

import Data.List
import Data.Monoid
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Graph.Inductive as Graph
import qualified Data.Graph.Inductive.Graph as Graph
import qualified Data.Graph.Inductive.Query.DFS as Graph

import Common.Identifier
import Untyped.Syntax
import Untyped.Variable

newtype FreeVars = FreeVars (Set.Set Variable -> Set.Set Variable)

runFreeVars (FreeVars f) = f Set.empty

instance Monoid FreeVars where
  mempty = FreeVars id
  FreeVars f `mappend` FreeVars g = FreeVars (f . g)

class Use a where free :: a -> FreeVars

instance Use a => Use [a] where free xs = mconcat $ map free xs

useVar :: Variable -> FreeVars
useVar v = FreeVars (Set.insert v)

class Def a where define :: a -> FreeVars -> FreeVars

instance Def a => Def [a] where define xs f = foldr define f xs

-- | Remove a variable from the free variable set
defineVar :: Variable -> FreeVars -> FreeVars
defineVar v fv =
  FreeVars (Set.union (Set.delete v $ runFreeVars fv))

-- | Remove several variables from the free variable set
defineVars :: [Variable] -> FreeVars -> FreeVars
defineVars vs fv =
  FreeVars (Set.union (foldl' (flip Set.delete) (runFreeVars fv) vs))

instance Use Expression where
  free (VariableE _ v)          = useVar v
  free (LiteralE _ _)           = mempty
  free (ListE _ es)             = free es
  free (UndefinedE _)           = mempty
  free (TupleE _ es)            = free es
  free (CallE _ op args)        = free op `mappend` free args
  free (IfE _ c t f)            = free c `mappend` free t `mappend` free f
  free (FunE _ f)               = free f
  free (LetE _ p rhs body)      = free rhs `mappend` define p (free body)
  free (LetrecE _ defs body)    = freeGroup defs $ free body
  free (TypeAssertE _ v _ body) = useVar v `mappend` free body

instance Use Function where
  free (Function _ params _ body) = define params $ free body

instance Use Export where
  free (Export _ _ v _) = useVar v

instance Def Pattern where
  define (WildP _) x         = x
  define (VariableP _ v _) x = defineVar v x
  define (TupleP _ ps) x     = define ps x

-- | Compute free variables in a definition group
freeGroup :: DefGroup -> FreeVars -> FreeVars
freeGroup fdefs f = defineVars bound_vars $ free functions `mappend` f
  where
    bound_vars = [v | FunctionDef v _ _ <- fdefs]
    functions = [f | FunctionDef _ _ f <- fdefs]

depAnalysis :: DefGroup -> [[FunctionDef]]
depAnalysis defs =
  let components = reverse $ Graph.scc g
  in map (map labelOf) components
  where
    labelOf n = nodeMap Map.! n
    
    nodeMap = Map.fromList [(fromIdent $ varID v, d)
                           | d@(FunctionDef v _ _) <- defs]

    defined_variables = Set.fromList [v | FunctionDef v _ _ <- defs]
    explicitly_typed_variables =
      Set.fromList [v | FunctionDef v ann _ <- defs
                      , isGivenSignature $ funPolySignature ann]

    -- It's only possible to depend on locally defined variables that don't
    -- have an explicit type signature
    dep_targets = defined_variables Set.\\ explicitly_typed_variables

    -- Get the subset of defined_variables that f depends on. 
    -- These are the variables that are used by f and not explicitly typed.
    dependences f =
      Set.toList $ dep_targets `Set.intersection` runFreeVars (free f)

    -- Create a graph.  Use the function variable ID as the node ID.
    nodes :: [Graph.LNode FunctionDef]
    nodes = [(fromIdent $ varID v, d) | d@(FunctionDef v _ _) <- defs]

    edges :: [Graph.UEdge]
    edges = [(function_var_id, use_var_id, ())
            | FunctionDef function_var _ f <- defs
            , let function_var_id = fromIdent $ varID function_var
            , use_var <- dependences f
            , let use_var_id = fromIdent $ varID use_var]

    g = Graph.mkGraph nodes edges :: Graph.Gr FunctionDef ()
