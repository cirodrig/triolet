{-|
Functions are scanned to find and label their /join points/.  A
function @g@ is a join point of @f@ if it is only executed by saturated tail
calls in @f@ or in join points of @f@.  Join points are handled specially by
inlining and closure conversion.  Inlining puts code at the return points of
a function, which are the 'ReturnE' terms that /don't/ call join points.
Closure conversion does not hoist join points.

Join points should be labeled by calling 'convertJoinPoints' after DCE and
before inlining.  DCE improves the ability to detect join points.  Inlining
uses knowledge of join points to keep tail calls of local functions in tail
position.

One top-level function at a time is converted.  The code is scanned to build a
/tail-calls/ graph in which an edge @f -> g@ means that @f@ tail-calls @g@
and @g@ is not referenced in a way other than a tail call.  The roots of the
graph, that is, functions that are used in some way other than a tail call,
are also identified.  Reachability from roots is determined using depth-first
search.  If any node is reachable from multiple roots, it is not a join point;
the remaining reachable set are endpoints.
-}

module LowLevel.JoinPoints(convertJoinPoints) where

import Data.Graph.Inductive(Gr)
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Query.DFS
import qualified Data.IntMap as IntMap
import Data.List as List
import qualified Data.Map as Map
import Data.Monoid
import qualified Data.Set as Set

import Common.Error
import Common.Identifier
import LowLevel.CodeTypes
import LowLevel.FreshVar
import LowLevel.Rename
import LowLevel.Syntax
import Globals

-------------------------------------------------------------------------------
-- Finding join points

-- | Information about observed tail calls observed in a function.
--
--   This keeps track of roots, functions that are defined in the scanned
--   scope, and tail calls.
data ObservedTailCalls = ObservedTailCalls [Var] [Var] [(Var, Var)]

instance Monoid ObservedTailCalls where
  mempty = ObservedTailCalls [] [] []
  ObservedTailCalls x1 y1 z1 `mappend` ObservedTailCalls x2 y2 z2 =
    ObservedTailCalls (x1 ++ x2) (y1 ++ y2) (z1 ++ z2)

-- | A tail call scan.  The scan needs to know the function in which
--   the current code is contained and the arity of all locally defined
--   functions.
type TailCallScan = Var -> IntMap.IntMap Int -> ObservedTailCalls

setCallingContext :: Var -> TailCallScan -> TailCallScan
setCallingContext v f = \_ arities -> f v arities

-- | Scan code that may use a definition of a function.  The function's
--   arity is given as a parameter.
withDefinition :: Var -> Int -> TailCallScan -> TailCallScan
withDefinition v arity f = \cc arities -> 
  let arities' = IntMap.insert (fromIdent $ varID v) arity arities
      ObservedTailCalls roots defs edges = f cc arities'
  in ObservedTailCalls roots (v:defs) edges

-- | Use a variable in a non-tail-call context
use :: Var -> TailCallScan
use v = scanner
  where
    scanner _ arities
      | fromIdent (varID v) `IntMap.member` arities =
          ObservedTailCalls [v] [] []
      | otherwise = mempty

-- | Use a variable in a tail call
useTailCall :: Var -> Int -> TailCallScan
useTailCall v num_args = scanner
  where
    scanner caller arities =
      case IntMap.lookup (fromIdent $ varID v) arities
      of Nothing -> mempty      -- Variable is ignored 
         Just arity | arity /= num_args -> non_tail_call
                    | otherwise         -> tail_call caller v
    non_tail_call = ObservedTailCalls [v] [] []
    tail_call caller callee = ObservedTailCalls [] [] [(caller, callee)]

tailCallScanVal :: Val -> TailCallScan
tailCallScanVal value =
  case value
  of VarV v -> use v
     RecV _ vs -> tailCallScanVals vs
     LitV _ -> mempty
     
tailCallScanVals :: [Val] -> TailCallScan
tailCallScanVals vs = mconcat $ map tailCallScanVal vs

-- | Scan an atom that's not in tail position
tailCallScanAtom :: Atom -> TailCallScan
tailCallScanAtom (ValA vs) = tailCallScanVals vs
tailCallScanAtom (CallA _ op args) = tailCallScanVals (op:args)
tailCallScanAtom (PrimA _ vs) = tailCallScanVals vs
tailCallScanAtom (PackA _ vs) = tailCallScanVals vs
tailCallScanAtom (UnpackA _ v) = tailCallScanVal v

tailCallScanStm :: Stm -> TailCallScan
tailCallScanStm statement =
  case statement
  of LetE params rhs body ->
       tailCallScanAtom rhs `mappend` tailCallScanStm body
     LetrecE defs body ->
       tailCallScanDefs defs $ tailCallScanStm body
     SwitchE scrutinee alternatives ->
       mconcat $
       tailCallScanVal scrutinee : map (tailCallScanStm . snd) alternatives

     -- Scan a tail call
     ReturnE (CallA _ (VarV op) args) ->
       useTailCall op (length args) `mappend` tailCallScanVals args
     ReturnE atom ->
       tailCallScanAtom atom
     ThrowE val ->
       tailCallScanVal val

tailCallScanFun :: Fun -> TailCallScan
tailCallScanFun f = tailCallScanStm (funBody f)

tailCallScanDefs defs scan = with_definitions (scan `mappend` scan_definitions)
  where
    with_definitions k = foldr with_definition k (groupMembers defs)
    with_definition def k =
      withDefinition (definiendum def) (length $ funParams $ definiens def) k
    
    scan_definitions =
      mconcat [setCallingContext fname $ tailCallScanFun fun
              | Def fname fun <- groupMembers defs]

-- | Scan a top-level function.  Indicate that the function is used outside of
--   the scanned code.
tailCallScanTopLevelFunction :: FunDef -> TailCallScan
tailCallScanTopLevelFunction def =
  tailCallScanDefs (Rec [def]) (use $ definiendum def)

-- | Create the tail-call graph of a top-level function.
-- Return the set of root nodes and the graph.
mkTailCallGraph :: FunDef -> ([Node], Gr Var ())
mkTailCallGraph fdef = 
  let ObservedTailCalls roots defs edges =
        tailCallScanTopLevelFunction fdef no_context IntMap.empty
        where
          no_context = internalError "mkTailCallGraph: No calling context"
      
      -- Get the set of roots and the set of all defined functions.
      root_set = Set.fromList roots
      all_nodes = Set.fromList defs -- Making a set removes duplicates
      node_map :: Map.Map Var Node
      node_map = Map.fromList $ zip (Set.toList all_nodes) [1..]
      root_nodes = [node_map Map.! v | v <- Set.toList root_set]

      graph_edges =
        [(node_map Map.! s, node_map Map.! d, ())
        | (s, d) <- edges, not $ d `Set.member` root_set]
      graph_nodes = [(n, l) | (l, n) <- Map.assocs node_map]
      graph = mkGraph graph_nodes graph_edges
  in (root_nodes, graph)

-- | For each root node of the tail-call graph, list its join points
type JoinPoints = [(Var, [Var])]

getJoinPoints :: FunDef -> JoinPoints
getJoinPoints fdef =
  let -- Get the tail call graph
      (roots, gr) = mkTailCallGraph fdef

      -- Start with the reachability graph
      endpoints = [(root, reachable root gr) | root <- roots]

      -- If a node is reachable from multiple roots, remove it and make it its
      -- own endpoint
      multiple_endpoints = [n | n <- nodes gr, memberN 2 n (map snd endpoints)]
      f_endpoints = [(n, [n]) | n <- multiple_endpoints] ++
                    [(n, ns List.\\ multiple_endpoints) | (n, ns) <- endpoints]

      getlab node = case lab gr node
                    of Just l -> l
                       Nothing -> internalError "getJoinPoints"

      -- Remove a node from its own reachability list.  By definition, a
      -- function is not is own join point.
      join_points = [(n, delete n ns) | (n, ns) <- f_endpoints]
  in [(getlab n, map getlab e) | (n, e) <- join_points]
  where
    -- memberN n x xss -> True if x appears in at least n members of xss 
    memberN 0 _ _        = True
    memberN _ _ []       = False
    memberN n x (xs:xss) = let n' = if x `elem` xs then n - 1 else n
                           in memberN n' x xss

-------------------------------------------------------------------------------

-- | Labelling of join points and join point calls
type Label a = Set.Set Var -> a -> a

labelFunDef :: Label FunDef
labelFunDef join_points (Def v f) =
  let f' = labelFun join_points f
      labeled_f =
        if v `Set.member` join_points
        then labelJoinPointFun f'
        else f'
  in Def v labeled_f

labelJoinPointFun f = f {funConvention = JoinCall}

labelFun :: Label Fun
labelFun join_points f = changeFunBody (labelStm join_points) f

labelStm :: Label Stm
labelStm join_points s =
  case s
  of LetE params rhs body ->
       -- RHS cannot be a tail call, so it won't be labeled
       LetE params rhs (continue body)
     LetrecE defs body ->
       LetrecE (fmap (labelFunDef join_points) defs) (continue body)
     SwitchE scr alts ->
       SwitchE scr [(l, continue s) | (l, s) <- alts]
     ReturnE atom ->
       ReturnE (label_tail_call atom)
     ThrowE x ->
       ThrowE x
  where
    continue s = labelStm join_points s

    -- Set the calling convention on atoms that are tail calls to a join point
    label_tail_call (CallA _ (VarV op) args)
      | op `Set.member` join_points = CallA JoinCall (VarV op) args

    label_tail_call atom = atom

-------------------------------------------------------------------------------

-- | Find and annotate join points in one top-level function
convertJoinPointsDef :: FunDef -> FunDef
convertJoinPointsDef def =
  let join_points_list = getJoinPoints def
      join_points_set = Set.fromList $ concatMap snd join_points_list
  in labelFunDef join_points_set def

convertJoinPointsGroup :: Group GlobalDef -> Group GlobalDef
convertJoinPointsGroup grp = fmap convert_def grp
  where
    convert_def (GlobalFunDef fdef) = GlobalFunDef (convertJoinPointsDef fdef)
    convert_def (GlobalDataDef ddef) = GlobalDataDef ddef

convertJoinPoints :: Module -> IO Module
convertJoinPoints mod = do
  -- Globally rename functions
  rn_mod <- withTheLLVarIdentSupply $ \var_ids ->
    runFreshVarM var_ids $ renameModule RenameFunctions emptyRenaming mod
  
  -- Convert all join points
  return $ mod {moduleGlobals = map convertJoinPointsGroup $ moduleGlobals mod}