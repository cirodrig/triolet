{-| Local continuation-passing transformation.

This transformation reorganizes local functions in a way that increases the
number of functions that can be translated to local procedures, which execute
more efficiently than hoisted functions.

The program should be lambda-converted before running the transformation.
LCPS creates non-minimal definition groups, so DCE should be run afterwards to
simplify the definition groups.

The transformation is described in the paper
\"Optimizing Nested Loops Using Local CPS Conversion\" by John Reppy,
in Proc. Higher-Order and Symbolic Computation 15, p. 161-180, 2002.
-}

module LowLevel.Closure.LocalCPS
       (RConts, RCont(..),
        lookupCont, needsContinuationCall,
        Lattice(..),
        identifyLocalContinuations)
where

import Prelude hiding(mapM)

import Control.Applicative hiding(empty)
import Control.Monad hiding(mapM, forM, join)
import qualified Data.Set as Set
import Data.Traversable
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import Data.List
import Data.Maybe
import Data.Monoid
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import LowLevel.CodeTypes
import LowLevel.FreshVar
import LowLevel.Print
import LowLevel.Syntax
import LowLevel.Closure.LocalCPSAnn
import Globals

-- | The set of return continuations of a function.
--
--   If the set contains zero or one values, we represent it precisely.
--   Larger sets are rounded up to 'Top'.
--
--   Each continuation has a return type.  The return type is stored here.
data RCont = Bottom | RCont !Var [ValueType] | Top

instance Eq RCont where
  Bottom     == Bottom      = True
  RCont v1 _ == RCont v2 _  = v1 == v2
  Top        == Top         = True 
  _          == _           = False

instance Ord RCont where
  compare Bottom       Bottom       = EQ
  compare Bottom       _            = LT
  compare (RCont _ _)  Bottom       = GT
  compare (RCont v1 _) (RCont v2 _) = compare v1 v2
  compare (RCont _ _ ) Top          = LT
  compare Top          Top          = EQ
  compare Top          _            = GT

instance Show RCont where
  show Top = "Top"
  show Bottom = "Bottom"
  show (RCont v ts) = "RCont " ++ show v ++ showList (map pprValueType ts) []

-- | A value supporting join semi-lattice operations.
class Lattice a where
  bottom :: a
  join :: a -> a -> a

joinList :: Lattice a => [a] -> a
joinList xs = foldr join bottom xs

instance Lattice RCont where
  bottom = Bottom
  join Bottom x = x
  join x Bottom = x
  join (RCont v1 r) (RCont v2 _) = if v1 == v2 then RCont v1 r else Top
  join _ _ = Top

instance Lattice a => Lattice (IntMap.IntMap a) where
  bottom = IntMap.empty
  join x y = IntMap.unionWith join x y

-- | A mapping from variable to return continuation.
type RConts = IntMap.IntMap RCont

singletonRConts :: Var -> RCont -> RConts
singletonRConts v rc = IntMap.singleton (fromIdent $ varID v) rc

-- | Look up the return continuation assigned to the given variable.
--   If not in the map, then no continuations (bottom) have been assigned.
lookupContSet :: Var -> RConts -> RCont
lookupContSet v m = fromMaybe bottom $ IntMap.lookup (fromIdent $ varID v) m

-- | Look up the return continuation assigned to the given variable.
lookupCont :: Var -> RConts -> Maybe RCont
lookupCont v m = IntMap.lookup (fromIdent $ varID v) m

-------------------------------------------------------------------------------
-- Queries on the computed continuation data

-- | Given an atom in tail position, decide whether the local CPS
--   transformation will insert a continuation call after this atom.
--   The 'RConts' data produced by analysis is used in making the decision.
needsContinuationCall :: RConts -> RCont -> Atom -> Maybe Var
needsContinuationCall rconts (RCont cont_var _) atom =
  case atom
  of CallA _ (VarV op_var) _ ->
       let callee_rcont = IntMap.lookup (fromIdent $ varID op_var) rconts

       -- We must insert a continuation call, unless the callee will
       -- call the continuation for us
       in case callee_rcont 
          of Just (RCont cont_var _) -> Nothing
             _ -> Just cont_var
     _ -> Just cont_var
                
needsContinuationCall _ _ _ =
  -- The current function does not have a known continuation, so it will 
  -- not be transformed
  Nothing

-------------------------------------------------------------------------------
-- Scanning to identify LCPS candidates.  A scan computes return continuations
-- of local functions.

-- | The set of local functions, and their arities.
--   Only local functions are considered for the local CPS transformation;
--   other variables are ignored.  To be CPS-transformed, a function has to
--   be called with the right number of arguments.
type Relevant = IntMap.IntMap Int

-- | A scan to identify LCPS candidates.
--
--   The parameters are the set of local functions, the current function's 
--   return type, and the current statement's return continuation.
--
--   Scanning produces a continuation map and the set of local functions that
--   were seen.
newtype Scan = Scan {runScan :: Relevant -> [ValueType] -> RCont
                             -> (RConts, Set.Set Var)}

joinScanResult (r1, s1) (r2, s2) = (join r1 r2, Set.union s1 s2)

joinScanResults = foldr joinScanResult emptyScanResult

emptyScanResult = (bottom, Set.empty)

instance Monoid Scan where
  mempty = Scan (\_ _ _ -> emptyScanResult)
  mappend (Scan f1) (Scan f2) = Scan $ \r rtypes c ->
    joinScanResult (f1 r rtypes c) (f2 r rtypes c)

addRelevant :: Var -> Int -> Scan -> Scan
addRelevant v a (Scan f) =
  Scan $ \r -> f (IntMap.insert (fromIdent $ varID v) a r)

addRelevants :: [(Var, Int)] -> Scan -> Scan
addRelevants vs s = foldr (uncurry addRelevant) s vs

-- | Set the return continuation of the scanned code.  The return continuation
--   is what executes after the scanned code finishes executing.  The return
--   continuation is taken from the current function, so it has the same
--   return type as the current function.
setCont :: Var -> Scan -> Scan
setCont cont_var (Scan f) = Scan $ \r rtypes _ ->
  f r rtypes (RCont cont_var rtypes)

-- | Record the variable's return continuation.
--
--   If the variable is not a candidate for transformation, nothing happens.
tellRCont :: Var -> RCont -> Scan
tellRCont v c = Scan $ \relevant _ _ ->
  if fromIdent (varID v) `IntMap.member` relevant
  then (singletonRConts v c, Set.empty)
  else (IntMap.empty, Set.empty)

-- | Record the continuation's return continuation.
--
--   For every labeled statement, its continuation is the current continuation.
tellContCont :: Var -> Scan
tellContCont v = Scan $ \_ _ rc -> (singletonRConts v rc, Set.empty)

-- | Record that some function definitions were seen.
tellDefs :: [Var] -> Scan
tellDefs vs = Scan $ \_ _ _ -> (bottom, Set.fromList vs)

-- | The variable was called with some arguments.
--
--   If the variable is not a candidate for transformation, nothing happens.
--
--   If it's a saturated call of a known function, then record the current
--   return continuation as the variable's return continuation.
--
--   If it's an under- or oversaturated call, then the function's return
--   continuation becomes unknown.
tellCurrentRCont :: Var -> Int -> Scan
tellCurrentRCont v n_args = Scan $ \relevant _ rc ->
  case IntMap.lookup (fromIdent $ varID v) relevant
  of Nothing -> emptyScanResult
     Just arity | arity == n_args -> (singletonRConts v rc, Set.empty)
                | otherwise       -> (singletonRConts v Top, Set.empty)

scanValue :: Val -> Scan
scanValue value =
  case value
  of VarV v -> tellRCont v Top  -- Variable has unknown return continuation
     LitV _ -> mempty
     RecV _ vs -> scanValues vs

scanValues vs = mconcat $ map scanValue vs

scanAtom :: Atom -> Scan
scanAtom atom =
  case atom
  of ValA vs -> scanValues vs
     CallA _ (VarV callee) vs ->
       -- The callee is called with the current return continuation
       tellCurrentRCont callee (length vs) `mappend`
       scanValues vs
     CallA _ v vs ->
       scanValues (v:vs)
     PrimA _ vs -> scanValues vs
     PackA _ vs -> scanValues vs
     UnpackA _ v -> scanValue v

scanDefGroup :: Group (Def LFun) -> Scan -> Scan
scanDefGroup group scan_body = Scan $ \relevant rtypes rcont ->
  let -- Scan the body to find calls of local functions
      (body_conts, body_vars) =
        runScan (in_scope scan_body) relevant rtypes rcont
      
      -- Scan each function, using its return continuation in the body.
      -- Iterate until a fixed point is reached.
      (fun_conts, fun_vars) = scan_until_convergence relevant body_conts
      
      conts = join body_conts fun_conts
      vars = body_vars `Set.union` fun_vars `Set.union` Set.fromList definienda
  in (conts, vars)
  where
    definienda = map definiendum $ groupMembers group

    -- Names and arities of functions in the definition group
    arities :: [(Var, Int)]
    arities = [(definiendum def, length $ funParams $ definiens def)
              | def <- groupMembers group]
    in_scope scan = addRelevants arities scan
    
    -- Scan a function definition.  Look up the function's continuation in
    -- the given RConts map.
    scan_def relevant rconts (Def v f) =
      let return_continuation = lookupContSet v rconts
          rtypes = funReturnTypes f
      in runScan (in_scope $ scanStm $ funBody f) relevant rtypes return_continuation

    -- Perform a scan of the definition group, using the given continuations
    -- as a starting point.
    --
    -- The set of variables is the same in every scan, so we just retain the
    -- final result.
    scan_group_once :: Relevant -> RConts
                    -> (RConts, Set.Set Var)
                    -> (RConts, Set.Set Var)
    scan_group_once relevant body_conts (given_conts, _) =
      let rconts = join body_conts given_conts
      in joinScanResults [scan_def relevant rconts d | d <- groupMembers group]

    -- Scan the group, updating continuation info, until the results converge.
    scan_until_convergence :: Relevant -> RConts -> (RConts, Set.Set Var)
    scan_until_convergence relevant body_conts =
      let steps =
            -- Iterate the operation.  Discard the initial value.
            tail $ iterate (scan_group_once relevant body_conts) emptyScanResult
      in case find (\((x, _), (y, _)) -> x == y) $ zip steps (tail steps)
         of Just (final, _) -> final

scanStm :: LStm -> Scan
scanStm statement =
  case statement
  of LetLCPS params rhs v body ->
       -- The continuation of the body is the current continuation.
       -- Record it in case the body will be transformed into a real function.
       tellContCont v `mappend`
       -- The RHS's continuation is the body
       setCont v (scanAtom rhs) `mappend`
       scanStm body
     LetrecLCPS defs _ body ->
       scanDefGroup defs $ scanStm body
     SwitchLCPS scr alts ->
       scanValue scr `mappend` mconcat [scanStm s | (_, s) <- alts]
     ReturnLCPS atom ->
       scanAtom atom
     ThrowLCPS val ->
       scanValue val

-------------------------------------------------------------------------------
-- Reachability analysis

-- | Interpreting 'RConts' as a graph, find the subgraph that is reachable from
--   the given starting set.
reachableConts initial_reachable_set all_rconts =
  accumulate initial_reachable_set
  where
    -- Compute the reachable set
    accumulate known_reachable = let

      -- Get the reachable part of the map
      rconts = IntMap.filterWithKey reachable all_rconts
        where reachable var_id _ = var_id `IntSet.member` known_reachable
    
      -- Find new reachable nodes
      new_reachable = IntSet.fromList [fromIdent $ varID f'
                                      | (_, RCont f' _) <- IntMap.toList rconts]

      -- If no new nodes found, we're done
      in if new_reachable `IntSet.isSubsetOf` known_reachable
         then rconts
         else accumulate $ IntSet.union new_reachable known_reachable

-------------------------------------------------------------------------------
-- Entry point of module                   

-- | Identify local continuations within a top-level function.  If a local 
--   function's continuation is a unique statement, then that will be recorded
--   in a mapping.
identifyLocalContinuations :: LFunDef -> RConts
identifyLocalContinuations (Def v f) = let
  -- Determine continuations for all functions, including every
  -- hypothetical continuation point.
  (all_rconts, all_funs) =
    runScan (scanStm (funBody f)) IntMap.empty (funReturnTypes f) Top

  -- Retain only the continuations that are reachable from a local function
  all_fun_ids = IntSet.fromList $ map (fromIdent . varID) $ Set.toList all_funs
  real_rconts = reachableConts all_fun_ids all_rconts

  -- Add an entry for the top-level function
  in IntMap.insert (fromIdent $ varID v) Top real_rconts
