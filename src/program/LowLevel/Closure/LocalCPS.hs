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
        continuationsSet,
        lookupCont, needsContinuationCall,
        Lattice(..),
        identifyLocalContinuations)
where

import Prelude hiding(mapM)

import Control.Applicative hiding(empty)
import Control.Monad hiding(mapM, forM, join)
import qualified Data.HashTable as HashTable
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

-- | Get the set of all continuations mentioned in the mapping
continuationsSet :: RConts -> Set.Set Var
continuationsSet rconts = Set.fromList [k | RCont k _ <- IntMap.elems rconts]

singletonRConts :: Var -> RCont -> RConts
singletonRConts v rc = IntMap.singleton (fromIdent $ varID v) rc

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
-- Scanning to find all functions defined in a piece of code.

definedFunctions :: LFunDef -> [Var]
definedFunctions def = definedFunctionsDef def []

definedFunctionsDef (Def v f) xs = v : definedFunctionsStm (funBody f) xs

definedFunctionsStm stm xs =
  case stm
  of LetLCPS _ _ _ body -> definedFunctionsStm body xs
     LetrecLCPS defs _ body ->
       let body_xs = definedFunctionsStm body xs
       in foldr definedFunctionsDef body_xs $ groupMembers defs
     SwitchLCPS _ alts ->
       foldr definedFunctionsStm xs (map snd alts)
     ReturnLCPS _ -> xs
     ThrowLCPS _ -> xs

-------------------------------------------------------------------------------
-- Scanning to identify LCPS candidates.  A scan computes return continuations
-- of local functions.

-- | The set of local functions, and their arities.
--   Only local functions are considered for the local CPS transformation;
--   other variables are ignored.  To be CPS-transformed, a function has to
--   be called with the right number of arguments.
type Relevant = IntMap.IntMap Int

type RContHT = HashTable.HashTable Var RCont

-- | Assign a function's return continuation.
--   Join the new information with whatever was in the hash table before.
assignCont :: RContHT -> Var -> RCont -> IO ()
assignCont hashtable v cont = do
  -- Join new and old values
  m_old_cont <- HashTable.lookup hashtable v
  let old_cont = fromMaybe bottom m_old_cont
      new_cont = join old_cont cont
  when (new_cont /= old_cont) $
    void $ HashTable.update hashtable v new_cont

-- | Look up the return continuation assigned to the given variable.
--   If not in the map, then no continuations (bottom) have been assigned.
lookupContSet :: RContHT -> Var -> IO RCont
lookupContSet hashtable v = do
  mcont <- HashTable.lookup hashtable v
  return $ fromMaybe bottom mcont

-- | A scan to identify LCPS candidates.
--
--   Scanning is an imperative algorithm that generates a map assigning
--   a set of continuations to each local function.
newtype Scan =
  Scan {runScan :: RContHT      -- Map from local function to continuation
                -> Relevant     -- In-scope local functions
                -> [ValueType]  -- Current function's return types
                -> RCont        -- Current function's return continuation
                -> IO ()}

instance Monoid Scan where
  {-# INLINE mempty #-}
  {-# INLINE mappend #-}
  {-# INLINE mconcat #-}
  mempty = Scan $ \_ _ _ _ -> return ()
  mappend (Scan f1) (Scan f2) = Scan $ \hashtable r rtypes c -> do
    f1 hashtable r rtypes c
    f2 hashtable r rtypes c
  mconcat scans = Scan $ \hashtable r rtypes c -> do
    sequence_ [f hashtable r rtypes c | Scan f <- scans]

-- | Set the return continuation of the scanned code.  The return continuation
--   is what executes after the scanned code finishes executing.  The return
--   continuation is taken from the current function, so it has the same
--   return type as the current function.
setCont :: Var -> Scan -> Scan
setCont cont_var (Scan f) = Scan $ \hashtable r rtypes _ ->
  f hashtable r rtypes (RCont cont_var rtypes)

-- | Record the variable's return continuation.
--
--   If the variable is not a candidate for transformation, nothing happens.
tellRCont :: Var -> RCont -> Scan
tellRCont v c = Scan $ \hashtable relevant _ _ ->
  if fromIdent (varID v) `IntMap.member` relevant
  then assignCont hashtable v c
  else return ()

-- | Record the continuation's return continuation.
--
--   For every labeled statement, its continuation is the current continuation.
tellContCont :: Var -> Scan
tellContCont v = Scan $ \hashtable _ _ rc ->
  assignCont hashtable v rc

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
tellCurrentRCont v n_args = Scan $ \hashtable relevant _ rc ->
  case IntMap.lookup (fromIdent $ varID v) relevant
  of Nothing -> return ()
     Just arity | arity == n_args -> assignCont hashtable v rc
                | otherwise       -> assignCont hashtable v Top

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
scanDefGroup group scan_body = Scan $ \hashtable relevant rtypes rcont -> do
  let local_relevant = foldr add_relevant relevant arities
        where
          add_relevant (v, a) r = IntMap.insert (fromIdent $ varID v) a r

  -- Scan the body to find calls of local functions
  runScan scan_body hashtable local_relevant rtypes rcont

  -- Scan the local functions until a fixed point is reached
  scan_until_convergence hashtable local_relevant
  where
    -- Names and arities of functions in the definition group
    arities :: [(Var, Int)]
    arities = [(definiendum def, length $ funParams $ definiens def)
              | def <- groupMembers group]
    definienda = map fst arities 

    -- Scan a function definition.  Look up the function's continuation in
    -- the given RConts map.
    scan_def hashtable relevant return_continuation (Def v f) =
      let rtypes = funReturnTypes f
      in runScan (scanStm $ funBody f) hashtable relevant rtypes return_continuation

    -- Scan the group, updating continuation info, until the results converge.
    scan_until_convergence :: RContHT -> Relevant -> IO ()
    scan_until_convergence hashtable relevant = do
      -- Look up the continuations currently assigned to each local function
      mapM (lookupContSet hashtable) definienda >>= iterate
      where
        iterate old_conts = do
          -- Scan all functions, using the continuation info that's known so far
          zipWithM_ (scan_def hashtable relevant) old_conts $ groupMembers group

          -- If any functions have changed, then repeat
          new_conts <- mapM (lookupContSet hashtable) definienda
          if new_conts /= old_conts
            then iterate new_conts
            else return ()

scanStm :: LStm -> Scan
scanStm statement =
  case statement
  of LetLCPS params rhs@(CallA {}) v body ->
       -- The RHS could be CPS-transformed.
       -- The continuation of the body is the current continuation.
       -- Record it in case the body will be transformed into a real function.
       tellContCont v `mappend`
       -- The RHS's continuation is the body
       setCont v (scanAtom rhs) `mappend`
       scanStm body
     LetLCPS params rhs v body ->
       -- RHSes other than calls will not be CPS-transformed, so don't
       -- generate info for this continuation
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
reachableConts initial_reachable_set all_rconts = {-# SCC "reachableConts" #-}
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
identifyLocalContinuations :: LFunDef -> IO RConts
identifyLocalContinuations top_level_def@(Def v f) = do
  -- Determine continuations for all functions, including every
  -- hypothetical continuation point.
  rconts_table <- HashTable.new (==) (HashTable.hashInt . fromIdent . varID)
  ({-# SCC "runScan" #-}
    runScan (scanStm (funBody f)) rconts_table IntMap.empty (funReturnTypes f) Top)
  rconts_list <- HashTable.toList rconts_table
  let all_rconts = IntMap.fromList [(fromIdent $ varID v, c) | (v, c) <- rconts_list]


  -- Retain only the continuations that are reachable from a local function
  let all_funs = definedFunctions top_level_def
  let all_fun_ids = IntSet.fromList $ map (fromIdent . varID) all_funs
  let real_rconts = reachableConts all_fun_ids all_rconts

  -- Add an entry for the top-level function
  return $ IntMap.insert (fromIdent $ varID v) Top real_rconts
