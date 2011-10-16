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
data RCont = Bottom | RCont !Var | Top
           deriving (Eq, Ord, Show)

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
  join (RCont v1) (RCont v2) = if v1 == v2 then RCont v1 else Top
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
needsContinuationCall rconts (RCont cont_var) atom =
  case atom
  of CallA _ (VarV op_var) _ ->
       let callee_rcont = IntMap.lookup (fromIdent $ varID op_var) rconts

       -- We must insert a continuation call, unless the callee will
       -- call the continuation for us
       in if callee_rcont == Just (RCont cont_var)
          then Nothing
          else (Just cont_var)
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
--   The parameters are the set of local functions and the current statement's 
--   return continuation.
newtype Scan = Scan {runScan :: Relevant -> RCont -> RConts}

instance Monoid Scan where
  mempty = Scan (\_ _ -> bottom)
  mappend (Scan f1) (Scan f2) = Scan (\r c -> f1 r c `join` f2 r c)

addRelevant :: Var -> Int -> Scan -> Scan
addRelevant v a (Scan f) =
  Scan $ \r -> f (IntMap.insert (fromIdent $ varID v) a r)

addRelevants :: [(Var, Int)] -> Scan -> Scan
addRelevants vs s = foldr (uncurry addRelevant) s vs

-- | Set the return continuation of the scanned code.  The return continuation
--   is what executes after the scanned code finishes executing.
setCont :: RCont -> Scan -> Scan
setCont rc (Scan f) = Scan (\r _ -> f r rc)

-- | Record the variable's return continuation.
--
--   If the variable is not a candidate for transformation, nothing happens.
tellRCont :: Var -> RCont -> Scan
tellRCont v c = Scan $ \relevant _ ->
  if fromIdent (varID v) `IntMap.member` relevant
  then singletonRConts v c
  else IntMap.empty

-- | Record the continuation's return continuation.
--
--   For every labeled statement, its continuation is the current continuation.
tellContCont :: Var -> Scan
tellContCont v = Scan $ \_ rc -> singletonRConts v rc

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
tellCurrentRCont v n_args = Scan $ \relevant rc ->
  case IntMap.lookup (fromIdent $ varID v) relevant
  of Nothing -> IntMap.empty
     Just arity | arity == n_args -> singletonRConts v rc
                | otherwise       -> singletonRConts v Top

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
scanDefGroup group scan_body = Scan $ \relevant rcont ->
  let -- Scan the body to find calls of local functions
      body_conts = runScan (in_scope scan_body) relevant rcont
      
      -- Scan each function, using its return continuation in the body.
      -- Iterate until a fixed point is reached.
      fun_conts = scan_until_convergence relevant body_conts
  in join body_conts fun_conts
  where
    -- Names and arities of functions in the definition group
    arities :: [(Var, Int)]
    arities = [(definiendum def, length $ funParams $ definiens def)
              | def <- groupMembers group]
    in_scope scan = addRelevants arities scan
    
    -- Scan a function definition.  Look up the function's continuation in
    -- the given RConts map.
    scan_def relevant rconts (Def v f) =
      let return_continuation = lookupContSet v rconts
      in runScan (in_scope $ scanStm $ funBody f) relevant return_continuation
    
    scan_group_once :: Relevant -> RConts -> RConts -> RConts
    scan_group_once relevant body_conts given_conts =
      let rconts = join body_conts given_conts
      in joinList [scan_def relevant rconts d | d <- groupMembers group]
    
    scan_until_convergence :: Relevant -> RConts -> RConts
    scan_until_convergence relevant body_conts =
      let steps =
            -- Iterate the operation.  Discard the initial value.
            tail $ iterate (scan_group_once relevant body_conts) bottom
      in case find (uncurry (==)) $ zip steps (tail steps)
         of Just (final, _) -> join body_conts final

scanStm :: LStm -> Scan
scanStm statement =
  case statement
  of LetLCPS params rhs v body ->
       -- The continuation of the body is the current continuation.
       -- Record it in case the body will be transformed into a real function.
       tellContCont v `mappend`
       -- The RHS's continuation is the body
       setCont (RCont v) (scanAtom rhs) `mappend`
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
-- Entry point of module                   

-- | Identify local continuations within a top-level function.  If a local 
--   function's continuation is a unique statement, then that will be recorded
--   in a mapping.
identifyLocalContinuations :: LFunDef -> RConts
identifyLocalContinuations (Def v f) =
  let rconts = runScan (scanStm (funBody f)) IntMap.empty Top
  in IntMap.insert (fromIdent $ varID v) Top rconts
