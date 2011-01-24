{-| Selection of functions for closure conversion.

Based on which functions are 
-}

module LowLevel.ClosureSelect(findFunctionsToHoist) where
       
import Control.Monad
import qualified Data.Graph.Inductive as Graph
import qualified Data.Graph.Inductive.Query.DFS as Graph
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid
import qualified Data.Set as Set

import Common.Error
import LowLevel.Print
import LowLevel.Syntax
import LowLevel.Types
import LowLevel.Build
import Globals

-------------------------------------------------------------------------------
-- Closure constraints

-- | An implication constraint used to identify functions that are dead and 
--   functions that should be hoisted.  Variables that appear in implication
--   constraints are function variables bound in @Letrec@ statements.  If a
--   function is 'Implied', it means that some property (is-dead or
--   should-hoist) is true of that function.
data Impl = Implied Var         -- ^ The variable is true
          | [Var] :=> Var       -- ^ True if any prerequisite is true

implVariables :: Impl -> [Var]
implVariables (Implied v) = [v]
implVariables (vs :=> v) = v : vs

-- | Create an implication graph
toImplGraph :: [Impl] -> (Map.Map Var Graph.Node, Graph.Gr Var ())
toImplGraph impls =
  let nodes = zip [1..] $ nub $ concatMap implVariables impls
      nodeLabelMap = Map.fromList [(lab, id) | (id, lab) <- nodes]
      edges = [(id1, id2, ()) | prereqs :=> target <- impls
                              , let id2 = nodeLabelMap Map.! target
                              , prereq <- prereqs
                              , let id1 = nodeLabelMap Map.! prereq]
      start_nodes = [nodeLabelMap Map.! lab | Implied lab <- impls]
  in (nodeLabelMap, Graph.mkGraph nodes edges)

-- | Find all implied variables in the implication graph
solveImplications :: [Impl] -> Set.Set Var
solveImplications impls =
  let (node_map, gr) = toImplGraph impls
      start_implications = [node_map Map.! v | Implied v <- impls]
      nodes = Graph.labNodes gr
      impl_nodes = Graph.dfs start_implications gr
  in Set.fromList [fromMaybe not_found $ lookup n nodes | n <- impl_nodes]
  where
    not_found = internalError "solveImplications"

-------------------------------------------------------------------------------
-- Constraint generation
--

-- | Constraints determining which functions should be hoisted.
type Constraints = [Impl]

-- | Context in which a function is used.  Keep track of all function
--   definitions that enclose the use but not the definition.
--   If any of them are marked for hoisting, then the function must be
--   hoisted.
data Context = Context [Var] ContextBase

data ContextBase = TopContext | LamContext

-- | Information about the definitions of functions that are candidates for  
--   hoisting.
type FunMap = Map.Map Var (Int, Context)

-- | A scan for computing hoisting.
type Scan = FunMap -> Constraints

enterLambda :: Scan -> Scan
enterLambda f = \m -> f (Map.map use_lam_context m)
  where
    use_lam_context (arity, _) = (arity, Context [] LamContext)

enterFun :: Var -> Scan -> Scan
enterFun defining_fun f = \m -> f (Map.map add_to_context m)
  where
    add_to_context (arity, Context ctx base) =
      (arity, Context (defining_fun:ctx) base)

-- | Track some more function variables
enterLetrec :: [(Var, Int)] -> Scan -> Scan
enterLetrec functions f = \m -> f (insert_functions m)
  where
    insert_functions m =
      foldr (uncurry Map.insert) m [(v, (a, Context [] TopContext)) | (v, a) <- functions]

-- | A function was tail-called with the specified number of arguments
tailCalled :: Var -> Int -> Scan
tailCalled v num_args arity_map
  | Just (arity, Context parents base) <- arity_entry,
    arity <= num_args =
      case base
      of TopContext -> [parents :=> v]
         LamContext -> [Implied v]
         
  | Just _ <- arity_entry =
      [Implied v]               -- Undersaturated application
  
  | otherwise = []              -- Not a hoisting candidate
  where
    arity_entry = Map.lookup v arity_map

-- | A function was referenced in some way other than a tail call
referenced :: Var -> Scan
referenced v arity_map
  | v `Map.member` arity_map = [Implied v]
  | otherwise                = []


scanValue :: Val -> Scan
scanValue val =
  case val
  of VarV v -> referenced v
     LitV _ -> mempty
     LamV f -> enterLambda $ scanStm $ funBody f
     RecV {} -> internalError "scanValue"

scanValues vals = mconcat (map scanValue vals)

scanAtom :: Bool -> Atom -> Scan
scanAtom is_tail atom =
  case atom
  of ValA vs           -> scanValues vs
     CallA _ op args   -> scan_call op args
     PrimA _ args      -> scanValues args
     UnpackA r arg     -> scanValue arg
     _                 -> internalError "scanAtom"
  where
    scan_call op args =
      let op_scan =
            case op
            of VarV v | is_tail -> tailCalled v (length args)
               _                -> scanValue op 
      in op_scan `mappend` scanValues args

scanStm :: Stm -> Scan
scanStm statement =
  case statement
  of LetE params rhs body ->
       scanAtom False rhs `mappend` scanStm body
     LetrecE defs stm ->
       enterLetrec (map get_arity defs) $
       mconcat (map scanDef defs) `mappend` scanStm stm
     SwitchE cond alts ->
       scanValue cond `mappend` mconcat [scanStm s | (_, s) <- alts] 
     ReturnE atom -> scanAtom True atom
  where
    get_arity (Def v f) = (v, length $ funParams f)
    
scanDef :: FunDef -> Scan
scanDef (Def v f) = enterFun v $ scanStm $ funBody f

scanTopLevelDef :: FunDef -> [Impl]
scanTopLevelDef def = scanDef def Map.empty

-- | Find all functions that should be hoisted in a top-level
-- function definition.
findFunctionsToHoist :: FunDef -> Set.Set Var
findFunctionsToHoist def =
  let scan_implications = scanTopLevelDef def
      -- Top-level functions always become closures
      implications = Implied (definiendum def) : scan_implications
  in solveImplications implications
       