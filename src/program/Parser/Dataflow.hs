
{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving #-}

module Parser.Dataflow
       (DFException, analyzeLivenessInFunc, analyzeLivenessInLFunc,
        getStmtDefinitions)
where

import Control.Exception
import Control.Monad
import Control.Monad.Identity
import Control.Monad.Trans
import Compiler.Hoopl
import Compiler.Hoopl.Passes.Dominator
import Data.List(foldl', elemIndex, nub, intercalate)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Typeable
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.SourcePos
import Common.Worklist
import Parser.ParserSyntax hiding(Stmt(..))
import Parser.Control

-- | A dataflow analysis monad.
--   Dataflow analysis keps track of fuel and can report errors.
newtype DFM a = DFM (InfiniteFuelMonad Identity a)
                deriving(Monad, FuelMonad)

runDFM :: DFM a -> a
runDFM (DFM m) = runIdentity $ runWithFuel infiniteFuel m

instance CheckpointMonad DFM where
  type Checkpoint DFM = ()
  checkpoint = return ()
  restart () = return ()

-------------------------------------------------------------------------------
-- Error detection

-- | An error in the input detected by dataflow analysis
data DFException =
  -- | A collection of variables was used without being defined in the
  --   given function
  DFUseBeforeDef
  { excFunctionName :: !PVar
  , excFunctionPos  :: !SourcePos 
  , excVars         :: ![PVar]
  }
  deriving(Typeable)

instance Exception DFException

instance Show DFException where
  show (DFUseBeforeDef fname fpos vars) =
    let var_text = intercalate ", " $ map varName vars
        location = "Error in function " ++ varName fname ++ " at " ++ show fpos ++ ":\n"
        diagnosis = if length vars == 1
                    then "variable may be used before definition: " ++ var_text
                    else "variables may be used before definition: " ++ var_text
    in location ++ diagnosis

-------------------------------------------------------------------------------
-- Finding variable uses and definitions in non-SSA code

type DeltaLiveness = Liveness -> Liveness

type Definitions = Set.Set PVar
type DeltaDefinitions = Definitions -> Definitions

-- | A thing that contains references to variables
class Reference a where
  use :: a -> DeltaLiveness

instance Reference a => Reference [a] where
  use xs l = foldr use l xs

instance Reference a => Reference (Maybe a) where
  use (Just x) = use x
  use Nothing  = id

instance Reference a => Reference (Loc a) where
  use x = use $ unLoc x

instance Reference (Var AST) where
  use v l = Set.insert v l

instance Reference (Expr AST) where
  use (Variable v)     = use v 
  use (Literal _)      = id
  use (Tuple es)       = use es
  use (List es)        = use es
  use (Unary _ e)      = use e
  use (Binary _ e1 e2) = use e1 . use e2
  use (Subscript e es) = use e . use es
  use (Slicing e s)    = use e . use s
  use (ListComp i)     = use i
  use (Generator i)    = use i
  use (Call e es)      = use e . use es
  use (Cond c t f)     = use c . use t . use f
  use (Lambda ps e)    = localKill ps (use e)
  use (Let p rhs e)    = use rhs . localKill p (use e)

instance Reference (Slice AST) where
  use (SliceSlice _ l u s) = use l . use u . use s
  use (ExprSlice e)        = use e

instance Reference (IterFor AST) where
  use (IterFor _ ps e c) = use e . localKill ps (use c)

instance Reference (IterIf AST) where
  use (IterIf _ e c) = use e . use c

instance Reference (IterLet AST) where
  use (IterLet _ p e c) = use e . localKill p (use c)

instance Reference (Comprehension AST) where
  use (CompFor i)  = use i
  use (CompIf i)   = use i
  use (CompLet i)  = use i
  use (CompBody x) = use x

useStmt :: LStmt AST e x -> Fact x Liveness -> Liveness
useStmt stmt liveness =
  -- Compute the set of live variables from 'liveness'
  let liveness_set =
        case unLStmt stmt
        of Assign {}   -> liveness
           DefGroup {} -> liveness
           Assert {}   -> liveness
           Require {}  -> liveness
           Target {}   -> liveness

           -- Control flow statements
           If _ t f    -> let Just l1 = mapLookup (flowLabel t) liveness
                              Just l2 = mapLookup (flowLabel f) liveness
                          in Set.union l1 l2
           Jump l      -> let Just l1 = mapLookup (flowLabel l) liveness
                          in l1
           Return _    -> Set.empty
  in useStmt' stmt liveness_set

-- | Find the variable uses in a statement and add them to the given
--   liveness set.
useStmt' :: LStmt AST e x -> Liveness -> Liveness
useStmt' stmt liveness =
  case unLStmt stmt
  of Assign lhs rhs -> (use rhs . kill lhs) liveness
     -- Read the value produced by 'analyzeLocalFunctionLiveness'
     DefGroup fs l  -> let uses = getLiveness l `Set.union` liveness
                       in foldr killFunc uses $ map unLoc fs
     Assert es      -> use es liveness
     Require v e    -> (use v . use e) liveness
     Target _ _     -> liveness
     If c _ _       -> use c liveness
     Jump l         -> liveness
     Return e       -> use e liveness

-- | A forall annotation declaring type variables and a constraint
useForallAnnotation Nothing f = f
useForallAnnotation (Just (ForallAnnotation params cst)) f =
  localKill params (use cst . f)

-- | Remove a function name from the live-in set
killFunc :: CFunc AST -> DeltaLiveness
killFunc f = kill (sigName $ cfSignature f)

class Definition a where
  -- | Remove variable definitions from a set
  kill :: a -> DeltaLiveness

  -- | Insert variable definitions into a set
  def :: a -> DeltaDefinitions

-- | Kill some local definitions, but do not kill any of the
--   incoming liveness facts.
--
--   This is used for expression-scoped variables like lambda parameters.
localKill :: Definition a => a -> DeltaLiveness -> DeltaLiveness
localKill x d liveness = 
  let local_liveness = d Set.empty
  in kill x local_liveness `Set.union` liveness

instance Definition a => Definition [a] where
  kill xs l = foldr kill l xs
  def xs s  = foldr def s xs

instance Definition (Var AST) where
  kill v l = Set.delete v l
  def v s  = Set.insert v s

instance Definition (Parameter AST) where
  kill (Parameter v ann) = use ann . Set.delete v
  kill (TupleParam ps)   = kill ps
  def (Parameter v ann) = def v
  def (TupleParam ps)   = def ps

defStmt :: LStmt AST e x -> DeltaDefinitions
defStmt stmt =
  case unLStmt stmt
  of Assign params _ -> def params
     DefGroup fs _   -> def $ map (sigName . cfSignature . unLoc) fs
     Assert _        -> id
     Require _ _     -> id
     Target _ _      -> id
     If _ _ _        -> id
     Jump _          -> id
     Return _        -> id

-- | Get all variables defined by a statement and visible to later statements
getStmtDefinitions :: LStmt AST e x -> DeltaDefinitions
getStmtDefinitions = defStmt

-- | Find all variables that are defined in a CFG,
--   without filtering out defs/uses
locallyDefinedVariables :: CFG AST C C -> Definitions
locallyDefinedVariables cfg = foldGraphNodes defStmt cfg Set.empty

-------------------------------------------------------------------------------
-- Non-SSA liveness analysis
  
-- | Get a liveness value that was saved by liveness analysis.
--   It is an error if liveness is not present.
getLiveness :: MLiveness -> Liveness
getLiveness Nothing  = internalError "getLiveness: No liveness information"
getLiveness (Just l) = l

livenessLattice :: DataflowLattice Liveness
livenessLattice = DataflowLattice "liveness" Set.empty join
  where
    join _ (OldFact s) (NewFact s') =
      let change = if s == s' then NoChange else SomeChange
      in (change, Set.union s s')

livenessTransfer :: BwdTransfer (LStmt AST) Liveness
livenessTransfer = mkBTransfer useStmt

livenessAnalysis :: BwdPass DFM (LStmt AST) Liveness
livenessAnalysis = BwdPass livenessLattice livenessTransfer noBwdRewrite

-- | Perform liveness analysis in local function definitions. 
--   Each 'DefGroup' statement is annotated with its liveness information.
analyzeLocalFunctionLiveness :: CFG AST C C -> CFG AST C C
analyzeLocalFunctionLiveness graph = mapGraph compute_liveness graph
  where
    -- Compute liveness and annotate it onto the definition group.
    -- Local function definitions in these functions are recursively analyzed
    -- by 'useFunc'.
    compute_liveness :: LStmt AST e x -> LStmt AST e x
    compute_liveness (LStmt (Loc pos (DefGroup fs _))) =
      let -- Analyze liveness in each function
          (fs', all_usess) = unzip $ map analyzeLivenessInLFunc fs
          all_uses = Set.unions all_usess
          -- Remove the function names from the set of uses
          exposed_uses = foldr killFunc all_uses $ map unLoc fs'
      in LStmt (Loc pos (DefGroup fs' (Just exposed_uses)))

    -- Other statements are unchanged
    compute_liveness s = s

-- | Analyze liveness in a control flow graph.
--   Detect uses of undefined variables and report them as errors.
--
--   Return a function body annotated with local liveness information,
--   the live-in set of each block, and the function's live-in set.
analyzeLiveness :: PVar -> SourcePos -> [Parameter AST] -> Label -> CFG AST C C
                -> (CFG AST C C, Livenesses, Liveness)
analyzeLiveness func_name func_pos params entry graph = let
  -- Analyze local function definitions first
  def_annotated_graph = analyzeLocalFunctionLiveness graph

  -- Analyze control flow in the function
  (_, live_in_map, NothingO) =
    runDFM $ analyzeAndRewriteBwd
             livenessAnalysis (JustC entry) def_annotated_graph
             mapEmpty
  body_live_ins = case mapLookup entry live_in_map
                  of Just l  -> l
                     Nothing -> internalError "analyzeLiveness"

  -- Remove function parameters from the live-in set
  live_ins = kill params body_live_ins

  -- Find undefined uses of local variables
  local_defs = locallyDefinedVariables graph
  undefined_uses = live_ins `Set.intersection` local_defs
  exception = DFUseBeforeDef func_name func_pos (Set.toList undefined_uses)

  in if Set.null undefined_uses 
     then (def_annotated_graph, live_in_map, live_ins)
     else throw exception

-- | Analyze liveness in a function.
--   The function is annotated with liveness information, and its live-in
--   set is returned.
--   Caller should catch 'DFException's.
analyzeLivenessInFunc :: SourcePos -> CFunc AST -> (CFunc AST, Liveness)
analyzeLivenessInFunc func_pos func = let
  -- Analyze the function body
  sig = cfSignature func
  (new_body, livenesses, body_live_in) =
    analyzeLiveness (sigName sig) func_pos (sigParams sig)
    (cfEntry func) (cfBody func)
  func' = func {cfBody = new_body, cfLivenesses = Just livenesses}

  -- Remove the function's type parameters from the live-in set.
  -- Note that the function name is _not_ removed from the live-in set;
  -- the name is not bound in the function definition, but in the
  -- enclosing defgroup or global scope.
  func_live_in =
    let foralls = sigAnnotation sig
        return_type = sigReturnAnnotation sig
    in useForallAnnotation foralls
       (use return_type . Set.union body_live_in)
       Set.empty
  in (func', func_live_in)

-- | Analyze liveness in a located function.
--   The function is annotated with liveness information, and its live-in
--   set is returned.
--   Caller should catch 'DFException's.
analyzeLivenessInLFunc :: LCFunc AST -> (LCFunc AST, Liveness)
analyzeLivenessInLFunc (Loc pos f) =
  let (f', liveness) = analyzeLivenessInFunc pos f
  in (Loc pos f', liveness)

