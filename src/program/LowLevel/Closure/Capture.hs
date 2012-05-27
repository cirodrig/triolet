{-|  Free variable analysis.

The analysis in this module identifies the free variables of each local function
and continuation in one top-level function definition.  The set of free
variables is used for variable capture during closure conversion.
-}

{-# Language FlexibleInstances, TypeSynonymInstances,
             GeneralizedNewtypeDeriving #-}
module LowLevel.Closure.Capture
       (Free, findCapturedVariables)
where

import Prelude hiding(mapM)
import Control.Applicative
import Control.Monad hiding(mapM, forM)
import Control.Monad.Reader hiding(mapM, forM)
import Control.Monad.RWS hiding(mapM, forM)
import Control.Monad.Trans
import Data.Array.IO
import Data.Function
import qualified Data.Graph.Inductive as Graph
import qualified Data.Graph.Inductive.Query.DFS as Graph
import qualified Data.HashTable as HashTable
import qualified Data.IntMap as IntMap
import Data.Traversable
import Data.IORef
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid
import qualified Data.Set as Set
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Common.MonadLogic
import Common.Error
import Common.Identifier
import Common.Supply
import Common.Worklist
import LowLevel.CodeTypes
import LowLevel.FreshVar
import LowLevel.Print
import LowLevel.Syntax
import LowLevel.Types
import LowLevel.Build
import LowLevel.Closure.CCInfo
import LowLevel.Closure.Code
import LowLevel.Closure.Hoisting
import LowLevel.Closure.LocalCPSAnn
import qualified LowLevel.Closure.LocalCPS as LocalCPS
import Globals

debug = False

-------------------------------------------------------------------------------
-- Constraints

-- | A set of free variables.
type Free = Set.Set Var

-- | An inherited free variable set.  If function F calls function G, and
--   G has captured a variable, then F must be able to pass that variable to G.
--   Unless the varible was defined by F, F must also capture the variable.
--
--   @FreeInherit (fromList [(v1, s1), ...]@ means that, for each function 
--   @v_i@ and set of variables @s_i@, the current function inherits the
--   free variables of @v_i@ that are not in @s_i@.
newtype FreeInherit = FreeInherit (Map.Map Var [Var])
                      deriving(Show, Monoid)

-- | The union of two free variable sets. 
--
--   We arbitrarily retain one of the sets of excluded variables
--   (implicit in the call to 'Map.union').
--   It does not matter which set excluded.
--   There will never be an attempt to propagate variables that are in
--   only one of the two sets.
captInheritUnion (FreeInherit s1) (FreeInherit s2) =
  FreeInherit (Map.union s1 s2)

-------------------------------------------------------------------------------
-- Constraint generation
--

-- | Information needed to make a hoisting decision about a function when 
--   a call to that function is encountered.
data FunInfo =
  FunInfo { -- | The function's arity.  The arity is used to decide whether
            --   a given function call is saturated.
            arity :: {-# UNPACK #-}!Int
          }

-- | While generating constraints, a map is used to keep track of all
--   in-scope local functions.
type FunMap = Map.Map Var FunInfo

-- | Information used to solve capture constraints for a function.
--   This information is stored in a set or hashtable indexed by the function
--   name.
data UnsolvedFunction =
  UnsolvedFunction
  { -- | Functions whose free variables are inherited by this function
    funInheritedCaptures :: FreeInherit
    -- | The set of free variables of this function
  , funCapturedSet :: {-# UNPACK #-}!(IORef Free)
  }

newFunctionDescr csts free = do
  free_set <- newIORef free
  return $ UnsolvedFunction csts free_set

data ScanInputs =
  ScanInputs
  { -- | Information about arity and scope of local functions.
    scanFunMap :: FunMap

    -- | Return continuations
  , scanRConts :: !LocalCPS.RConts

    -- | The set of all continuation functions.  Continuaions are only included
    --   in the set if they are actually the continuation of some function.
  , scanContinuations :: !(Set.Set Var)
    
    -- | The function being scanned
  , scanCurrentFun :: Var

    -- | The set of global variables.  Globals are excluded from the analysis 
    --   because they are never captured.
  , scanGlobals :: !(Set.Set Var)
    -- | The variables that are defined in the current function and are
    --   in scope at the current program point.  Variables defined in an
    --   enclosing function are not in this list.
    --
    --   A function never captures variables that are defined in its
    --   own body.  We must remove those variables when computing the 
    --   captured variable set.  To do this, the set of local variables
    --   is saved in each capture constraint.
  , scanLocals :: [Var]
  }

-- | Add a definition group to the scope where a function is being used.
--
--   This clears the set of local variables, because the scan is about to
--   enter the body of a new function.
pushContext :: ScanInputs -> ScanInputs
pushContext si =
  si {scanLocals = []}

-- | Add a group's local functions to the environment.
extendContext :: [LFunDef] -> ScanInputs -> ScanInputs
extendContext defs si =
  si {scanFunMap = insert_defs $ scanFunMap si,
      scanLocals = map definiendum defs ++ scanLocals si}
  where
    insert_defs :: FunMap -> FunMap
    insert_defs m = foldr insert_def m defs

    insert_def (Def v f) m =
      let info = FunInfo (length $ funParams f)
      in Map.insert v info m

-------------------------------------------------------------------------------

-- | A scan for computing free variables.
newtype Scan a = Scan {runScan :: ScanInputs -> IO (ScanResult a)}

data ScanResult a = ScanResult a !GlobalConstraints

-- | Global constraints are collected by scanning and processed after scanning
--   is complete.
newtype GlobalConstraints =
  GlobalConstraints
  { unsolvedFunctions :: Map.Map Var UnsolvedFunction
  }

instance Monoid GlobalConstraints where
  mempty = GlobalConstraints mempty
  GlobalConstraints a `mappend` GlobalConstraints b =
    GlobalConstraints (a `mappend` b)

-- | Scanning an expression produces a set of free variables and inherited
--   variable constraints.
type ScanExp = Scan (Free, FreeInherit)

instance Monoid ScanExp where
  mempty = Scan (\_ -> return (ScanResult mempty mempty))

  Scan f1 `mappend` Scan f2 = Scan $ \i -> do
    ScanResult c1 csts1 <- f1 i
    ScanResult c2 csts2 <- f2 i
    return $ ScanResult (c1 `mappend` c2) (csts1 `mappend` csts2)

  mconcat xs = Scan $ \i -> do
    (frees, globals) <-
      let run_scan a (Scan f) = do
            ScanResult c g <- f i
            return (a `mappend` (c, g))
      in foldM run_scan mempty xs
    return $ ScanResult frees globals

instance Monad Scan where
  return x = Scan (\_ -> return (ScanResult x mempty))
  m >>= k = Scan (\i -> do ScanResult x c1 <- runScan m i
                           ScanResult y c2 <- runScan (k x) i
                           return $ ScanResult y (c1 `mappend` c2))

instance MonadIO Scan where
  liftIO m = Scan $ \_ -> do x <- m
                             return $ ScanResult x mempty

putFun :: Var -> UnsolvedFunction -> Scan ()
putFun v f = Scan $ \_ ->
  return (ScanResult () (GlobalConstraints (Map.singleton v f)))

getRConts :: Scan LocalCPS.RConts
getRConts = Scan $ \i -> return $ ScanResult (scanRConts i) mempty

getCurrentFunction :: Scan Var
getCurrentFunction = Scan $ \i ->
  return $ ScanResult (scanCurrentFun i) mempty

-- | Check whether variable 'v' is a continuation label
isContinuation :: Var -> Scan Bool
isContinuation v = Scan $ \i ->
  return $ ScanResult (v `Set.member` scanContinuations i) mempty

-- | Enter a member of a definition group.
--
--   This function updates the context when scanning traverses into a 
--   @letfun@-bound function body.  At any time during scanning, the
--   context for a function @f@ is the nesting of function definitions
--   between the definition of @f@ and the use of @f@.  If @f@ is in a
--   recursive group,
--   the context includes the definition of @f@.
enterGroup :: ScanExp -> ScanExp
enterGroup (Scan f) =
  Scan $ \i -> do
    -- Scan the local functions
    ScanResult (fv, inherited) global_constraints <- f (pushContext i)

    -- If a variable is defined in this function, we can't inherit it as
    -- a free variable from a subfunction.
    let inherited' =
          case inherited
          of FreeInherit m -> FreeInherit $ Map.map (scanLocals i ++) m
    return $ ScanResult (fv, inherited') global_constraints

-- | Enter a context in which variables defined by a definition group are 
--   in scope.
--
--   Add the definition group to the environment, and remove the defined
--   variables from the inherited free-variable set.
defineGroup :: [LFunDef] -> ScanExp -> ScanExp
defineGroup fdefs (Scan f) =
  define_group $
  defines definienda $
  Scan $ \i -> f (extendContext fdefs i)
  where
    definienda = map definiendum fdefs
    
    -- Captured variables are not inherited by 
    define_group (Scan f) = Scan $ \i -> do
      ScanResult (captured, FreeInherit inherits) global_csts <- f i
      let inherits' = foldr Map.delete inherits definienda
      return $ ScanResult (captured, FreeInherit inherits') global_csts

-- | Scan a reference to a variable, other than a tail call.
--
--   If it's not a global variable, the variable will be added to the
--   captured variable set.  If it's a local function, the function
--   will be hoisted.
capture :: Var -> ScanExp
capture v = Scan $ \env ->
  let captured =
        if v `Set.member` scanGlobals env
        then mempty
        else (Set.singleton v, mempty)
      result = ScanResult captured mempty
  in captured `seq` return result

define :: Var -> ScanExp -> ScanExp
define v (Scan s) = Scan $ \i -> do
  ScanResult (capt, inherit) csts <- s (i {scanLocals = v : scanLocals i})
  return $ ScanResult (Set.delete v capt, inherit) csts

defines :: [Var] -> ScanExp -> ScanExp
defines vs (Scan s) = Scan $ \i -> do
  ScanResult (capt, inherit) csts <- s (i {scanLocals = vs ++ scanLocals i})
  return $ ScanResult (foldr Set.delete capt vs, inherit) csts

-- | Scan a call of a variable.
--
--   The variable is captured.
--
--   If the callee is not fully applied, or if it's not a tail call, 
--   it must be hoisted.
--
--   Otherwise, if a function enclosing this call is hoisted, the callee
--   must also be hoisted.
called :: Var -> ScanExp
called v = capture v `mappend` called' v

called' v = Scan $ \env ->
  let locals = scanLocals env
      m_finfo = Map.lookup v $ scanFunMap env
      c_cst =
        case m_finfo
        of Just _ -> FreeInherit (Map.singleton v locals)
           _ -> mempty
      global_constraints = GlobalConstraints mempty
      result = ScanResult (mempty, c_cst) global_constraints
  in c_cst `seq` return result

-------------------------------------------------------------------------------
-- Scanning for constraint generation

scanValue :: Val -> ScanExp
scanValue value =
  case value
  of VarV v    -> capture v
     LitV _    -> mempty
     RecV _ xs -> scanValues xs

scanValues vals = mconcat (map scanValue vals)

scanAtom :: Atom -> ScanExp
scanAtom atom =
  case atom
  of ValA vs         -> scanValues vs
     CallA _ op args -> scan_call op args
     PrimA _ args    -> scanValues args
     UnpackA r arg   -> scanValue arg
     _               -> internalError "scanAtom"
  where
    scan_call op args =
      let op_scan =
            case op
            of VarV v -> called v
               _      -> scanValue op 
      in op_scan `mappend` scanValues args

scanStm :: LStm -> ScanExp
scanStm statement =
  case statement
  of LetLCPS params rhs label body -> do
       is_cont <- isContinuation label
       scanAtom rhs `mappend`
         if is_cont
         then
           -- The body is in a separate function
           scanContinuationFunction params label body
         else
           defines params (scanStm body)
     LetrecLCPS defs _ stm ->
       scanGroup defs $ scanStm stm
     SwitchLCPS cond alts ->
       scanValue cond `mappend` mconcat [scanStm s | (_, s) <- alts] 
     ReturnLCPS atom ->
       scanAtom atom 
     ThrowLCPS val ->
       scanValue val

scanFun :: LFun -> ScanExp
scanFun f = defines (funParams f) $ scanStm (funBody f)

scanDef :: LFunDef -> ScanExp
scanDef d = Scan $ \i ->
  runScan (scanFun (definiens d)) (i {scanCurrentFun = definiendum d})

-- | Using the results of scanning a function body, produce constraints
--   to be solved later.
generateConstraint :: Var -> Free -> FreeInherit -> Scan ()
generateConstraint fun_name free inherits = do      
  -- This function always inherits free variables from its continuation
  -- as if there were a direct call to the continuation.
  rconts <- getRConts
  let (free_k, inherits_k) =
        case LocalCPS.lookupCont fun_name rconts
        of Just (LocalCPS.RCont k _) ->
             (Set.insert k free,
              inherits `captInheritUnion` FreeInherit (Map.singleton k []))
           _ -> (free, inherits)

  -- Create an UnsolvedFunction
  putFun fun_name =<< liftIO (newFunctionDescr inherits_k free_k)
 
-- | Scan the functions in a definition group and create placeholders for
--   constraint solving.
scanGroupFunctions :: Group LFunDef -> ScanExp
scanGroupFunctions g =
  case g
  of Rec group_members -> defineGroup group_members $
                          mconcat $ map scan_def group_members
     NonRec fdef -> scan_def fdef
  where
    scan_def :: LFunDef -> ScanExp
    scan_def fdef = do
      (free, inherits) <- scanDef fdef
      generateConstraint (definiendum fdef) free inherits
      return (free, inherits)

scanContinuationFunction :: [Var] -> Var -> LStm -> ScanExp
scanContinuationFunction params fun_name body = enterGroup $ do
  (free, inherits) <- defines params $ scanStm body
  generateConstraint fun_name free inherits
  return (free, inherits)

-- | Scan a function definition group. 
--   The scan creates an 'UnsolvedFunction' for each function in the group.  
--   Free variable constraints for local functions are propagated.
scanGroup :: Group LFunDef -> ScanExp -> ScanExp
scanGroup group scan_body =
  -- Create a descriptor for this group; add it to the descriptors taken from 
  -- the function bodies.  Do not propagate constraints.
  enterGroup (scanGroupFunctions group) `mappend`

  -- Process the body
  defineGroup (groupMembers group) scan_body

-- | Scan a top-level function, generating a set of constraints
scanTopLevelDef :: LocalCPS.RConts -- ^ Return continuations
                -> Set.Set Var     -- ^ Global variables that are in scope
                -> Set.Set Var     -- ^ Continuation funtions in the @LFunDef@
                -> LFunDef
                -> IO (Map.Map Var UnsolvedFunction)
scanTopLevelDef rconts globals conts (Def v f) = do
  let initial_context =
        ScanInputs Map.empty rconts conts undefined globals []
  ScanResult (free, inherits) (GlobalConstraints ufuncs) <-
    runScan (scanDef (Def v f)) initial_context

  unless (Set.null free) $
    traceShow free $
    internalError "scanTopLevelDef: Top-level function has free variables"

  unless (Map.null (case inherits of FreeInherit m -> m)) $
    internalError "scanTopLevelDef: Invalid free variable constraints"

  return ufuncs

-------------------------------------------------------------------------------
-- Free constraint solving

data FCSEntry =
  FCSEntry
  { -- | The free variables assigned to this function
    ccsFree :: {-#UNPACK#-}!(IORef Free)
    -- | Propagation of free variables.  For each @(f, s)@,
    --   we have @free f `isSupersetOf` (free this \\ s)@.
  , ccsPropagate :: [(Var, [Var])]
  }

-- | A hash table of functions being solved
type FTable = HashTable.HashTable Var FCSEntry

makeFTable :: [(Var, UnsolvedFunction)] -> IO FTable
makeFTable xs = do
  htab <- HashTable.newHint compare_var hash_var (length xs)
  
  -- Create an entry for each function
  mapM_ (create_entry htab) xs

  -- Take free variable propagation info from each UnsolvedFunction and 
  -- distribute it to the function that's the source of each constraint
  forM_ xs $ \(target, f) ->
    forM_ (case funInheritedCaptures f
           of FreeInherit m -> Map.toList m) $ \(source, mask) ->
      add_propagation htab source target mask

  return htab
  where
    compare_var = (==)
    hash_var v = HashTable.hashInt $ fromIdent $ varID v
    
    create_entry htab (v, f) =
      let entry = FCSEntry (funCapturedSet f) []
      in HashTable.insert htab v entry
    
    add_propagation htab src tgt mask = do
      Just entry <- HashTable.lookup htab src
      let entry' = entry {ccsPropagate = (tgt, mask) : ccsPropagate entry}
      HashTable.update htab src entry'

-- | Solve a set of variable capture constraints by computing a set of
--   free variables that satisfies all constraints.  The results of
--   the computation will be in the 'funCapturedSet'
--   fields of various objects.
solveCaptureConstraints :: [(Var, UnsolvedFunction)]
                        -> IO (Map.Map Var Free)
solveCaptureConstraints funs = do
  -- Set up data structures
  htab <- makeFTable funs
  worklist <- newWorklist (map fst funs)
  
  -- Solve
  forWorklist worklist $ propagateFunctionFreeConstraints worklist htab
  
  -- Read final value of free variable sets
  final_free_variables <-
    forM funs $ \(v, uf) -> do
      free <- readIORef $ funCapturedSet uf
      return (v, free)
  return $ Map.fromList final_free_variables

-- | Given a function whose free variables have been updated,
--   update the free variables of functions that inherit from this one.
propagateFunctionFreeConstraints :: Worklist Var -> FTable -> Var -> IO ()
propagateFunctionFreeConstraints worklist htab fun_name = do
  Just fun <- HashTable.lookup htab fun_name
  free_vars <- readIORef $ ccsFree fun
  
  -- Update any functions that inherit from this one
  forM_ (ccsPropagate fun) $ \(target, mask) ->
    let propagated_vars = foldr Set.delete free_vars mask
    in updateFunctionFreeConstraints worklist htab target propagated_vars

updateFunctionFreeConstraints :: Worklist Var -> FTable -> Var -> Free -> IO ()
updateFunctionFreeConstraints worklist htab fun_name extra_vars = do
  Just fun <- HashTable.lookup htab fun_name
  change <- modifyCheckIORef (Set.union extra_vars) (ccsFree fun)
  when change $ putWorklist worklist fun_name

-------------------------------------------------------------------------------
-- Reading results of constraint solving

printUnsolvedFunction :: (Var, UnsolvedFunction) -> IO ()
printUnsolvedFunction (v, ufun) = do
  free_set <- readIORef $ funCapturedSet ufun
  
  print $ hang (pprVar v) 4 $
    text "free" <+> free_doc (Set.elems free_set) $$
    text "inherits" <+> inherit_doc (funInheritedCaptures ufun)
  where
    inherit_doc (FreeInherit m) =
      vcat [pprVar v <+> text "-" <+> braces (fsep (map pprVar vs))
           | (v, vs) <- Map.toList m]

    free_doc s = fsep $ punctuate (text ",") $ map pprVar s

-------------------------------------------------------------------------------

-- | Find the set of non-global variables that is used by each local function,
--   including continuation funtions.
findCapturedVariables :: LocalCPS.RConts -- ^ Return continuations
                      -> Set.Set Var     -- ^ Global variables in scope here
                      -> Set.Set Var     -- ^ Continuations
                      -> LFunDef         -- ^ A global function definition
                      -> IO (Map.Map Var Free)
                      -- ^ Computes the free variables of each local function
                      --   and continuation
findCapturedVariables return_continuations global_vars conts ann_def = do
  -- Create constraints
  ufuns <- scanTopLevelDef return_continuations global_vars conts ann_def

  -- Debugging
  when debug $ do
    let Def global_name _ = ann_def
    putStrLn $ "Hoisting in " ++ show global_name
    mapM_ printUnsolvedFunction $ Map.toList ufuns

  -- Solve constraints
  solveCaptureConstraints $ Map.toList ufuns