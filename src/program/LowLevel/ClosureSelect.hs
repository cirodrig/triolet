{-| Selection of functions for closure conversion.

Based on which functions are 
-}

{-# Language FlexibleInstances, GeneralizedNewtypeDeriving #-}
module LowLevel.ClosureSelect(Capt, findFunctionsToHoist) where

import Control.Monad
import Control.Monad.Identity
import Control.Monad.Trans
import Data.Array.IO
import Data.Function
import qualified Data.Graph.Inductive as Graph
import qualified Data.Graph.Inductive.Query.DFS as Graph
import qualified Data.HashTable as HashTable
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
import LowLevel.FreshVar
import LowLevel.Print
import LowLevel.Syntax
import LowLevel.Types
import LowLevel.Build
import LowLevel.ClosureCode
import Globals

-------------------------------------------------------------------------------
-- Constraints

-- | A hoisting decision.  @True@ means hoist, @False@ means don't hoist.
type Hoist = Bool

-- | An implication constraint used to identify definition groups that
--   should be hoisted.  @HoistCst g gs@ means that if any of @gs@ are
--   hoisted, then @g@ should be hoisted.
data HoistCst = HoistCst !GroupID [GroupID] deriving(Show)

type HoistCsts = [HoistCst]

-- | A variable capture set
type Capt = Set.Set Var

-- | An inherited capture set.  @CaptInherit fs@ means that the current
--   function inherits the captured variables of each function in @fs@.
--   A function can only inherit captured variables from functions defined
--   in lexically enclosing @letrec@ statements.
newtype CaptInherit = CaptInherit (Set.Set Var)
                      deriving(Show, Monoid)

captInheritUnion (CaptInherit s1) (CaptInherit s2) =
  CaptInherit (Set.union s1 s2)

-------------------------------------------------------------------------------
-- Constraint generation
--

-- | Information needed to make a hoisting decision about a function when 
--   a call to that function is encountered.
data FunInfo =
  FunInfo { -- | The function's arity.  The arity is used to decide whether
            --   a given function call is saturated.
            arity :: {-# UNPACK #-}!Int
            -- | The group where the function is defined
          , defGroup :: !GroupID
            -- | Context in which a function is used.  The context consists
            --   of all function definitions that enclose the use but not
            --   the definition.  A function is not part
            --   of its own context.  If any of them are marked for
            --   hoisting, then the function must be hoisted.
            --
            --   A definition group is /not/ part of the context of its body.
          , useContext :: [GroupID]
          }

-- | While generating constraints, a map is used to keep track of all
--   in-scope local functions.
type FunMap = Map.Map Var FunInfo

-- | A description of a local definition group or single top-level function.
--   The description is used to decide whether to hoist.
data UnsolvedGroup =
  UnsolvedGroup
  { groupID :: {-# UNPACK #-}!GroupID
    -- | Function definitions in this group
  , groupDefs :: !(Group UnsolvedFunction)
    -- | The hoisting decision for this group
  , groupHoistedVal :: !(IORef Hoist)
  }

type GroupID = Ident UnsolvedGroup

instance Eq UnsolvedGroup where
  (==) = (==) `on` groupID
  (/=) = (/=) `on` groupID

instance Ord UnsolvedGroup where
  compare = compare `on` groupID

data UnsolvedFunction =
  UnsolvedFunction
  { funDef :: FunDef
    -- | Functions whose captured variables are inherited by this function
  , funInheritedCaptures :: CaptInherit
    -- | The set of variables captured by this function
  , funCapturedSet :: !(IORef Capt)
  }

funID :: UnsolvedFunction -> Var
funID f = definiendum $ funDef f

instance Eq UnsolvedFunction where
  (==) = (==) `on` funID
  (/=) = (/=) `on` funID

instance Ord UnsolvedFunction where
  compare = compare `on` funID

newGroupDescr :: GroupID -> Group UnsolvedFunction -> IO UnsolvedGroup
newGroupDescr gid defs = do
  -- Initially assume the group is not hoisted
  hoisted_val <- newIORef False
  return $ UnsolvedGroup { groupID = gid
                         , groupDefs = defs
                         , groupHoistedVal = hoisted_val}

newFunctionDescr fdef csts captured = do
  captured_set <- newIORef captured
  return $ UnsolvedFunction fdef csts captured_set


data ScanInputs =
  ScanInputs
  { -- | Information about arity and scope of local functions.
    scanFunMap :: FunMap
    -- | The set of global variables.  Globals are never captured.
  , scanGlobals :: !(Set.Set Var)
  , scanIdSupply :: {-# UNPACK #-}!(IdentSupply UnsolvedGroup)
  }

-- | Add a definition group to the scope where a function is being used.
--
--   This puts a new group in between preexisting definitions and their uses.
pushContext :: GroupID -> ScanInputs -> ScanInputs
pushContext context_fun si =
  si {scanFunMap = Map.map add_to_context (scanFunMap si)}
  where
    add_to_context finfo =
      finfo {useContext = (context_fun:useContext finfo)}

-- | Add a group's local functions to the environment.
extendContext :: GroupID -> [FunDef] -> ScanInputs -> ScanInputs
extendContext gid defs si =
  si {scanFunMap = insert_defs $ scanFunMap si}
  where
    insert_defs :: FunMap -> FunMap
    insert_defs m = foldr insert_def m defs

    insert_def (Def v f) m =
      let info = FunInfo (length $ funParams f) gid []
      in Map.insert v info m

-------------------------------------------------------------------------------

-- | A scan for computing hoisting and capture information.
newtype Scan a = Scan {runScan :: ScanInputs -> IO (ScanResult a)}

data ScanResult a = ScanResult a !GlobalConstraints

-- | Global constraints are collected by scanning and processed after scanning
--   is complete.
data GlobalConstraints =
  GlobalConstraints
  { hoistedGroups :: Set.Set GroupID
  , unsolvedGroups :: [UnsolvedGroup]
  }

instance Monoid GlobalConstraints where
  mempty = GlobalConstraints mempty mempty
  GlobalConstraints a b `mappend` GlobalConstraints c d =
    GlobalConstraints (a `mappend` c) (b `mappend` d)

-- | Scanning an expression produces a set of variable capture constraints,
--   captured variables, and hoisting constraints.
type ScanExp = Scan (CaptInherit, Capt, HoistCsts)

instance Supplies Scan (Ident UnsolvedGroup) where
  fresh = Scan $ \inputs -> do
    x <- supplyValue $ scanIdSupply inputs
    return $ ScanResult x mempty

instance Monoid a => Monoid (Scan a) where
  mempty = Scan (\_ -> return (ScanResult mempty mempty))

  Scan f1 `mappend` Scan f2 = Scan $ \i -> do
    ScanResult x csts1 <- f1 i
    ScanResult y csts2 <- f2 i
    return $ ScanResult (x `mappend` y) (csts1 `mappend` csts2)

  mconcat xs = Scan $ \i -> do
    ys <- sequence [f i | Scan f <- xs]
    return $ foldr append (ScanResult mempty mempty) ys
    where
      append (ScanResult y d) (ScanResult x c) =
        ScanResult (x `mappend` y) (c `mappend` d)

instance Monad Scan where
  return x = Scan (\_ -> return (ScanResult x mempty))
  m >>= k = Scan (\i -> do ScanResult x c1 <- runScan m i
                           ScanResult y c2 <- runScan (k x) i
                           return $ ScanResult y (c1 `mappend` c2))

instance MonadIO Scan where
  liftIO m = Scan $ \_ -> do x <- m
                             return $ ScanResult x mempty

putGroup :: UnsolvedGroup -> Scan ()
putGroup g = Scan (\_ -> return (ScanResult () (GlobalConstraints mempty [g])))

-- | Enter a member of a definition group.
--
--   This function updates the context when scanning traverses into a 
--   @letfun@-bound function body.  At any time during scanning, the
--   context for a function @f@ is the nesting of function definitions
--   between the definition of @f@ and the use of @f@.  If @f@ is in a
--   recursive group,
--   the context includes the definition of @f@.
enterGroup :: GroupID -> Scan a -> Scan a
enterGroup gid (Scan f) =
  Scan $ \i -> f (pushContext gid i)

-- | Enter a context in which variables defined by a definition group are 
--   in scope.
--
--   Add the definition group to the environment, and remove the defined
--   variables from the captured variable set.
--
--   If 'in_context' is True, then we're processing the function definitions
--   and should add them to the context.  Otherwise we're processing the
--   body of the definition group and we should not add them to the context.
defineGroup :: GroupID -> [FunDef] -> ScanExp -> ScanExp
defineGroup gid fdefs (Scan f) =
  define_group $
  defines definienda $
  Scan $ \i -> f (extendContext gid fdefs i)
  where
    definienda = map definiendum fdefs

    define_group (Scan f) = Scan $ \env -> do
      ScanResult (c_csts, c, h_csts) global_csts <- f env
      let c_csts' =
            case c_csts
            of CaptInherit s -> CaptInherit (foldr Set.delete s definienda)
      return $ ScanResult (c_csts', c, h_csts) global_csts

-- | Scan a reference to a variable, other than a tail call.
--
--   If it's a local variable, the variable will be added to the
--   captured variable set.  If it's a local function, the function
--   will be hoisted.
capture :: Var -> ScanExp
capture v = Scan $ \env ->
  let (captured, hoisted) =
        if v `Set.member` scanGlobals env
        then (mempty, mempty) 
        else case Map.lookup v $ scanFunMap env
             of Nothing -> (Set.singleton v, mempty)
                Just finfo -> (Set.singleton v, Set.singleton (defGroup finfo))
      global_constraints = GlobalConstraints hoisted mempty
      result = ScanResult (mempty, captured, mempty) global_constraints
  in captured `seq` hoisted `seq` return result

define :: Var -> ScanExp -> ScanExp
define v (Scan s) = Scan $ \i -> do
  ScanResult (c_csts, c, h_csts) global_constraints <- s i
  return $ ScanResult (c_csts, Set.delete v c, h_csts) global_constraints

defines :: [Var] -> ScanExp -> ScanExp
defines vs (Scan s) = Scan $ \i -> do
  ScanResult (c_csts, c, h_csts) global_constraints <- s i
  return $ ScanResult (c_csts, foldr Set.delete c vs, h_csts) global_constraints

-- | Scan a call of a variable.
--
--   The variable is captured.
--
--   If the callee is not fully applied, or if it's not a tail call, 
--   it must be hoisted.
--
--   Otherwise, if a function enclosing this call is hoisted, the callee
--   must also be hoisted.
called :: Bool -> Var -> Int -> ScanExp
called is_tail v num_args = Scan $ \env ->
  if v `Set.member` scanGlobals env
  then return $ ScanResult mempty mempty
  else let m_finfo = Map.lookup v $ scanFunMap env
           captured = Set.singleton v
           c_cst =
             case m_finfo
             of Just finfo -> CaptInherit (Set.singleton v)
                _ -> mempty
           (h_cst, hoisted) =
             case m_finfo
             of Just finfo
                  | is_tail && num_args >= arity finfo ->
                      -- Saturated tail call.  Hoist the callee if this
                      -- call is part of a hoisted function that doesn't
                      -- contain the definition of the callee.
                      ([HoistCst (defGroup finfo) (useContext finfo)], mempty)
                  | otherwise ->
                      -- Undersaturated or non-tail-call; must hoist
                      (mempty, Set.singleton (defGroup finfo))
                _ -> mempty     -- Unknown function
           global_constraints = GlobalConstraints hoisted mempty
           result = ScanResult (c_cst, captured, h_cst) global_constraints
       in h_cst `seq` hoisted `seq` c_cst `seq` return result

-------------------------------------------------------------------------------
-- Scanning for constraint generation

scanValue :: Val -> ScanExp
scanValue value =
  case value
  of VarV v    -> capture v
     LitV _    -> mempty
     RecV _ xs -> scanValues xs
     LamV _    -> internalError "scanValue"

scanValues vals = mconcat (map scanValue vals)

scanAtom :: Bool -> Atom -> ScanExp
scanAtom is_tail atom =
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
            of VarV v -> called is_tail v (length args)
               _      -> scanValue op 
      in op_scan `mappend` scanValues args

scanStm :: Stm -> ScanExp
scanStm statement =
  case statement
  of LetE params rhs body ->
       scanAtom False rhs `mappend` defines params (scanStm body)
     LetrecE defs stm ->
       scanGroup defs $ scanStm stm
     SwitchE cond alts ->
       scanValue cond `mappend` mconcat [scanStm s | (_, s) <- alts] 
     ReturnE atom ->
       scanAtom True atom
     ThrowE val ->
       scanValue val

scanFun :: Fun -> ScanExp
scanFun f = defines (funParams f) $ scanStm (funBody f)

-- | Scan the functions in a definition group and create placeholders for
--   constraint solving.
scanGroupFunctions :: GroupID -> Group FunDef
                   -> Scan (Group UnsolvedFunction, (CaptInherit, Capt, HoistCsts))
scanGroupFunctions group_id g =
  case g
  of Rec group_members -> do
       let setup_context = defineGroup group_id group_members
       (fs, constraints) <- mapAndUnzipM (scan_def setup_context) group_members
       return (Rec fs, mconcat constraints)
     NonRec fdef -> do
       (f, constraints) <- scan_def id fdef
       return (NonRec f, constraints)
  where
    scan_def :: (ScanExp -> ScanExp) -> FunDef
             -> Scan (UnsolvedFunction, (CaptInherit, Capt, HoistCsts))
    scan_def setup_context fdef = do
      constraints@(local_c_csts, local_captured, _) <-
        setup_context $ scanFun (definiens fdef)

      -- Create an UnsolvedFunction
      unsolved_function <-
        liftIO $ newFunctionDescr fdef local_c_csts local_captured
      return (unsolved_function, constraints)

-- | Scan a function definition group. 
--   The scan creates an 'UnsolvedGroup'.  Also, captured variable constraints
--   are propagated in the scan.  The set of hoisted groups is propagated.
--   Hoisting constraints in the body are propagated.
scanGroup :: Group FunDef -> ScanExp -> ScanExp
scanGroup group scan_body = do
  -- Create a descriptor for this group; add it to the descriptors taken from 
  -- the function bodies.  Do not propagate constraints.
  group_id <- fresh
  (local_defs, local_constraints) <-
    enterGroup group_id $ scanGroupFunctions group_id group

  -- Create a descriptor for this group
  putGroup =<< liftIO (newGroupDescr group_id local_defs)

  -- Process the body
  body_constraints <- defineGroup group_id (groupMembers group) scan_body

  -- Propagate capture constraints from the defgroup,
  -- but not hoisting constraints
  return (local_constraints `mappend` body_constraints)

-- | Scan a top-level function, generating a set of constraints that determine
--   hoisting and variable capture
scanTopLevelDef :: Set.Set Var
                -> FunDef
                -> IO (HoistCsts, Set.Set GroupID, [UnsolvedGroup], GroupID)
scanTopLevelDef globals (Def v f) = do
  id_supply <- newIdentSupply
  let initial_context = ScanInputs Map.empty globals id_supply
  ScanResult (c_csts, captured, h_csts) (GlobalConstraints hoisted groups) <-
    runScan (scanFun f) initial_context
  id_bound <- supplyValue id_supply

  unless (Set.null $ case c_csts of CaptInherit s -> s) $
    internalError "scanTopLevelDef: Top-level function captures variables"
  
  unless (Set.null captured) $
    internalError "scanTopLevelDef: Top-level function captures variables"

  return (h_csts, hoisted, groups, id_bound)

-------------------------------------------------------------------------------
-- Shared constraint solving code
--
-- This code is used for solving both capture constraints and
-- hoisting constraints.

type Worklist a = IORef (Set.Set a)

newWorklist :: Ord a => [a] -> IO (Worklist a)
newWorklist contents = newIORef (Set.fromList contents)

putWorklist :: Ord a => Worklist a -> a -> IO ()
putWorklist wl x = modifyIORef wl $ Set.insert x

readWorklist :: Ord a => Worklist a -> IO (Maybe a)
readWorklist wl = do
  s <- readIORef wl
  case Set.minView s of
    Just (x, s') -> do
      writeIORef wl s'
      return (Just x)
    Nothing -> return Nothing

isEmptyWorklist :: Ord a => Worklist a -> IO Bool
isEmptyWorklist wl = do
  s <- readIORef wl
  return $ Set.null s

forWorklist :: Ord a => Worklist a -> (a -> IO ()) -> IO ()
forWorklist wl f = readWorklist wl >>= continue
  where
    continue Nothing  = return ()
    continue (Just x) = f x >> forWorklist wl f

-- | Modify the contents of an @IORef@, and test whether the value has
--   actually changed.
modifyCheckIORef :: Eq a => (a -> a) -> IORef a -> IO Bool
modifyCheckIORef f ref = do
  x <- readIORef ref
  let y = f x
  let change = x /= y
  when change $ writeIORef ref y
  return change

-------------------------------------------------------------------------------
-- Hoisting constraint solving

-- | An array where index @n@ has the group with ID @n@ in  
type GroupArray = IOArray GroupID UnsolvedGroup

-- | Create a lookup table from ID to group.  The lookup table is used to
--   solve constraints.
mkGroupArray :: [UnsolvedGroup] -> GroupID -> IO GroupArray
mkGroupArray groups id_bound = do
  ga <- newArray (toIdent 0, id_bound) undefined_group
  forM_ groups $ \g -> writeArray ga (groupID g) g
  return ga
  where
    undefined_group = internalError "mkGroupArray: Not a valid group"

forGroups_ :: GroupArray -> [GroupID] -> (UnsolvedGroup -> IO a) -> IO ()
forGroups_ table gids f = mapM_ (f <=< readArray table) gids

-- | Determine which groups are hoisted.  The 'groupHoistedVal' field is
--   set to @True@ on hoisted groups.
setupAndSolveHoistingConstraints :: HoistCsts
                                 -> Set.Set GroupID
                                 -> GroupArray
                                 -> IO ()
setupAndSolveHoistingConstraints h_csts initial_set table = do
  -- Every group in initial_set is hoisted
  initialize_hoisted_groups
  
  -- Create an array of hoisting implications.
  -- if @g2 `elem` h_cst_array !! g@, and @g@ is hoisted, then @g2@ is hoisted.
  table_bounds <- getBounds table
  h_cst_array <- newArray table_bounds []
  initialize_hoist_array h_cst_array
  
  solveHoistingConstraints table h_cst_array initial_set
  where
    -- Groups in the set are hoisted
    initialize_hoisted_groups =
      forGroups_ table (Set.toList initial_set) $ \grp ->
      writeIORef (groupHoistedVal grp) True

    initialize_hoist_array ay =
      -- For each constraint (consequent <== antecedents),
      forM_ h_csts $ \(HoistCst consequent antecedents) ->
      -- for each antecedent,
      forM_ antecedents $ \antecedent ->
      -- add consequent to the antecedent's table entry
      writeArray ay antecedent . (consequent :) =<< readArray ay antecedent

-- | The solving phase for hoisting constraints
solveHoistingConstraints :: GroupArray
                         -> IOArray GroupID [GroupID]
                         -> Set.Set GroupID
                         -> IO ()
solveHoistingConstraints table h_csts initial_set = do
  -- Process groups until no changes are made
  workset <- newWorklist (Set.toList initial_set)

  forWorklist workset $ \elt -> do
    -- Find all groups that must be hoisted, given that 'elt' is hoisted
    need_marking <- readArray h_csts elt
    forM_ need_marking $ \gid -> do
      -- Look up and mark this group
      group <- readArray table gid
      change <- modifyCheckIORef (const True) (groupHoistedVal group)
      when change $ putWorklist workset gid

-------------------------------------------------------------------------------
-- Capture constraint solving

type FHashTable a = HashTable.HashTable Var a

fHashTable :: [(Var, a)] -> IO (FHashTable a)
fHashTable xs = do
  htab <- HashTable.new compare_var hash_var
  forM_ xs $ \(k, v) -> HashTable.insert htab k v
  return htab
  where
    compare_var = (==)
    hash_var v = HashTable.hashInt $ fromIdent $ varID v

-- | Constant data used during capture constraint solving
data CCSConstants =
  CCSConstants 
  { -- | Worklist of functions
    functionWorklist :: {-#UNPACK#-} !(Worklist UnsolvedFunction)
    -- | Lookup table from function name to UnsolvedFunction
  , functionTable :: !(FHashTable UnsolvedFunction)
    -- | For each function, this table records the functions
    --   that inherit from it.  An absent entry means the same as the empty set.
  , funInheritorTable :: !(FHashTable (Set.Set Var))
  }

initializeCCSConstants :: [UnsolvedGroup] -> GroupID -> IO CCSConstants
initializeCCSConstants groups id_bound = do
  function_table <- fHashTable [(funID f, f) | f <- unsolved_functions]
  
  -- Create a table with one entry for each capture-inherit constraint
  fun_inheritor_table <- fHashTable []
  forM_ unsolved_functions $ \inheritor ->
    case funInheritedCaptures inheritor
    of CaptInherit funs -> forM_ (Set.toList funs) $ \endower -> do
         -- Insert a mapping (endower |-> inheritor)
         m_old_value <- HashTable.lookup fun_inheritor_table endower
         let old_value = fromMaybe Set.empty m_old_value
         HashTable.update fun_inheritor_table endower
           (Set.insert (funID inheritor) old_value)

  -- Initially, all functions are put onto the worklist
  function_worklist <- newWorklist unsolved_functions
  return $ CCSConstants function_worklist function_table fun_inheritor_table
  where
    unsolved_functions = concatMap (groupMembers . groupDefs) groups

-- | @funInheritors f@ is the set of functions that inherit the captured
--   variables of @f@.
funInheritors :: CCSConstants -> Var -> IO [UnsolvedFunction]
funInheritors input fun_name = do
  m_inheritors <- HashTable.lookup (funInheritorTable input) fun_name
  let inheritors = maybe [] Set.toList m_inheritors
  forM inheritors $ \v -> do
    Just inheritor <- HashTable.lookup (functionTable input) v
    return inheritor

-- | Solve a set of variable capture constraints by computing a set of
--   captured variables that satisfies all constraints.  The results of
--   the computation will be in the 'funCapturedSet'
--   fields of various objects.
solveCaptureConstraints :: CCSConstants -> IO ()
solveCaptureConstraints input =
  forWorklist (functionWorklist input) (propagateFunctionCaptureConstraints input)

-- | Given a function whose captured variables have been updated,
--   update the captured variables of functions that inherit from this one.
propagateFunctionCaptureConstraints ::
  CCSConstants -> UnsolvedFunction -> IO ()
propagateFunctionCaptureConstraints input fun = do
  let fun_name = funID fun
  captured_vars <- readIORef $ funCapturedSet fun
  
  -- Update any functions that inherit from this one
  funInheritors input fun_name >>=
    mapM_ (updateFunctionCaptureConstraints input captured_vars)

updateFunctionCaptureConstraints :: CCSConstants -> Capt
                                 -> UnsolvedFunction -> IO ()
updateFunctionCaptureConstraints input captured_vars fun = do
  change <- modifyCheckIORef (Set.union captured_vars) (funCapturedSet fun)
  when change $ putWorklist (functionWorklist input) fun

-------------------------------------------------------------------------------
-- Reading results of constraint solving

finalizeGroup :: IdentSupply Var -> UnsolvedGroup -> IO SolvedGroup
finalizeGroup id_supply grp = do
  hoisted <- readIORef $ groupHoistedVal grp
  if not hoisted
    then return $ UnhoistedGroup (map funID $ groupMembers $ groupDefs grp)
    else do 
      let members = groupMembers $ groupDefs grp

      -- Get the captured variables of each function.
      -- The group's shared captured variables is the intersection of the
      -- per-function captured variables.
      captureds <- mapM (readIORef . funCapturedSet) members
      let shared_captured = foldr1 Set.intersection captureds
      runFreshVarM id_supply $ make_closure (Set.toList shared_captured)
  where
    make_closure captured =
      case groupDefs grp
      of NonRec ufun -> do
           (_, closure) <- mkNonrecClosure (funDef ufun) captured
           return $ HoistedGroup (NonRec (funID ufun, closure))
         Rec ufuns -> do
           closures <- mkRecClosures (map funDef ufuns) captured
           return $ HoistedGroup (Rec $ zip (map funID ufuns) (map snd closures))

printUnsolvedGroup :: UnsolvedGroup -> IO ()
printUnsolvedGroup grp = do
  fun_docs <- mapM prettyUnsolvedFun $ groupMembers $ groupDefs grp
  print $ text "group" <+> text (show $ groupID grp) $$
    braces (vcat fun_docs)

prettyUnsolvedFun :: UnsolvedFunction -> IO Doc
prettyUnsolvedFun f = do
  captured <- readIORef $ funCapturedSet f
  let cap_doc = fsep $ map pprVar $ Set.toList captured
      inherit_doc =
        case funInheritedCaptures f
        of CaptInherit vs -> fsep $ map pprVar $ Set.toList vs
  return $ hang (pprVar (funID f)) 4 (cap_doc $$ inherit_doc)

-- | A group whose constraints have been solved.
data SolvedGroup =
    HoistedGroup (Group (Var, Closure))
  | UnhoistedGroup [Var]

groupFunctions g =
  case g
  of HoistedGroup grp -> map fst $ groupMembers grp
     UnhoistedGroup fs -> fs

printGroup :: SolvedGroup -> IO ()
printGroup grp =
  case grp
  of UnhoistedGroup fs ->
       print $ text "unhoisted" <+> fsep (map pprVar fs)
     HoistedGroup g ->
       print $ text "hoisted" <+> fsep (map pprVar $ map fst $ groupMembers g) $$
               nest 2 (text "captures" <+>
                       fsep (map pprVar $ closureCapturedVariables $ snd $ head $ groupMembers g))

-------------------------------------------------------------------------------

-- | Find all functions that should be hoisted in a top-level
--   function definition.  For each function, determine what
--   variables it captures and whether it should be hoisted.
--
--   The captured variables and hoisting decisions will always be the same
--   for functions defined in the same definition group.
findFunctionsToHoist :: IdentSupply Var
                     -> Set.Set Var
                     -> FunDef
                     -> IO (Var -> Maybe (Maybe (Group (Var, Closure))))
findFunctionsToHoist var_ids global_vars def = do
  -- Generate constraints
  (h_csts, hoisted, groups, id_bound) <- scanTopLevelDef global_vars def

  -- Debugging
  when False $ do
    let Def global_name _ = def
    putStrLn $ "Hoisting in " ++ show global_name
    mapM_ printUnsolvedGroup groups
    putStrLn $ "Initial hoisted set: " ++ show hoisted
    print h_csts

  -- Solve constraints
  table <- mkGroupArray groups id_bound
  setupAndSolveHoistingConstraints h_csts hoisted table
  ccs_constraints <- initializeCCSConstants groups id_bound
  solveCaptureConstraints ccs_constraints
  final_groups <- mapM (finalizeGroup var_ids) groups
  
  -- Debugging
  when False $ do
    mapM_ printGroup final_groups

  -- Look up results
  let lookup_function v =
        case find (\g -> v `elem` groupFunctions g) final_groups
        of Just g -> 
             case g
             of UnhoistedGroup _ -> Just Nothing
                HoistedGroup g -> Just (Just g)
           Nothing -> Nothing

  return lookup_function