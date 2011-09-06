
{-# Language FlexibleInstances #-}
module LowLevel.Closure.Hoisting(GroupID(..), findHoistedGroups)
where

import Control.Monad
import Control.Monad.Identity
import Control.Monad.Trans
import Data.Array.IO
import Data.Function
import qualified Data.Graph.Inductive as Graph
import qualified Data.Graph.Inductive.Query.DFS as Graph
import qualified Data.HashTable as HashTable
import Data.Int
import qualified Data.IntMap as IntMap
import Data.IORef
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid
import qualified Data.Set as Set
import Debug.Trace

import Common.MonadLogic
import Common.Error
import Common.Identifier
import Common.Supply
import LowLevel.FreshVar
import LowLevel.LocalCPSAnn
import qualified LowLevel.LocalCPS as LocalCPS
import LowLevel.Syntax
import LowLevel.Types
import LowLevel.Build
import Globals

-------------------------------------------------------------------------------
-- Constraints

-- | The ID of a definition group.
--   It may stand for an ordinary definition group or a virtual group
--   containing a continuation.  Virtual groups are converted to real groups
--   later.
data GroupID = GroupID {-#UNPACK#-}!(Ident GroupLabel) | ContID !Var
             deriving(Eq, Ord, Show)

hashGroupID :: GroupID -> Int32
hashGroupID (GroupID ident) = HashTable.hashInt (fromIdent ident)
hashGroupID (ContID v) = HashTable.hashInt (fromIdent $ varID v)

-- | A hoisting decision.  @True@ means hoist, @False@ means don't hoist.
type Hoist = Bool

-- | An implication constraint used to identify definition groups that
--   should be hoisted.  @HoistCst g gs@ means that if any of @gs@ are
--   hoisted, then @g@ should be hoisted.
data HoistCst = HoistCst !GroupID [GroupID] deriving(Show)

type HoistCsts = [HoistCst]

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
    -- | The hoisting decision for this group
  , groupHoistedVal :: !(IORef Hoist)
  }

instance Eq UnsolvedGroup where
  (==) = (==) `on` groupID
  (/=) = (/=) `on` groupID

instance Ord UnsolvedGroup where
  compare = compare `on` groupID

newGroupDescr :: GroupID -> IO UnsolvedGroup
newGroupDescr gid = do
  -- Initially assume the group is not hoisted
  hoisted_val <- newIORef False
  return $ UnsolvedGroup { groupID = gid
                         , groupHoistedVal = hoisted_val}

data ScanInputs =
  ScanInputs
  { -- | Information about arity and scope of local functions
    scanFunMap :: FunMap
    
    -- | The definition group containing the current function, or @Nothing@
    --   if currently scanning the body of the top-level function.
  , scanCurrentGroup :: !(Maybe GroupID)

    -- | Continuation points assigned to each local function.
    --   Continuation points will probably be converted to functions,
    --   and this must be taken into account when identifying tail calls.
  , scanRConts :: LocalCPS.RConts

    -- | The set of all continuation points.
    --   Continuation points will probably be converted to functions,
    --   so they are analyzed for variable capture as if they were functions. 
  , scanContinuations :: Set.Set Var
  }

-- | Add a definition group to the scope where a function is being used.
--
--   This puts a new group in between preexisting definitions and their uses.
--   It also clears the set of local variables, because the scan is about to
--   enter the body of a new function.
pushContext :: GroupID -> ScanInputs -> ScanInputs
pushContext context_fun si =
  si { scanFunMap = Map.map add_to_context (scanFunMap si)
     , scanCurrentGroup = Just context_fun}
  where
    add_to_context finfo =
      finfo {useContext = (context_fun:useContext finfo)}

-- | Add a group's local functions to the environment.
extendContext :: GroupID -> [LFunDef] -> ScanInputs -> ScanInputs
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
  { hoistingConstraints :: HoistCsts
  , hoistedGroups :: Set.Set GroupID
  , unsolvedGroups :: [UnsolvedGroup]
  }

instance Monoid GlobalConstraints where
  mempty = GlobalConstraints mempty mempty mempty
  GlobalConstraints a b c `mappend` GlobalConstraints d e f =
    GlobalConstraints (a `mappend` d) (b `mappend` e) (c `mappend` f)

-- | Scanning an expression produces a set of variable capture constraints,
--   captured variables, and hoisting constraints.
type ScanExp = Scan ()

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
putGroup g = Scan $ \_ ->
  return (ScanResult () (GlobalConstraints mempty mempty [g]))

-- | Check whether variable 'v' is a continuation label
isContinuation :: Var -> Scan Bool
isContinuation v = Scan $ \i ->
  return $ ScanResult (v `Set.member` scanContinuations i) mempty

-- | Find the return continuation of the named function argument.
--   The return continuation is 'LocalCPS.Top' if unknown.
lookupCont :: Var -> Scan LocalCPS.RCont
lookupCont v = Scan $ \i ->
  let m_cont = IntMap.lookup (fromIdent $ varID v) (scanRConts i)
  in return $ ScanResult (fromMaybe LocalCPS.Top m_cont) mempty

getRConts :: Scan LocalCPS.RConts
getRConts = Scan $ \i -> return $ ScanResult (scanRConts i) mempty

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
defineGroup :: GroupID -> [LFunDef] -> ScanExp -> ScanExp
defineGroup gid fdefs (Scan f) =
  Scan $ \i -> f (extendContext gid fdefs i)

-- | Scan a reference to a variable, other than a tail call.
--
--   If it's not a global function, the function will be hoisted.
capture :: Var -> ScanExp
capture v = Scan $ \env ->
  let hoisted =
        case Map.lookup v $ scanFunMap env
        of Nothing -> mempty
           Just finfo -> Set.singleton (defGroup finfo)
      global_constraints = GlobalConstraints mempty hoisted mempty
      result = ScanResult () global_constraints
  in hoisted `seq` return result

-- | Scan a call of a variable.
--
--   If the callee is not fully applied, or if it's not a tail call, 
--   it must be hoisted.
--
--   Otherwise, if a function enclosing this call is hoisted, the callee
--   must also be hoisted.
called :: Bool -> Var -> Int -> ScanExp
called is_tail v num_args = Scan $ \env ->
  let m_finfo = Map.lookup v $ scanFunMap env
      (h_cst, hoisted) =
        case m_finfo
        of Just finfo
             | is_tail && num_args == arity finfo ->
               -- Saturated tail call.  Hoist the callee if this
               -- call is part of a hoisted function that doesn't
               -- contain the definition of the callee.
               ([HoistCst (defGroup finfo) (useContext finfo)], mempty)
             | otherwise ->
                 -- Undersaturated, oversaturated, or non-tail-call; must hoist
                 (mempty, Set.singleton (defGroup finfo))
           _ -> mempty     -- Unknown function
      global_constraints = GlobalConstraints h_cst hoisted mempty
      result = ScanResult () global_constraints
  in h_cst `seq` hoisted `seq` return result

-- | Scan an implicit continuation tail-call.  The call has not actually
--   been inserted into the code yet, but can be identified based on the
--   result of local CPS analysis.
--
--   The continuation is hoisted if the caller (the current function) is.
calledCont :: Var -> ScanExp
calledCont v = Scan $ \env ->
  let current_group =
        case scanCurrentGroup env
        of Just g -> g
           Nothing -> internalError "calledCont: Function is not hoistable"
      cont_group = ContID v
      h_cst = [HoistCst cont_group [current_group]]
      global_constraints = GlobalConstraints h_cst mempty mempty
      result = ScanResult () global_constraints
  in return result

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

-- | Scan a statement.  When scanning, pretend the statement calls the
--   given return continuation at the end.
scanStm :: LocalCPS.RCont -> LStm -> ScanExp
scanStm rcont statement =
  case statement
  of LetLCPS params rhs label body -> do
       is_cont <- isContinuation label
       if is_cont
         then do
           -- The RHS will become a tail call
           scanAtom True rhs
           -- The body will become a new function
           putGroup =<< liftIO (newGroupDescr (ContID label))
           enterGroup (ContID label) (scanStm rcont body)
         else
           scanAtom False rhs `mappend` scanStm rcont body
     LetrecLCPS defs gid stm ->
       scanGroup (GroupID gid) defs $ scanStm rcont stm
     SwitchLCPS cond alts ->
       scanValue cond `mappend` mconcat [scanStm rcont s | (_, s) <- alts] 
     ReturnLCPS atom -> do
       rconts <- getRConts
       case LocalCPS.needsContinuationCall rconts rcont atom of
         Nothing ->
           -- This statement will become a tail call
           scanAtom True atom
         Just cont_var -> do
           -- This statement will become a non-tail call followed by an
           -- explicit continuation call
           scanAtom False atom
           calledCont cont_var
     ThrowLCPS val ->
       scanValue val

scanFunDef :: LFunDef -> ScanExp
scanFunDef d = do
  rcont <- lookupCont $ definiendum d
  scanStm rcont (funBody $ definiens d)

-- | Scan a function definition group. 
--   The scan creates an 'UnsolvedGroup'.  Also, captured variable constraints
--   are propagated in the scan.  The set of hoisted groups is propagated.
--   Hoisting constraints in the body are propagated.
scanGroup :: GroupID -> Group LFunDef -> ScanExp -> ScanExp
scanGroup group_id group scan_body = do
  enterGroup group_id $
    case group
    of Rec group_members ->
         defineGroup group_id group_members $
         mapM_ scanFunDef group_members
       NonRec fdef -> scanFunDef fdef

  -- Create a descriptor for this group
  putGroup =<< liftIO (newGroupDescr group_id)

  -- Process the body
  defineGroup group_id (groupMembers group) scan_body

-- | Scan a top-level function, generating a set of constraints that determine
--   hoisting and variable capture
scanTopLevelDef :: LocalCPS.RConts
                -> LFunDef
                -> IO (HoistCsts, Set.Set GroupID, [UnsolvedGroup])
scanTopLevelDef rconts def = do
  let continuations = Set.fromList [v | LocalCPS.RCont v <- IntMap.elems rconts]
      initial_context = ScanInputs Map.empty Nothing rconts continuations
  ScanResult () (GlobalConstraints h_csts hoisted groups) <-
    runScan (scanFunDef def) initial_context

  return (h_csts, hoisted, groups)

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
type GroupTable = HashTable.HashTable GroupID UnsolvedGroup

-- | Create a lookup table from ID to group.  The lookup table is used to
--   solve constraints.
mkGroupTable :: [UnsolvedGroup] -> IO GroupTable
mkGroupTable groups = do
  htbl <- HashTable.newHint (==) hashGroupID (length groups)
  forM_ groups $ \g -> HashTable.insert htbl (groupID g) g
  return htbl

forGroups_ :: GroupTable -> [GroupID] -> (UnsolvedGroup -> IO a) -> IO ()
forGroups_ table gids f = mapM_ apply_to_group gids
  where
    apply_to_group gid = do
      Just g <- HashTable.lookup table gid
      f g
      return ()

-- | Determine which groups are hoisted.  The 'groupHoistedVal' field is
--   set to @True@ on hoisted groups.
--
--   The set of groups that will be hoisted is returned.
setupAndSolveHoistingConstraints :: HoistCsts
                                 -> [UnsolvedGroup]
                                 -> Set.Set GroupID
                                 -> GroupTable
                                 -> IO (Set.Set GroupID)
setupAndSolveHoistingConstraints h_csts groups initial_set table = do
  -- Every group in initial_set is hoisted
  initialize_hoisted_groups
  
  -- Create an array of hoisting implications.
  -- if @g2 `elem` h_cst_array !! g@, and @g@ is hoisted, then @g2@ is hoisted.
  h_cst_table <- HashTable.newHint (==) hashGroupID (length groups)
  initialize_hoist_array h_cst_table

  -- Solve constraints
  solveHoistingConstraints table h_cst_table initial_set

  -- Extract results
  readHoistingResults groups
  where
    -- Groups in the set are hoisted
    initialize_hoisted_groups =
      forGroups_ table (Set.toList initial_set) $ \grp ->
      writeIORef (groupHoistedVal grp) True

    initialize_hoist_array htbl =
      -- For each constraint (consequent <== antecedents),
      forM_ h_csts $ \(HoistCst consequent antecedents) ->
      -- for each antecedent,
      forM_ antecedents $ \antecedent -> do
        -- add consequent to the antecedent's table entry
        m_x <- HashTable.lookup htbl antecedent
        let x = fromMaybe [] m_x
        HashTable.update htbl antecedent (consequent : x)

-- | The solving phase for hoisting constraints
solveHoistingConstraints :: GroupTable
                         -> HashTable.HashTable GroupID [GroupID]
                         -> Set.Set GroupID
                         -> IO ()
solveHoistingConstraints table h_csts initial_set = do
  -- Process groups until no changes are made
  workset <- newWorklist (Set.toList initial_set)

  forWorklist workset $ \elt -> do
    -- Find all groups that must be hoisted, given that 'elt' is hoisted
    m_need_marking <- HashTable.lookup h_csts elt
    let need_marking = fromMaybe [] m_need_marking
    forM_ need_marking $ \gid -> do
      -- Look up and mark this group
      Just group <- HashTable.lookup table gid
      change <- modifyCheckIORef (const True) (groupHoistedVal group)
      when change $ putWorklist workset gid

-- | Create a set of all groups that were marked True
readHoistingResults groups = foldM insert_if_hoisted Set.empty groups
  where
    insert_if_hoisted s grp = do
      is_hoisted <- readIORef $ groupHoistedVal grp
      return $ if is_hoisted then Set.insert (groupID grp) s else s

-- | Find defgroups that will be hoisted in a top-level function definition.
--   @id_bound@ is an ID larger than any group ID.
findHoistedGroups :: LFunDef -> LocalCPS.RConts -> IO (Set.Set GroupID)
findHoistedGroups fdef rconts = do
  -- Scan the function definition and generate constraints
  (h_csts, initial_hoisted, unsolved) <- scanTopLevelDef rconts fdef
  
  -- Solve constraints
  table <- mkGroupTable unsolved
  setupAndSolveHoistingConstraints h_csts unsolved initial_hoisted table
