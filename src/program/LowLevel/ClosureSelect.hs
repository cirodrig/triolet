{-| Selection of functions for closure conversion.

Based on which functions are 
-}

{-# Language GeneralizedNewtypeDeriving #-}
module LowLevel.ClosureSelect(Capt, findFunctionsToHoist) where
       
import Control.Monad
import Control.Monad.Identity
import Data.Array.IO
import qualified Data.Graph.Inductive as Graph
import qualified Data.Graph.Inductive.Query.DFS as Graph
import Data.IORef
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid
import qualified Data.Set as Set
import Debug.Trace
import Text.PrettyPrint.HughesPJ

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

-- | An inherited capture set.  @CaptInherit gs@ means that the current group
--   inherits the captured variables of each group in @gs@.  A group can only
--   inherit captured variables from lexically enclosing @letrec@ statements.
newtype CaptInherit = CaptInherit (Set.Set GroupID)
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
            --   the definition.  If any of them are marked for
            --   hoisting, then the function must be hoisted.
            --
            --   A definition group is /not/ part of the context of its body.
          , useContext :: [GroupID]
            -- | Scope in which a function is used.  The scope consists
            --   of all function definitions that are in scope at the use but
            --   not the definition.  If any of them are marked for
            --   hoisting, then the function must be hoisted.
            --
            --   A definition group /is/ part of the scope of its body.
          , useScope :: [GroupID]
          }

-- | While generating constraints, a map is used to keep track of all
--   in-scope local functions.
type FunMap = Map.Map Var FunInfo

-- | A description of a local definition group or single top-level function.
--   The description is used to decide whether to hoist.
data UnsolvedGroup =
  UnsolvedGroup
  { groupID :: {-# UNPACK #-}!GroupID
  , -- | Function definitions in this group
    groupDefs :: !(Group FunDef)
    -- | Inherited captured variables
  , groupInheritedCaptures :: CaptInherit
    -- | Captured variables
  , groupCapturedVal :: !(IORef Capt)
    -- | The hoisting decision for this group
  , groupHoistedVal :: !(IORef Hoist)
  }

type GroupID = Ident UnsolvedGroup

newGroupDescr :: GroupID -> Group FunDef -> CaptInherit -> Capt -> HoistCsts
              -> IO UnsolvedGroup
newGroupDescr gid defs capts c hoists = do
  captured_val <- newIORef c
  hoisted_val <- newIORef False
  return $ UnsolvedGroup { groupID = gid
                         , groupDefs = defs
                         , groupInheritedCaptures = capts
                         , groupCapturedVal = captured_val
                         , groupHoistedVal = hoisted_val}

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
extendContext :: Bool -> GroupID -> [FunDef] -> ScanInputs -> ScanInputs
extendContext in_context gid defs si =
  si {scanFunMap = insert_defs $ Map.map add_to_context $ scanFunMap si}
  where
    insert_defs :: FunMap -> FunMap
    insert_defs m = foldr insert_def m defs

    insert_def (Def v f) m =
      let info = FunInfo (length $ funParams f) gid [] []
      in Map.insert v info m

    add_to_context :: FunInfo -> FunInfo
    add_to_context finfo
      | in_context =
          finfo {useContext = (gid:useContext finfo),
                 useScope = (gid:useScope finfo)}
      | otherwise =
          finfo {useScope = (gid:useScope finfo)}


-- | A scan for computing hoisting and capture information.
newtype Scan = Scan {runScan :: ScanInputs -> IO ScanResult}

type ScanResult = (CaptInherit, -- Variable capture constraints
                   Capt, -- Captured variables
                   HoistCsts, -- Hoisting constraints
                   Set.Set GroupID, -- Hoisted groups
                   [UnsolvedGroup] {- Groups -})

instance Monoid Scan where
  mempty = Scan (\_ -> return mempty)
  Scan f1 `mappend` Scan f2 =
    Scan (\i -> do x <- f1 i
                   y <- f2 i
                   return (x `mappend` y))
  mconcat xs = Scan (\i -> do ys <- sequence [f i | Scan f <- xs]
                              return $ mconcat ys)

-- | Enter a context in which a definition group has been defined, but is not
--   in scope.
enterGroup :: GroupID -> Scan -> Scan
enterGroup gid (Scan f) =
  Scan $ \i -> f (pushContext gid i)

-- | Enter a context in which a definition group is in scope.
--
--   Add the definition group to the environment, and remove the defined
--   variables from the captured variable set.
--
--   If 'in_context' is True, then we're processing the function definitions
--   and should add them to the context.  Otherwise we're processing the
--   body of the definition group and we should not add them to the context.
defineGroup :: Bool -> GroupID -> [FunDef] -> Scan -> Scan
defineGroup in_context gid fdefs (Scan f) =
  define_group $
  defines (map definiendum fdefs) $
  Scan $ \i -> f (extendContext in_context gid fdefs i)
  where
    define_group (Scan f) = Scan $ \env -> do
      (c_csts, c, h_csts, h, groups) <- f env
      let c_csts' = case c_csts
                    of CaptInherit gs -> CaptInherit (Set.delete gid gs)
      return (c_csts', c, h_csts, h, groups)

-- | Scan a reference to a variable, other than a tail call.
--
--   If it's a local variable, the variable will be added to the
--   captured variable set.  If it's a local function, the function
--   will be hoisted.
capture :: Var -> Scan
capture v = Scan $ \env ->
  let (captured, hoisted) =
        if v `Set.member` scanGlobals env
        then (mempty, mempty) 
        else case Map.lookup v $ scanFunMap env
             of Nothing -> (Set.singleton v, mempty)
                Just finfo -> (Set.singleton v, Set.singleton (defGroup finfo))
  in captured `seq` hoisted `seq`
     return (mempty, captured, mempty, hoisted, mempty)

define :: Var -> Scan -> Scan
define v (Scan s) = Scan $ \i -> do
  (c_csts, c, h_csts, h, groups) <- s i
  return (c_csts, Set.delete v c, h_csts, h, groups)

defines :: [Var] -> Scan -> Scan
defines vs (Scan s) = Scan $ \i -> do
  (c_csts, c, h_csts, h, groups) <- s i
  return (c_csts, foldr Set.delete c vs, h_csts, h, groups)

-- | Scan a call of a variable.
--
--   The variable is captured.
--
--   If the callee is not fully applied, or if it's not a tail call, 
--   it must be hoisted.
--
--   Otherwise, if a function enclosing this call is hoisted, the callee
--   must also be hoisted.
called :: Bool -> Var -> Int -> Scan
called is_tail v num_args = Scan $ \env ->
  if v `Set.member` scanGlobals env
  then return mempty
  else let m_finfo = Map.lookup v $ scanFunMap env
           captured = Set.singleton v
           c_cst =
             case m_finfo
             of Just finfo -> CaptInherit (Set.singleton $ defGroup finfo)
                _ -> mempty
           (h_cst, hoisted) =
             case m_finfo
             of Just finfo
                  | is_tail && num_args >= arity finfo ->
                      -- Saturated tail call; do not need to hoist
                      ([HoistCst (defGroup finfo) (useContext finfo)], mempty)
                  | otherwise ->
                      -- Undersaturated or non-tail-call; must hoist
                      (mempty, Set.singleton (defGroup finfo))
                _ -> mempty     -- Unknown function
       in h_cst `seq` hoisted `seq` c_cst `seq`
          return (c_cst, captured, h_cst, hoisted, mempty)

-------------------------------------------------------------------------------
-- Scanning for constraint generation

scanValue :: Val -> Scan
scanValue value =
  case value
  of VarV v    -> capture v
     LitV _    -> mempty
     RecV _ xs -> scanValues xs
     LamV _    -> internalError "scanValue"

scanValues vals = mconcat (map scanValue vals)

scanAtom :: Bool -> Atom -> Scan
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

scanStm :: Stm -> Scan
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

scanFun :: Fun -> Scan
scanFun f =
  defines (funParams f) $ scanStm (funBody f)

-- | Scan a function definition group. 
--   The scan creates an 'UnsolvedGroup'.  Also, captured variable constraints
--   are propagated in the scan.  The set of hoisted groups is propagated.
--   Hoisting constraints in the body are propagated.
scanGroup :: Group FunDef -> Scan -> Scan
scanGroup group scan_body = Scan $ \i -> do
  -- Create a descriptor for this group; add it to the descriptors taken from 
  -- the function bodies.  Do not propagate constraints.
  group_id <- supplyValue $ scanIdSupply i
  (local_c_csts, local_captured, local_h_csts, local_hoisted, local_groups) <-
    flip runScan i $
    case group
    of Rec fs ->
         -- Scan all functions in the group.  Remove references to the group.
         defineGroup True group_id (groupMembers group) $
         mconcat $ map (scanFun . definiens) fs

       NonRec f -> do
         -- Scan this function
         enterGroup group_id $ scanFun $ definiens f
         
  -- Create a descriptor for this group
  descr <- newGroupDescr group_id group
           local_c_csts local_captured local_h_csts

  -- Process the body
  (body_c_csts, body_c, body_h_csts, body_h, body_groups) <-
    flip runScan i $ defineGroup False group_id (groupMembers group) scan_body

  return (captInheritUnion local_c_csts body_c_csts,
          Set.union body_c local_captured,
          body_h_csts, Set.union body_h local_hoisted,
          descr : local_groups ++ body_groups)

-- | Scan a top-level function, generating a set of constraints that determine
--   hoisting and variable capture
scanTopLevelDef :: Set.Set Var
                -> FunDef
                -> IO (HoistCsts, Set.Set GroupID, [UnsolvedGroup], GroupID)
scanTopLevelDef globals (Def v f) = do
  id_supply <- newIdentSupply
  let initial_context = ScanInputs Map.empty globals id_supply
  (c_csts, captured, h_csts, hoisted, groups) <-
    runScan (scanFun f) initial_context
  id_bound <- supplyValue id_supply

  unless (Set.null $ case c_csts of CaptInherit s -> s) $
    internalError "scanTopLevelDef: Top-level function captures variables"
  
  unless (Set.null captured) $
    internalError "scanTopLevelDef: Top-level function captures variables"

  return (h_csts, hoisted, groups, id_bound)

-------------------------------------------------------------------------------
-- Constraint solving
--
-- Hoisting constraints and capture constraints are solved independently.
-- Both use a worklist algorithm for solving.

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
solveHoistingConstraints table h_csts initial_set = go initial_set
  where
    go workset =
      -- Remove an arbitrary element from the set
      case Set.minView workset
      of Just (elt, workset') -> do
           -- Mark all groups implied by this element as hoisted.
           -- Groups that were changed by marking are added to the workset.
           go =<< foldM mark_group workset' =<< readArray h_csts elt
         Nothing -> do
           -- All updates are finished
           return ()

    -- Mark a group as hoisted.  Add it to the workset if it was not
    -- already hoisted.
    mark_group workset gid = do
      group <- readArray table gid
      
      old_hoisted <- readIORef $ groupHoistedVal group
      if old_hoisted
        then return workset
        else do
          writeIORef (groupHoistedVal group) True
          return $ Set.insert gid workset


setupAndSolveCaptureConstraints :: GroupArray -> [UnsolvedGroup] -> IO ()
setupAndSolveCaptureConstraints table groups = do
  -- Create an array of closure implications.
  -- if @g2 `elem` c_cst_array !! g@, then @g2@'s captured variables are a 
  -- superset of @g@'s captured variables.
  table_bounds <- getBounds table
  c_csts <- newArray table_bounds []
  forM_ groups $ \inheritor ->
    case groupInheritedCaptures inheritor
    of CaptInherit gids -> forM_ (Set.toList gids) $ \endower ->
         writeArray c_csts endower . (groupID inheritor :) =<< 
         readArray c_csts endower

  -- Solve
  go c_csts (Set.fromList $ map groupID groups)
  where
    go :: IOArray GroupID [GroupID] -> Set.Set GroupID -> IO ()
    go c_csts workset =
      -- Remove an arbitrary element from the set
      case Set.minView workset
      of Just (elt, workset') -> do
           -- Update all groups that inherit from this one.
           -- Groups that were changed by marking are added to the workset.
           endower <- readArray table elt
           endower_value <- readIORef $ groupCapturedVal endower
           inheritors <- readArray c_csts elt
           go c_csts =<< foldM (update_group endower_value) workset' inheritors
         Nothing -> do
           -- All updates are finished
           return ()

    update_group endower_value workset inheritor = do
      grp <- readArray table inheritor
      inheritor_value <- readIORef $ groupCapturedVal grp
      
      -- Does this change the set of captured variables?
      let new_value = Set.union endower_value inheritor_value
      if new_value == inheritor_value
        then return workset
        else do writeIORef (groupCapturedVal grp) new_value
                return (Set.insert inheritor workset)

finalizeGroup :: IdentSupply Var -> UnsolvedGroup -> IO SolvedGroup
finalizeGroup id_supply grp = do
  captured <- readIORef $ groupCapturedVal grp
  hoisted <- readIORef $ groupHoistedVal grp
  
  if not hoisted
    then return $ UnhoistedGroup (map definiendum $ groupMembers $ groupDefs grp)
    else runFreshVarM id_supply $ make_closure (Set.toList captured)
  where
    make_closure captured =
      case groupDefs grp
      of NonRec def -> do
           (_, closure) <- mkNonrecClosure def captured
           return $ HoistedGroup (NonRec (definiendum def, closure))
         Rec defs -> do
           closures <- mkRecClosures defs captured
           return $ HoistedGroup (Rec $ zip (map definiendum defs) (map snd closures))

printUnsolvedGroup :: UnsolvedGroup -> IO ()
printUnsolvedGroup grp = do
  print $ text "group" <+> text (show $ groupID grp) <+> 
    fsep (map (pprVar . definiendum) $ groupMembers $ groupDefs grp)
  capt <- readIORef $ groupCapturedVal grp
  print $ text "  captured" <+> fsep (map pprVar $ Set.toList capt)
  putStrLn $ "  inherits " ++ show (groupInheritedCaptures grp)

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
  setupAndSolveCaptureConstraints table groups
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