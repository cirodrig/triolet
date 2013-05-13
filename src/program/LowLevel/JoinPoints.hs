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
/tail-calls/ graph in which a node represents a local or top-level function
and an edge @f -> g@ means that @f@ tail-calls @g@.
Each node is labeled with a list of /parents/.  The parents of a function
@f@ are the functions whose body contains the definition of @f@ somewhere
inside.
Each node is also labeled with a /root/, which is its unique non-join-point
caller.  The initial set of roots is determined optimistically.  Any function
that is used in some way other than a saturated tail call is a root, and the
top-level function is a root.

The analysis turns additional functions into roots if they have any of several
properties.  A function becomes a root if it has two non-join-point callers.
A function becomes a root if its would-be root is not a parent.
-}

module LowLevel.JoinPoints(convertJoinPoints) where

import Control.Monad
import qualified Data.HashTable as HashTable
import Data.Graph.Inductive(Gr)
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Query.DFS
import Data.IORef
import qualified Data.IntMap as IntMap
import Data.List as List
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid
import qualified Data.Set as Set
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import Common.Worklist
import LowLevel.CodeTypes
import LowLevel.FreshVar
import LowLevel.Rename
import LowLevel.Syntax
import LowLevel.Print
import Globals

-------------------------------------------------------------------------------
-- Finding join points.

-- A top-level function is first scanned to build an 'AnalysisTable'
-- containing information about all local functions.  Then all local functions 
-- that do /not/ satisfy the criteria for being join points are identified.
-- The list of such functions is returned.

-- | A list of a function's parents.  @f@ is a parent of @g@ if the
--   definition of @f@ contains the definition of @g@.
type Parents = [Var]

-- | Analysis data associated with a function.
data AnalysisData =
  AnalysisData
  { -- | The root currently assigned to the function.
    --   A function is a root iff it is its own root.
    --   'Nothing' if no root has been assigned.
    rootRef :: {-# UNPACK #-}!(IORef (Maybe Var))

    -- | Arity of this function
  , arity :: {-# UNPACK #-}!Int

    -- | Functions that are tail called by this function.
    --   This IORef is updated when building the hash table.
    --   By the time solving begins, all callee lists are immutable.
  , tailCallees :: {-# UNPACK #-}!(IORef [Var])

    -- | The function definitions containing the definition of this function
  , parents :: !Parents
  }

isRootData :: Var -> AnalysisData -> IO Bool
isRootData v d = do
  root <- readIORef $ rootRef d
  return $ root == Just v

type AnalysisTable = HashTable.HashTable Var AnalysisData

lookupFun :: AnalysisTable -> Var -> IO (Maybe AnalysisData)
lookupFun = HashTable.lookup

lookupFun' :: AnalysisTable -> Var -> IO AnalysisData
lookupFun' tbl v = do
  md <- lookupFun tbl v
  case md of
    Just d -> return d
    Nothing -> internalError "lookupFun'"

-- | Find the hash table members that are roots
getRoots :: AnalysisTable -> IO [Var]
getRoots tbl = do
  members <- HashTable.toList tbl
  roots <- filterM (uncurry isRootData) members
  return $ map fst roots

-- | Make the given variable a root, if it's in the table.
makeRoot :: AnalysisTable -> Var -> IO ()
makeRoot tbl v = do
  md <- lookupFun tbl v
  case md of
    Nothing -> return ()
    Just d  -> writeIORef (rootRef d) (Just v)

createAnalysisTable :: FunDef -> IO AnalysisTable
createAnalysisTable def = do
  tbl <- HashTable.new (==) (HashTable.hashInt . fromIdent . varID)
  scanDef tbl [] def
  makeRoot tbl (definiendum def) -- The top-level function is a root
  return tbl

-- | Create an entry for a function definition
setupDef tbl parent_list (Def v f) = do
  root_ref <- newIORef Nothing
  callees_ref <- newIORef []
  HashTable.insert tbl v $ AnalysisData { rootRef = root_ref 
                                        , arity = length $ funParams f
                                        , tailCallees = callees_ref 
                                        , parents = parent_list}
  return callees_ref

-- | Scan a function definition
scanDefBody tbl parent_list callees_ref (Def v f) =
  scanStm tbl callees_ref (v : parent_list) (funBody f)

scanDef :: AnalysisTable -> Parents -> FunDef -> IO ()
scanDef tbl parent_list def = do
  callees_ref <- setupDef tbl parent_list def
  scanDefBody tbl parent_list callees_ref def

scanDefs :: AnalysisTable -> Parents -> Group FunDef -> IO ()
scanDefs tbl parent_list defs = do
  callees <- mapM (setupDef tbl parent_list) (groupMembers defs)
  zipWithM_ (scanDefBody tbl parent_list) callees (groupMembers defs)

scanStm tbl callees_ref parent_list statement =
  case statement
  of LetE _ rhs body -> do
       scanAtom tbl rhs
       continue body
     LetrecE defs body -> do
       scanDefs tbl parent_list defs
       continue body
     SwitchE scrutinee alts -> do
       scanVal tbl scrutinee
       sequence_ [continue s | (_, s) <- alts]
     ReturnE (CallA _ (VarV op) args) -> do
       -- tail call
       scanTailCall tbl callees_ref op (length args)
       scanVals tbl args
     ReturnE atom ->
       scanAtom tbl atom
     ThrowE v ->
       scanVal tbl v
  where
    continue s = scanStm tbl callees_ref parent_list s

-- | Scan a tail call.  If the callee is in the table and the call has
--   the correct number of arguments, record the fact
--   that the current function has a tail call by modifying @callees_ref@.
scanTailCall tbl callees_ref op n_args = do
  md <- lookupFun tbl op
  case md of
    Just d | n_args == arity d -> modifyIORef callees_ref (insert op)
    _                          -> return ()
  
scanAtom tbl atom =
  case atom
  of ValA vs -> scanVals tbl vs
     CallA _ v vs -> scanVal tbl v >> scanVals tbl vs
     PrimA _ vs -> scanVals tbl vs
     PackA _ vs -> scanVals tbl vs
     UnpackA _ v -> scanVal tbl v

scanVals tbl vs = mapM_ (scanVal tbl) vs

scanVal tbl value = 
  case value
  of VarV v -> makeRoot tbl v
     RecV _ vs -> scanVals tbl vs
     LitV _ -> return ()

solveJoinPoints tbl wl =
  -- Iterate until worklist is empty
  forWorklist wl $ \f -> do
    f_info <- lookupFun' tbl f

    -- For each function that is tail-called by f
    callees <- readIORef $ tailCallees f_info
    forM_ callees $ \callee -> do
      callee_info <- lookupFun' tbl callee

      -- Look up the root currently assigned to 'f'.  Something must
      -- have been assigned before 'f' was put into the worklist.
      -- This lookup is in the inner loop because the root of 'f' may be
      -- modified by the inner loop.
      m_f_root <- readIORef $ rootRef f_info
      f_root <- case m_f_root
                of Nothing -> internalError "solveJoinPoints"
                   Just rt -> return rt

      -- The callee may only be a join point if it is defined inside 
      -- the root of f.  Otherwise it will beome a root.
      let new_root = if f_root `elem` parents callee_info
                     then f_root
                     else callee
      updateRoot wl callee callee_info new_root

-- | Update a function's root
updateRoot :: Worklist Var -> Var -> AnalysisData -> Var -> IO ()
updateRoot wl callee callee_info new_root = do
  -- Assign the callee's root.  If the new root and old root disagree, 
  -- then the callee becomes a root.
  let update_root Nothing      = Just new_root
      update_root (Just old_root) 
        | old_root == new_root = Just new_root
        | otherwise            = Just callee -- Callee becomes a root
  changed <- modifyCheckIORef update_root $ rootRef callee_info
  when changed $ putWorklist wl callee

-- | The main analysis routine.  Given a top-level function definition, this
--   analysis returns the list of join points that are defined in the function.
getJoinPoints :: FunDef -> IO [Var]
getJoinPoints top_level_def = do
  -- Setup
  tbl <- createAnalysisTable top_level_def
  roots <- getRoots tbl
  wl <- newWorklist roots

  -- Computation
  solveJoinPoints tbl wl

  -- Read the set of join points
  let append_root_entry root_list (v, d) = do
        is_root <- isRootData v d
        return $! if is_root then root_list else v : root_list
  entries <- HashTable.toList tbl
  foldM append_root_entry [] entries

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
convertJoinPointsDef :: FunDef -> IO FunDef
convertJoinPointsDef def = do
  join_points_list <- getJoinPoints def
  let join_points_set = Set.fromList join_points_list
  return $ labelFunDef join_points_set def

convertJoinPointsGroup :: Group GlobalDef -> IO (Group GlobalDef)
convertJoinPointsGroup grp =
  case grp
  of NonRec def -> NonRec `liftM` convert_def def
     Rec defs -> Rec `liftM` mapM convert_def defs
  where
    convert_def (GlobalFunDef fdef) =
      GlobalFunDef `liftM` convertJoinPointsDef fdef
    convert_def (GlobalDataDef ddef) =
      return $ GlobalDataDef ddef

convertJoinPoints :: Module -> IO Module
convertJoinPoints mod = do
  -- Globally rename functions
  rn_mod <- withTheLLVarIdentSupply $ \var_ids ->
    runFreshVarM var_ids $ renameModule RenameFunctions mod
  
  -- Convert all join points
  globals <- mapM convertJoinPointsGroup $ moduleGlobals mod
  return $ mod {moduleGlobals = globals}