{-| Selection of functions for closure conversion.

Based on which functions are 
-}

{-# Language FlexibleInstances, TypeSynonymInstances,
             GeneralizedNewtypeDeriving #-}
module LowLevel.ClosureSelect(Free, findFunctionsToHoist) where

import Prelude hiding(mapM)
import Control.Applicative
import Control.Monad hiding(mapM, forM)
import Control.Monad.Identity hiding(mapM, forM)
import Control.Monad.Reader hiding(mapM, forM)
import Control.Monad.RWS hiding(mapM, forM)
import Control.Monad.Trans
import Data.Array.IO
import Data.Function
import qualified Data.Graph.Inductive as Graph
import qualified Data.Graph.Inductive.Query.DFS as Graph
import qualified Data.HashTable as HashTable
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
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
import LowLevel.CodeTypes
import LowLevel.FreshVar
import LowLevel.Print
import LowLevel.Syntax
import LowLevel.Types
import LowLevel.Build
import LowLevel.Closure.CCInfo
import LowLevel.Closure.Code
import LowLevel.Closure.Capture
import LowLevel.Closure.Hoisting
import LowLevel.Closure.LocalCPSAnn
import qualified LowLevel.Closure.LocalCPS as LocalCPS
import Globals

debug = False

-------------------------------------------------------------------------------
-- Continuation map construction

-- | A map from letrec-bound function names to continuation function names.
--   The map associates a function to its continuation only if the continuation
--   should be moved to the function's @letrec@ statement.  Every continuation
--   appears exactly once in the map.
--   The map is injective.
type ContMap = Map.Map Var Var

-- | A map from continuation function name to letrec-bound function name.
--   The continuation will be moved to the same group as the letrec-bound
--   function.  The map is constructed by reversing the associations in
--   a 'ContMap'.
type CoContMap = Map.Map Var Var

-- | Extract global information needed by other passes.
--
--   The tuple members are:
--
--   1. The set of continuation labels in the program, including labels that
--      won't become functions.
--   2. A map from continuation to its first caller.
--   3. A map from caller to continuation.  For each continuation, only the 
--      first caller is in the map.
mkContMap :: LocalCPS.RConts -> LFunDef -> (Set.Set Var, ContMap, CoContMap)
mkContMap rconts def = let
  -- Construct a map from continuation to caller
  conts_set = LocalCPS.continuationsSet rconts
  caller_map = findOutermostCallerDef rconts conts_set def

  -- Reverse the map, producing a map from caller to continuation
  cont_map = Map.fromList [(caller, cont)
                          | (cont, caller) <- Map.toList caller_map]
  in (conts_set, cont_map, caller_map)

-- | For each continuation called in this function definition, find
--   the lexically outermost caller.
--
--   We rely on the monoid definition of maps to choose the outermost caller.
--   In calls to 'mappend', entries in the left map take precedence.
findOutermostCallerDef :: LocalCPS.RConts -> Set.Set Var -> LFunDef
                       -> ContMap
findOutermostCallerDef rconts conts_set (Def v f) =
  -- Get the continuation that was computed for this function
  (let current_cont =
        case LocalCPS.lookupCont v rconts
        of Just c -> c
           Nothing -> internalError $ "No continuation for " ++ show v
  in -- Determine whether an explicit continuation call will be
     -- inserted here 
     case current_cont
     of LocalCPS.RCont cont _ -> Map.singleton cont v
        _   -> mempty) `mappend`
  findOutermostCallerFun rconts conts_set v f

findOutermostCallerFun rconts conts_set v f = 
  findOutermostCaller rconts conts_set v (funBody f)

-- | For each continuation called in this statement, find the lexically
--   outermost caller.
--
--   We rely on the monoid definition of maps to choose the outermost caller.
--   In calls to 'mappend', entries in the left map take precedence.
findOutermostCaller :: LocalCPS.RConts -- ^ Continuation of each function
                    -> Set.Set Var     -- ^ The set of continuations
                    -> Var             -- ^ The function containing the current
                                       --   statement (may be a continuation)
                    -> LStm            -- ^ Statement to scan
                    -> ContMap
                       -- ^ Outermost caller of each continuation that
                       --   is called in the statement, parameters of
                       --   continuations, and local variables at each
                       --   definition group
findOutermostCaller rconts conts_set current_fun stm =
  case stm
  of LetLCPS params rhs label body ->
       if label `Set.member` conts_set
       then
         -- Body is a continuation function.
         -- Use the label as the current function while processing the body.
         findOutermostCaller rconts conts_set label body
       else continue body

     LetrecLCPS defs group_id body ->
       let defs_map = mconcat (map enter $ groupMembers defs)
           body_map = continue body
       in defs_map `mappend` body_map

     SwitchLCPS cond alts ->
       mconcat $ map (continue . snd) alts

     ReturnLCPS atom ->
       -- Get the continuation that was computed for this function
       let current_cont =
             case LocalCPS.lookupCont current_fun rconts
             of Just c -> c
                Nothing -> internalError $
                           "No continuation for " ++ show current_fun
       in -- Determine whether an explicit continuation call will be
          -- inserted here 
          case LocalCPS.needsContinuationCall rconts current_cont atom
          of Just cont -> Map.singleton cont current_fun
             Nothing   -> mempty

     ThrowLCPS exc ->
       mempty
  where
    enter def =
      findOutermostCallerDef rconts conts_set def
    continue stm =
      findOutermostCaller rconts conts_set current_fun stm


-------------------------------------------------------------------------------

-- | A mapping that associates function IDs with the definition groups where
--   the functions belong.  All functions that should be relocated are
--   in the mapping.
type MovedFunctions = IntMap.IntMap (Ident GroupLabel)

-- | Group together all functions that have the same continution.
--
--   The return value is a map from function ID to the definition group ID
--   that the function should be moved to.
unifyRConts :: LocalCPS.RConts  -- ^ Continuations of each function
            -> Set.Set Var      -- ^ Hoisted functions
            -> CoContMap        -- ^ Lexically first caller of each continuation
            -> (Var -> Maybe (Ident GroupLabel))
               -- ^ ID of group containing each function
            -> MovedFunctions
unifyRConts rconts hoisted_set caller_map lookup_group = let
  -- Map each continuation function ID to all functions that transitively
  -- tail-call the continuation
  tail_callers_of_continuation :: IntMap.IntMap [Int]
  tail_callers_of_continuation =
    IntMap.mapWithKey insert_self $
    foldl' insert_cont IntMap.empty $ IntMap.toList rconts

  in IntMap.fromList [ (f_id, cont_group_id)
                     | (cont_id, f_ids) <-
                          IntMap.toList tail_callers_of_continuation

                       -- Look up the destination group ID.
                       -- Find the first function that calls the continuation, 
                       -- then find it's group.
                     , let cont_group_id =
                             case IntMap.lookup cont_id caller_int_map
                             of Just first_caller ->
                                  case lookup_group first_caller 
                                  of Just gid -> gid
                                     Nothing -> internalError "unifyRConts"
                                Nothing -> internalError "unifyRConts"
                     , f_id <- f_ids]
  where
    -- A continuation should appear in the same list as its callers
    insert_self k v | k `elem` v = v
                    | otherwise = k : v

    -- Insert a (function ID, continuation) association into the unified
    -- continuation table.
    insert_cont m (f_id, LocalCPS.RCont k _) =
      insert_cont' f_id (fromIdent $ varID k) m
    
    insert_cont m _ = m
    
    insert_cont' f_id k_id m
      | Just (LocalCPS.RCont k' _) <- IntMap.lookup k_id rconts =
          insert_cont' f_id (fromIdent $ varID k') m
      | otherwise =
          IntMap.insertWith (++) k_id [f_id] m

    is_unhoisted f_id = not $ IntSet.member f_id hoisted

    hoisted =
      IntSet.fromList $ map (fromIdent . varID) $ Set.toList hoisted_set

    caller_int_map = IntMap.fromList [ (fromIdent $ varID f, g)
                                     | (f, g) <- Map.toList caller_map]

-- | Move un-hoisted functions to different definition groups.  Turn
--   continuations into functions.  Insert tail calls to continuations.
--
--   Functions that aren't hoisted and that share the same continuation 
--   are moved to the lexically first definition group where any such function
--   is defined.  Moving code this way ensures that the region of code
--   where the function is in scope can only become bigger, and furthermore,
--   if any tail-calls are inserted by the transformation, the callee is in
--   scope where it is called.
--
--   After moving code, functions may refer to variables that are not
--   in scope at the definition site.  That is fixed later.
moveFunctions :: IdentSupply Var
              -> LocalCPS.RConts
              -> MovedFunctions
                 -- ^ The set of functions and continuations that should be
                 --   moved, and their destination groups
              -> ContMap
              -> LFunDef
              -> IO FunDef
moveFunctions var_ids rconts moved_functions cont_map ann_def = do
  (extracted_funs, def1) <- extractFunctions var_ids rconts moved_functions ann_def
  
  return $ insertFunctions moved_functions extracted_funs def1

data MFContext =
  MFContext
  { -- | Return continuations of each function and continuation.
    --   The return continuation is looked up to decide where to insert
    --   explicit calls to continuations.
    mfRConts     :: !LocalCPS.RConts

    -- | Moved functions.  Definitions of moved functions are extracted
    --   from the code and returned in a list.
  , mfMoved      :: !MovedFunctions

    -- | The function containing the current statement 
  , mfCurrentFun :: Var

    -- | Return type of the function containing the current statement before
    --   CPS conversion.
  , mfRType      :: [ValueType]

    -- | CPS-transformed return type of the function containing
    --   the current statement.  This is either the function's original
    --   return type, or its continuation's return type.
  , mfContType    :: [ValueType]
  , mfIdentSupply :: {-# UNPACK #-}!(IdentSupply Var)
  }

-- | Get the CPS-transformed function's return type.
--   If the function has a continuation, it's the continuation's return type. 
--   Otherwise, it's the function's original return type.
--   If the function
cpsReturnType :: LFunDef -> LocalCPS.RConts -> [ValueType]
cpsReturnType (Def v f) rconts =
  lookup_cps_return_type v $ funReturnTypes f
  where
    -- Look up the CPS-transformed function's return type.
    -- If the function has a continuation, take the continuation's return type.
    lookup_cps_return_type fun_name fun_return_type =
      case IntMap.lookup (fromIdent $ varID fun_name) rconts
      of Just (LocalCPS.RCont cont_fun rtypes) ->
           -- Look up the continuation's return type
           lookup_cps_return_type cont_fun rtypes
         _ -> fun_return_type

-- | Extract functions from the code.
--
--   A function definition is created for each continuation, and the
--   original continuation is removed from the code.  Tail-calls to
--   continuations are inserted.  In functions where tail-calls are inserted,
--   return types are changed.
extractFunctions :: IdentSupply Var
                 -> LocalCPS.RConts
                 -> MovedFunctions
                 -> LFunDef
                 -> IO ([(Ident GroupLabel, LFunDef)], LFunDef)
extractFunctions supply rconts moved def = do
  let no_fun = internalError "extractFunctions: No function" 
      no_rettype = internalError "extractFunctions: No return type"
      context = MFContext rconts moved no_fun no_rettype no_rettype supply
  (def', (), cont_funs) <-
    runRWST (extractFunctionsDef def) context ()
  return (cont_funs, def')

extractFunctionsDef def@(Def v f) = do
  -- Compute this function's new return type
  rconts <- asks mfRConts
  let new_rtype = cpsReturnType def rconts
  let new_ctx ctx = ctx { mfRType = funReturnTypes f
                        , mfContType = new_rtype
                        , mfCurrentFun = v}
  local new_ctx $ do
    body' <- extractFunctionsStm (funBody f)
    let f' = mkFun (funConvention f) (funInlineRequest f) (funFrameSize f)
             (funParams f) new_rtype body'
    return $ Def v f'

extractFunctionsStm stm =
  case stm
  of LetLCPS params rhs label body -> do
       moved <- asks mfMoved
       case IntMap.lookup (fromIdent $ varID label) moved of
         Just destination_group -> do
           -- Create continuation function
           rtype <- asks mfRType
           let fun = mkFun ClosureCall False 0 params rtype body
           cont_def <- extractFunctionsDef (Def label fun)
           tell [(destination_group, cont_def)]

           -- The RHS becomes a tail expression
           return $ ReturnLCPS rhs
         Nothing -> do
           body' <- extractFunctionsStm body
           return $ LetLCPS params rhs label body'

     LetrecLCPS defs group_id body -> do
       moved <- asks mfMoved
       defs' <- mapM extractFunctionsDef $ groupMembers defs
       let (defs_moved, defs_here) = partition_moved moved defs'
       tell defs_moved
       body' <- extractFunctionsStm body
       return $ LetrecLCPS (Rec defs_here) group_id body'
     
     SwitchLCPS cond alts -> do
       alts' <- mapM do_alt alts
       return $ SwitchLCPS cond alts'
     
     ReturnLCPS atom -> do
       context <- ask
       let moved = mfMoved context
           rconts = mfRConts context
           current_fun = mfCurrentFun context
           rtype = mfRType context
       let current_cont =
             case LocalCPS.lookupCont current_fun rconts
             of Just c -> c
                Nothing -> internalError $ "No continuation for " ++ show current_fun
       case LocalCPS.needsContinuationCall rconts current_cont atom of
         Just current_cont -> do
           -- This function has a continuation call.
           -- What used to be the function's return values becomes bound to
           -- temporary variables, then passed to the continuation call.
           tmpvars <- mapM newAnonymousVar_mf rtype

           -- Use an arbitrary variable as the label; its value is ignored
           return $ LetLCPS tmpvars atom current_cont $
             ReturnLCPS (CallA ClosureCall (VarV current_cont) (map VarV tmpvars))
         Nothing ->
           return $ ReturnLCPS atom
     ThrowLCPS exc ->
       return $ ThrowLCPS exc
  where
    do_alt (tag, s) = liftM ((,) tag) $ extractFunctionsStm s
    
    -- Partition a set of function definitions into those that are moved 
    -- and those that are left in place.
    partition_moved :: MovedFunctions
                    -> [LFunDef]
                    -> ([(Ident GroupLabel, LFunDef)], [LFunDef])
    partition_moved moved defs = go id id defs
      where
        go moved_defs unmoved_defs (def:defs) =
          case IntMap.lookup (fromIdent $ varID $ definiendum def) moved
          of Nothing  -> go moved_defs (unmoved_defs . (def:)) defs
             Just gid -> go (moved_defs . ((gid, def):)) unmoved_defs defs

        go moved_defs unmoved_defs [] = (moved_defs [], unmoved_defs [])

    newAnonymousVar_mf t = do
      id_supply <- asks mfIdentSupply
      lift $ runFreshVarM id_supply $ newAnonymousVar t

-- | Insert the extracted function definitions into the code.
insertFunctions :: MovedFunctions
                   -- ^ Map from function to its continuation
                -> [(Ident GroupLabel, LFunDef)]
                   -- ^ Continuation function definitions
                -> LFunDef   -- ^ Top-level function definition
                -> FunDef
insertFunctions moved_functions funs def =
  let fun_map = foldl' insert_def Map.empty funs
        where
          insert_def m (grp, f) = Map.insertWith (++) grp [f] m
  in runReader (insertFunctionsDef def) (moved_functions, fun_map)

insertFunctionsDef (Def v f) = do
  body <- insertFunctionsStm $ funBody f
  return $ Def v (f {funBody = body})

insertFunctionsStm stm =
  case stm
  of LetLCPS params rhs _ body ->
       LetE params rhs <$> insertFunctionsStm body
     LetrecLCPS defs group_id body -> do
       -- Add continuations to this definition group
       (_, fun_map) <- ask
       let functions_here = fromMaybe [] $ Map.lookup group_id fun_map
       let defs' = functions_here ++ groupMembers defs

       -- Recurse on the bodies of these function definitions
       finished_defs <- mapM insertFunctionsDef defs'

       finished_body <- insertFunctionsStm body

       -- If the transformation has removed all local function definitions,
       -- then eliminate this 'Letrec' term
       if null finished_defs
         then return finished_body
         else return $ LetrecE (Rec finished_defs) finished_body
     SwitchLCPS cond alts ->
       SwitchE cond <$> mapM do_alt alts
     ReturnLCPS atom -> pure (ReturnE atom)
     ThrowLCPS val -> pure (ThrowE val)
     where
       do_alt (tag, s) = do
         s' <- insertFunctionsStm s
         return (tag, s')

-------------------------------------------------------------------------------

lookupDestinationLocals f caller_map fun_to_group locals_in_scope =
  -- Look up the group of @f@ first.  If @f@ is not a continuation, this will
  -- produce the answer.
  from_group f $

  -- If @f@ is a continuation, look up its non-continuation caller.
  case Map.lookup f caller_map
  of Just caller -> from_group caller invalid_destination
     Nothing -> no_caller
  where
    from_group f handle_continuation =
      case fun_to_group f
      of GroupID gid ->
           -- Local functions are never moved to a new group
           case IntMap.lookup (fromIdent gid) locals_in_scope
           of Just xs -> Set.fromList xs
              Nothing -> no_group

         ContID _ -> handle_continuation

    no_group =
      internalError "lookupDestinationLocals: Missing information for definition group"
    no_caller =
      internalError "lookupDestinationLocals: Continuation has no caller"
    invalid_destination =
      internalError "lookupDestinationLocals: Invalid destination group"

-- | Find all functions that should be hoisted in a top-level
--   function definition.  For each function, determine what
--   variables it captures and whether it should be hoisted.
--
--   The captured variables and hoisting decisions will always be the same
--   for functions defined in the same definition group.
findFunctionsToHoist :: IdentSupply Var
                     -> Set.Set Var
                     -> FunDef
                     -> IO (FunDef, Map.Map Var CCInfo)
findFunctionsToHoist var_ids global_vars def = do
  -- Label possible continuations
  (ann_fun, id_bound) <- labelFunction var_ids (definiens def)
  let ann_def = Def (definiendum def) ann_fun

  -- Compute continuations
  rconts <- LocalCPS.identifyLocalContinuations ann_def

  -- Find the first caller of each continuation
  let (conts_set, cont_map, caller_map) =
        mkContMap rconts ann_def

  when debug $ do
    putStrLn "Computing hoisting and variable capture for closure conversion"
    print $ pprLFunDef ann_def
    print $ text "Continuations:" <+>
      fsep [parens $ int f <+> text "|->" <+> text (show k)
           | (f, k) <- IntMap.toList rconts]
    print $ text "Callers:" <+>
      fsep [parens $ text (show f) <+> text "called by" <+> text (show k)
           | (f, k) <- Map.toList caller_map]

  -- Compute hoisting
  (hoisted_set, fun_to_group) <- findHoistedGroups ann_def rconts

  -- Compute free variables
  captures <- findCapturedVariables rconts global_vars conts_set ann_def
  
  -- Debugging
  when debug $ do
    putStrLn $ "Hoisted set: " ++ show hoisted_set
    putStrLn "Free variables:"
    print captures
  
  -- Move function definitions so that all functions having the same
  -- continuation are in the same definition group
  let moved_functions = unifyRConts rconts hoisted_set caller_map fun_to_group
  cont_def <- moveFunctions var_ids rconts moved_functions cont_map ann_def

  -- Construct closure conversion info
  let lookup_function f =
        FunAnalysisResults
        { funHoisted  = f `Set.member` hoisted_set
        , funCaptured = fromMaybe Set.empty $ Map.lookup f captures
        }
  cc_info <- runFreshVarM var_ids $
             stmCCInfo lookup_function Set.empty (funBody $ definiens $ cont_def)

  when debug $ do
    putStrLn "Results of analysis:"
    print $ vcat[hang (pprVar v) 2 (pprCCInfo cc) | (v, cc) <- cc_info]
    putStrLn "Unified RConts"
    print moved_functions
    putStrLn "Moved"
    print $ pprFunDef cont_def

  return (cont_def, Map.fromList cc_info)
