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
import LowLevel.LocalCPSAnn
import qualified LowLevel.LocalCPS as LocalCPS
import LowLevel.Print
import LowLevel.Syntax
import LowLevel.Types
import LowLevel.Build
import LowLevel.Closure.CCInfo
import LowLevel.Closure.Code
import LowLevel.Closure.Capture
import LowLevel.Closure.Hoisting
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
--   1. The set of continuations in the program and their parameter variables.
--   2. A map from continuation to its first caller.
--   3. A map from caller to continuation.  For each continuation, only the 
--      first caller is in the map.
--   4. The set of local variables in scope at each definition group.
mkContMap :: LocalCPS.RConts -> LFunDef -> (ContMap, CoContMap)
mkContMap rconts def = let
  -- Construct a map from continuation to caller
  conts_set = Set.fromList [k | LocalCPS.RCont k <- IntMap.elems rconts]
  caller_map = findOutermostCallerDef rconts conts_set def

  -- Reverse the map, producing a map from caller to continuation
  cont_map = Map.fromList [(caller, cont)
                          | (cont, caller) <- Map.toList caller_map]
  in (cont_map, caller_map)

-- | For each continuation called in this function definition, find
--   the lexically outermost caller.
--
--   We rely on the monoid definition of maps to choose the outermost caller.
--   In calls to 'mappend', entries in the left map take precedence.
findOutermostCallerDef :: LocalCPS.RConts -> Set.Set Var -> LFunDef
                       -> ContMap
findOutermostCallerDef rconts conts_set (Def v f) =
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
       -- If this function has a continuation, it will be called here
       let current_cont =
             case LocalCPS.lookupCont current_fun rconts
             of Just c -> c
                Nothing -> internalError $ "No continuation for " ++ show current_fun
       in case LocalCPS.needsContinuationCall rconts current_cont atom
          of Just current_cont ->
               Map.singleton current_cont current_fun
             Nothing ->
               mempty

     ThrowLCPS exc ->
       mempty
  where
    enter def =
      findOutermostCallerDef rconts conts_set def
    continue stm =
      findOutermostCaller rconts conts_set current_fun stm

-------------------------------------------------------------------------------
-- Computation of in-scope variables

-- | Compute the set of variables that is in scope at the definition of each
--   local function or procedure /after/ closure conversion.
--
--   The in-scope set is mostly the same before closure conversion as
--   after closure conversion.  Variable capture, by itself, does not
--   change the in-scope set.  However, continuations are moved to a
--   new location in the source code.  This changes the in-scope set
--   at the point where the continuation is defined.  It does not
--   change the in-scope set in the body of the continuation.  This also
--   puts the continuation into the scope of other variables. 
mkInScopeSet :: ContMap -> LFunDef -> LocalsAtGroup
mkInScopeSet cont_map def =
  let local_list = mkInScopeSetFun cont_map [] (definiens def)
  in IntMap.fromList local_list

mkInScopeSetFun cont_map locals f =
  mkInScopeSetStm cont_map (funParams f ++ locals) (funBody f)

mkInScopeSetStm cont_map locals stm =
  case stm
  of LetLCPS params rhs label body -> continue params body
     LetrecLCPS defs group_id body ->
       let definienda = map definiendum $ groupMembers defs

           -- Find the continuations that will be moved to this group
           continuations_here =
             nub $ catMaybes [Map.lookup v cont_map | v <- definienda]
           
           -- Add letrec-bound functions to the in-scope set.
           -- Continuations are always added to the scope.
           -- (A nonrecursive let will be converted to a recursive one if
           -- necessary so that the scoping rules work).
           locals' = case defs
                     of NonRec _ -> continuations_here ++ locals
                        Rec _    -> continuations_here ++ definienda ++ locals

           -- Record these definitions
           local_defs = (fromIdent group_id, locals')

           -- Continue processing local functions and body
           defs_result =
             concat [mkInScopeSetFun cont_map locals' (definiens d)
                    | d <- groupMembers defs]
           
           body_result = continue (continuations_here ++ definienda) body
       in local_defs : defs_result ++ body_result

     SwitchLCPS cond alts ->
       concat [continue [] s | (_, s) <- alts]

     ReturnLCPS atom -> []

     ThrowLCPS exc -> []
  where
    continue new_locals stm =
      mkInScopeSetStm cont_map (new_locals ++ locals) stm

-------------------------------------------------------------------------------

-- | Convert all continuations to local functions in a function definition.
--
--   This allows closure conversion to hoist and insert captured variable
--   parameters.
reifyContinuations :: IdentSupply Var -> LocalCPS.RConts -> ContMap -> LFunDef
                   -> IO FunDef
reifyContinuations var_ids rconts cont_map ann_def = do
  (cont_funs, def1) <- extractContinuations var_ids rconts ann_def

  return $ insertContinuations cont_map cont_funs def1

data ECContext =
  ECContext
  { ecRConts     :: LocalCPS.RConts
  , ecCurrentFun :: Var
  , ecRType      :: [ValueType]
  , ecIdentSupply :: {-# UNPACK #-}!(IdentSupply Var)
  }

-- | Extract continuations from the code.
--
--   A function definition is created for each continuation, and the
--   original continuation is removed from the code.  Tail-calls to
--   continuations are inserted.
--
--   The first return value in the returned tuple is a mapping from
--   each continuation to its syntactically first caller.  Because the
--   continuation is a continuation, the first caller dominates all
--   other callers.
--
--   The other return values are the continuation functions, and the
--   modified top-level function definition.
extractContinuations :: IdentSupply Var -> LocalCPS.RConts -> LFunDef
                     -> IO ([FunDef], FunDef)
extractContinuations supply rconts def = do
  let no_fun = internalError "extractContinuations: No function" 
      no_rettype = internalError "extractContinuations: No return type"
  (def', (), cont_funs) <-
    runRWST (extractContinuationsDef def) (ECContext rconts no_fun no_rettype supply) ()
  return (cont_funs, def')

extractContinuationsDef (Def v f) =
  local (\ctx -> ctx {ecRType = funReturnTypes f, ecCurrentFun = v}) $ do
    body' <- extractContinuationsStm (funBody f)
    let f' = mkFun (funConvention f) (funInlineRequest f) (funFrameSize f)
             (funParams f) (funReturnTypes f) body'
    return $ Def v f'

extractContinuationsStm stm =
  case stm
  of LetLCPS params rhs label body -> do
       rconts <- asks ecRConts
       let is_cont = LocalCPS.RCont label `elem` IntMap.elems rconts
       if is_cont
         then do
           -- Create continuation function
           rtype <- asks ecRType
           let fun = mkFun ClosureCall False 0 params rtype body
           cont_def <- extractContinuationsDef (Def label fun)
           tell [cont_def]

           -- The RHS becomes a tail expression
           return $ ReturnE rhs
         else do
           body' <- extractContinuationsStm body
           return $ LetE params rhs body'

     LetrecLCPS defs group_id body -> do
       defs' <- mapM extractContinuationsDef defs
       body' <- extractContinuationsStm body
       return $ LetrecE defs' body'
     
     SwitchLCPS cond alts -> do
       alts' <- mapM do_alt alts
       return $ SwitchE cond alts'
     
     ReturnLCPS atom -> do
       context <- ask
       let rconts = ecRConts context
           current_fun = ecCurrentFun context
           rtype = ecRType context
       let current_cont =
             case LocalCPS.lookupCont current_fun rconts
             of Just c -> c
                Nothing -> internalError $ "No continuation for " ++ show current_fun
       case LocalCPS.needsContinuationCall rconts current_cont atom of
         Just current_cont -> do
           -- This function has a continuation call.
           -- Bind the atom's results to temporary variables, and
           -- create a continuation call.
           tmpvars <- mapM newAnonymousVar_ec rtype
           return $ LetE tmpvars atom $
             ReturnE (CallA ClosureCall (VarV current_cont) (map VarV tmpvars))
         Nothing ->
           return $ ReturnE atom
     ThrowLCPS exc ->
       return $ ThrowE exc
  where
    do_alt (tag, s) = liftM ((,) tag) $ extractContinuationsStm s
    
    newAnonymousVar_ec t = do
      id_supply <- asks ecIdentSupply
      lift $ runFreshVarM id_supply $ newAnonymousVar t

-- | Insert the continuation function definitions into the code.
insertContinuations :: Map.Map Var Var
                       -- ^ Map from function to its continuation
                    -> [FunDef] -- ^ Continuation function definitions
                    -> FunDef   -- ^ Top-level function definition
                    -> FunDef
insertContinuations cont_map cont_funs def =
  runReader (insertContinuationsDef def) (cont_map, cont_funs)

insertContinuationsDef (Def v f) = do
  body <- insertContinuationsStm $ funBody f
  return $ Def v (f {funBody = body})

insertContinuationsStm stm =
  case stm
  of LetE params rhs body ->
       LetE params rhs <$> insertContinuationsStm body
     LetrecE defs body -> do
       -- Add continuations to this definition group
       (cont_map, cont_funs) <- ask
       let definienda = map definiendum $ groupMembers defs
           continuations_here = nub $ mapMaybe lookup_cont definienda
             where
               lookup_cont v = Map.lookup v cont_map
           continuation_defs = map lookup_def continuations_here
             where
               lookup_def v =
                 case find ((v ==) . definiendum) cont_funs 
                 of Just d -> d
                    Nothing -> internalError "insertContinuations: Not found"

           defs' =
             if null continuation_defs
             then defs
             else Rec (continuation_defs ++ groupMembers defs)
         in LetrecE <$>
            mapM insertContinuationsDef defs' <*>
            insertContinuationsStm body
     SwitchE cond alts ->
       SwitchE cond <$> mapM do_alt alts
     ReturnE _ -> pure stm
     ThrowE _ -> pure stm
     where
       do_alt (tag, s) = do
         s' <- insertContinuationsStm s
         return (tag, s')

-------------------------------------------------------------------------------

-- A list of groups and the functions they contain
type GroupMembership = [(GroupID, [Var])]

stmGroupTable :: LocalCPS.RConts -> LStm -> GroupMembership
stmGroupTable rconts stm =
  case stm
  of LetLCPS _ _ label body
       | LocalCPS.RCont label `elem` IntMap.elems rconts ->
           -- This is a continuation function
           (ContID label, [label]) : stmGroupTable rconts body
       | otherwise ->
           -- This is an ordinary let expression
           stmGroupTable rconts body
     LetrecLCPS defs gid body ->
       (GroupID gid, map definiendum $ groupMembers defs) :
       concatMap (stmGroupTable rconts . funBody . definiens) (groupMembers defs) ++
       stmGroupTable rconts body
     SwitchLCPS _ alts ->
       concat [stmGroupTable rconts s | (_, s) <- alts]
     ReturnLCPS _ -> []
     ThrowLCPS _ -> []

createGroupTables :: LocalCPS.RConts -> LFunDef -> (Var -> GroupID, GroupID -> [Var])
createGroupTables rconts fun_def =
  let group_membership = stmGroupTable rconts $ funBody $ definiens fun_def
      fun_group = Map.fromList [(v, g) | (g, vs) <- group_membership, v <- vs]
      get_group_members gid =
        case lookup gid group_membership
        of Just vs -> vs
           Nothing -> internalError "createGroupTables: lookup failed"
      get_fun_group v =
        case Map.lookup v fun_group
        of Just gid -> gid
           Nothing  -> internalError "createGroupTables: lookup failed"
  in (get_fun_group, get_group_members)

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
  let rconts = LocalCPS.identifyLocalContinuations ann_def
      conts_set = Set.fromList [v | LocalCPS.RCont v <- IntMap.elems rconts]

  -- Compute lookup tables to associate functions to groups and vice versa
  let (fun_to_group, group_to_fun) =
        createGroupTables rconts ann_def

  -- Find the first caller of each continuation
  let (cont_map, caller_map) =
        mkContMap rconts ann_def

  -- Find the set of variables that will be in scope at each definition group
  -- after closure converison
  let locals_in_scope =
        mkInScopeSet cont_map ann_def 
  
  when debug $ do
    putStrLn "Computing hoisting and variable capture for closure conversion"
    print $ pprLFunDef ann_def
    print $ text "Continuations:" <+>
      fsep [parens $ int f <+> text "|->" <+> text (show k)
           | (f, k) <- IntMap.toList rconts]
    print $ text "Locals:" <+> vcat [int g <+> text "|->" <+> text (show l) 
                                    | (g, l) <- IntMap.toList locals_in_scope]

  -- Compute hoisting
  hoisted_groups <- findHoistedGroups ann_def rconts

  -- Compute free variables
  captures <- findCapturedVariables rconts global_vars conts_set ann_def
  
  -- Debugging
  when debug $ do
    putStrLn $ "Hoisted set: " ++ show hoisted_groups
    putStrLn "Captured variables:"
    print captures

  -- Reify continuations and remove annotations
  cont_def <- reifyContinuations var_ids rconts cont_map ann_def

  -- Construct closure conversion info
  let lookup_function f =
        let grp = fun_to_group f
        in FunAnalysisResults
           { funHoisted  = grp `Set.member` hoisted_groups
           , funGroup    = grp
           , funCaptured = fromMaybe Set.empty $ Map.lookup f captures
           }
  cc_info <- runFreshVarM var_ids $ stmCCInfo lookup_function locals_in_scope (funBody $ definiens $ cont_def)
  
  when debug $ do
    putStrLn "Results of analysis:"
    print $ vcat[hang (pprVar v) 2 (pprCCInfo cc_info) | (v, cc_info) <- cc_info]

  return (cont_def, Map.fromList cc_info)
