{-| Closure conversion.

This pass converts all functions into a form that can be represented directly
with function calls and jumps.  Letrec expressions are eliminated.

Data structures should be flattened before running closure conversion.
CSE and DCE must be performed (at least once) before running closure
conversion, to fix up frame pointer references.

'PackA' atoms are not allowed.
Frame pointers may only be accessed in top-level functions.
-}

{-# LANGUAGE FlexibleInstances #-}
module LowLevel.Closures(closureConvert)
where

import Prelude hiding(mapM)
import Control.Monad hiding(forM, mapM)
import Control.Monad.Trans
import Data.List
import Data.Maybe
import Data.Monoid
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Traversable
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.MonadLogic
import Common.Identifier
import LowLevel.Builtins
import LowLevel.FreshVar
import LowLevel.Print
import LowLevel.Rename
import LowLevel.Syntax
import LowLevel.CodeTypes
import LowLevel.Build
import LowLevel.ClosureSelect
import LowLevel.Closure.CCInfo
import LowLevel.Closure.Code
import Globals

-------------------------------------------------------------------------------
-- Closure conversion and hoisting

-- | Perform closure conversion on a value
ccVal :: Val -> GenM Val
ccVal val =
  case val
  of VarV v -> genVarRef v
     _ -> return val

ccVals :: [Val] -> GenM [Val]
ccVals = mapM ccVal

-- | Perform closure conversion on an atom.
ccAtom :: [PrimType]         -- ^ atom's return types
          -> Atom               -- ^ atom to convert
          -> GenM Atom
ccAtom returns atom =
  case atom
  of -- Generate a direct call if possible
     CallA ClosureCall (VarV v) vs ->
       genClosureCall returns v =<< ccVals vs
     
     CallA PrimCall (VarV v) vs ->
       genPrimCall v =<< ccVals vs

     CallA JoinCall (VarV v) vs ->
       genJoinCall v =<< ccVals vs

     -- General case
     CallA conv v vs -> do
       v' <- ccVal v
       vs' <- ccVals vs
       case conv of
         ClosureCall -> genIndirectCall returns v' vs'
         -- Primitive calls are always direct
         PrimCall    -> return $ primCallA v' vs'

     -- Other atoms aren't transformed, except for expanding variable references
     ValA vs -> ValA `liftM` ccVals vs
     PrimA p vs -> PrimA p `liftM` ccVals vs
     PackA r vs -> PackA r `liftM` ccVals vs
     UnpackA r v -> UnpackA r `liftM` ccVal v

ccStm :: [PrimType] -> Stm -> GenM Stm
ccStm returns stm =
  case stm
  of LetE params rhs body -> do
       ccAtom (map (valueToPrimType . varType) params) rhs >>= bindAtom params
       ccStm returns body
     LetrecE defs body ->
       ccLocalGroup defs $ ccStm returns body
     SwitchE val alts -> do
       val' <- ccVal val
       alts' <- lift $ forM alts $ \(lit, alt_stm) -> do
         stm' <- execBuild (map PrimType returns) $ ccStm returns alt_stm
         return (lit, stm')
       return $ SwitchE val' alts'
     ReturnE atom -> ReturnE `liftM` ccAtom returns atom
     ThrowE val -> ThrowE `liftM` ccVal val

-- | Perform closure conversion on the body of a function.  Get the
--   transformed function body.
ccFunBody :: Fun -> CC Stm
ccFunBody fun =
  execBuild (map PrimType return_prim_types) $
  ccStm return_prim_types $ funBody fun
  where
    return_prim_types = map valueToPrimType $ funReturnTypes fun

-- | Perform closure conversion on a letrec-bound function group.
--
--   Hoisted functions become closures.
--   Un-hoisted functions become a new 'letrec'.
ccLocalGroup :: Group FunDef -> GenM a -> GenM a
ccLocalGroup defs do_body = do
  cc_infos <- lift $ mapM get_cc_info local_defs
  
  -- Create global data for these local functions
  lift $ mapM_ emitClosureGlobalData cc_infos
  
  -- Allocate closures
  closure_data <- allocateLocalClosures (zip local_names cc_infos)

  -- For each hoisted function, create a global function definition;
  -- For each unhoisted function, create a local function definition.
  let (hoisted, unhoisted) =
        partition (ccIsHoisted . snd) $ zip local_defs cc_infos
  lift $ mapM_ ccHoistedFun hoisted
  new_defs <- lift $ mapM ccUnhoistedFun unhoisted
  
  -- Create a statement to define the unhoisted functions
  when (not $ null new_defs) $ emitLetrec (Rec new_defs)
  
  -- Now that all local functions are defined, populate closures
  populateLocalClosures closure_data

  do_body
  where
    local_defs = groupMembers defs
    local_names = map definiendum local_defs

    get_cc_info :: FunDef -> CC CCInfo
    get_cc_info def = do
      m_inf <- lookupCCInfo $ definiendum def
      case m_inf of
        Just inf -> return inf
        Nothing  -> internalError "ccLocalGroup: Missing closure conversion info"

-- | Given a function that is to be closure converted, closure-convert the 
--   function body and create the direct entry point.
--  
--   Other parts of the converted function must be built elsewhere.
ccHoistedFun :: (FunDef, CCInfo) -> CC ()
ccHoistedFun (def, ccinfo) = do
      let fun = definiens def
      body <- ccFunBody fun

      -- Add the captured variables as extra parameters
      let new_params = ccCaptured ccinfo ++ funParams fun
          new_fun = mkFun PrimCall (funInlineRequest fun) (funFrameSize fun)
                    Nothing new_params (funReturnTypes fun) body

      -- Emit the function
      writeFun (Def (directEntry $ ccEntryPoints ccinfo) new_fun)

-- | Perform closure conversion on a function that won't be hoisted.
--   The function body is closure-converted.  A primitive-call function 
--   is returned.
ccUnhoistedFun :: (FunDef, CCInfo) -> CC FunDef
ccUnhoistedFun (def, ccinfo) = do
  let fun = definiens def
  body <- ccFunBody fun
  -- Call-captured variables become additional function parameters
  let fun' = joinFun (ccCallCaptured ccinfo ++ funParams fun)
             (funReturnTypes fun) body
      def' = Def (ccJumpTarget ccinfo) fun'
  return def'

mapDef f (Def v fun) = do
  f' <- f fun
  return (Def v f')

-- | Perform closure conversion in the body of a global function or procedure
--
--   Generate the converted procedure, or the direct entry point.
ccGlobalFun :: (FunDef, CCInfo) -> CC ()
ccGlobalFun (def, ccinfo)
  | not (null $ ccCaptured ccinfo) =
      internalError "ccGlobalFun: Global function captures variables"

  | ccIsGlobalClosure ccinfo = do
      let fun = definiens def
      body <- ccFunBody fun
      let new_fun = mkFun PrimCall (funInlineRequest fun) 
                    (funFrameSize fun) Nothing 
                    (funParams fun) (funReturnTypes fun) body
      writeFun (Def (directEntry $ ccEntryPoints ccinfo) new_fun)

  | ccIsGlobalPrim ccinfo = do
      let fun = definiens def
      body <- ccFunBody fun
      let new_fun = fun {funBody = body}
      writeFun (Def (definiendum def) new_fun)

  | otherwise =
      -- The function should be a global closure-call or prim-call function
      internalError "ccGlobalFun"

{-
ccHoistedGroup hoisted_group defs do_body =
  withLocalFunctions hoisted_group $ do
    funs <- lift $ mapM (ccHoistedFun captured . definiens) (groupMembers defs)
    body <- do_body
    return (funs, body)
  where
    captured = closureCapturedVariables $ snd $ head $ groupMembers hoisted_group

ccUnhoistedGroup defs do_body =
  liftT (withUnhoistedVariables (map definiendum $ groupMembers defs)) $ do
    emitLetrec =<< lift (mapM (mapDef ccUnhoistedFun) defs)
    do_body
-}

-- | State accumulated while closure-converting top-level functions.
data TopState =
  TopState
    (Set.Set Var)      -- Global variables in scope
    CCInfos            -- Closure conversion info for globals in scope

-- | Perform closure conversion on one top-level function.
--
--   The 
closureConvertTopLevelFunction :: IdentSupply Var
                               -> TopState
                               -> FunDef
                               -> CCInfo
                               -> IO [GlobalDef]
closureConvertTopLevelFunction var_supply (TopState globals cc_info) def inf = do
  -- Compute variable capture and hoisting information
  (def', local_cc_info) <- findFunctionsToHoist var_supply globals def
  let cc_info' = local_cc_info `mappend` cc_info

  -- Perform closure conversion
  ((), new_defs) <-
    runCC var_supply globals cc_info' $ do
      ccGlobalFun (def', inf)
      emitClosureGlobalData inf

  return new_defs

closureConvertTopLevelDef :: IdentSupply Var
                          -> TopState
                          -> GlobalDef
                          -> Maybe CCInfo
                          -> IO [GlobalDef]
closureConvertTopLevelDef var_supply state (GlobalFunDef fdef) (Just inf) =
  closureConvertTopLevelFunction var_supply state fdef inf
  
closureConvertTopLevelDef var_supply state (GlobalDataDef ddef) Nothing =
  return [GlobalDataDef $ convertDataDef ddef]

-- | Perform closure conversion on one top-level definition group.
closureConvertTopLevelGroup :: IdentSupply Var
                            -> TopState
                            -> Group GlobalDef
                            -> IO (TopState, Group GlobalDef)
closureConvertTopLevelGroup var_supply state defs =
  case defs
  of NonRec def -> do
       let TopState globals cc_info = state

       -- Update the environment
       (inf, output_state) <-
         runFreshVarM var_supply $ extend_global_state def state
       
       -- Closure-convert this function, using the original environment
       cc_defs <- closureConvertTopLevelDef var_supply state def inf
       return (output_state, Rec cc_defs)

     Rec defs -> do
       -- Update the environment from all definitions in the group
       (infs, output_state) <-
         runFreshVarM var_supply $ extend_global_state_many state defs

       -- Closure-convert these functions
       cc_defss <-
         zipWithM (closureConvertTopLevelDef var_supply output_state) defs infs

       return (output_state, Rec (concat cc_defss))
  where
    extend_global_state (GlobalFunDef def) (TopState globals cc_info) = do
      inf <- globalCCInfo def
      let globals' = Set.insert (definiendum def) globals
          cc_info' = Map.insert (definiendum def) inf cc_info
      return (Just inf, TopState globals' cc_info')

    extend_global_state (GlobalDataDef def) (TopState globals cc_info) = do
      let globals' = Set.insert (definiendum def) globals
      return (Nothing, TopState globals' cc_info)

    extend_global_state_many state (def:defs) = do
      (inf, state') <- extend_global_state def state
      (infs, state'') <- extend_global_state_many state' defs
      return (inf : infs, state'')
    
    extend_global_state_many state [] =
      return ([], state)
    
closureConvertTopLevel :: IdentSupply Var
                       -> [Var]
                       -> [Import]
                       -> [Group GlobalDef]
                       -> IO [Group GlobalDef]
closureConvertTopLevel var_ids globals imports defs = do
  -- Construct environment from the given imported variables and other
  -- global variables
  cc_info <- runFreshVarM var_ids $ importCCInfos imports
  let global_set = Set.fromList (globals ++ map importVar imports)
  let initial_state = TopState global_set cc_info
  
  -- Convert one definition group at a time
  cc_globals initial_state defs
  where
    cc_globals state (group : groups) = do
      (state', group') <-
        closureConvertTopLevelGroup var_ids state group
      groups' <- cc_globals state' groups
      return (group' : groups')
    
    cc_globals _ [] = return []

-- | Perform closure conversion on a data value.
scanDataValue :: Val -> Val
scanDataValue value = 
  case value
  of RecV r vs -> RecV r $ map scanDataValue vs
     _       -> value

-- | Perform closure conversion on a data definition.
--
-- Currently we don't allow lambda functions inside static data structures,
-- so this is just a validity check.
convertDataDef :: DataDef -> DataDef
convertDataDef (Def v (StaticData val)) =
  let val' = scanDataValue val
  in Def v (StaticData val')

convertDataDefs = map convertDataDef

-- | Replace an imported symbol with its closure-converted equivalent.
--
--   Imported functions are expanded into multiple imported symbols.
--   Imported function definitions are removed.
convertImport :: Import -> [Import]
convertImport (ImportClosureFun entry_points _) =
  importedClosureEntryPoints entry_points

convertImport x@(ImportPrimFun {}) = [x]
convertImport x@(ImportData {}) = [x]

-- | Perform closure conversion.
--
--   FIXME: We must globally rename functions to avoid name collisions!
closureConvert :: Module -> IO Module
closureConvert mod =
  withTheLLVarIdentSupply $ \var_ids -> do
    -- Perform closure conversion
    let imports = moduleImports mod
        globals = moduleGlobals mod
        global_vars = []
    defs' <- closureConvertTopLevel var_ids [] imports globals

    -- Expand imported functions into multiple imported entities
    let imports' = concatMap convertImport imports

    -- Rename variables so that variable names are unique
    -- within a top-level function
    let mod' = mod {moduleImports = imports', moduleGlobals = defs'}

    runFreshVarM var_ids $ renameModule RenameParameters emptyRenaming mod'
  where
    rename_global_fun (GlobalFunDef fdef) =
      liftM GlobalFunDef $ renameInFunDef RenameParameters fdef
    rename_global_fun ddef@(GlobalDataDef _) = return ddef
