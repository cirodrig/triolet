{-| Closure conversion.

This pass converts all functions into primitive (non-closure-based)
functions.  Lambda values and letrec expressions are eliminated.  This pass
runs before reference counting is inserted.

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
import LowLevel.ClosureCode
import Globals

-------------------------------------------------------------------------------
-- Closure conversion and hoisting

-- | Perform closure conversion on an atom.
ccAtom :: [PrimType]         -- ^ atom's return types
          -> Atom               -- ^ atom to convert
          -> GenM Atom
ccAtom returns atom =
  case atom
  of -- Generate a direct call if possible
     CallA ClosureCall (VarV v) vs -> genVarCall returns v vs

     -- General case
     CallA conv v vs -> do
       case conv of
         ClosureCall -> genIndirectCall returns v vs
         -- Primitive calls are always direct
         PrimCall    -> return $ primCallA v vs

     -- Other atoms are unchanged
     _ -> return atom

ccStm :: [PrimType] -> Stm -> GenM Stm
ccStm returns stm =
  case stm
  of LetE params rhs body -> do
       ccAtom (map varPrimType params) rhs >>= bindAtom params
       ccStm returns body
     LetrecE defs body ->
       ccLocalGroup defs $ ccStm returns body
     SwitchE val alts -> do
       alts' <- lift $ forM alts $ \(lit, alt_stm) -> do
         stm' <- execBuild (map PrimType returns) $ ccStm returns alt_stm
         return (lit, stm')
       return $ SwitchE val alts'
     ReturnE atom -> ReturnE `liftM` ccAtom returns atom

-- | Perform closure conversion on the body of a function.  Get the
--   transformed function body.
ccFunBody :: Fun -> CC Stm
ccFunBody fun =
  execBuild (map PrimType return_prim_types) $ ccStm return_prim_types $ funBody fun
  where
    return_prim_types = map valueToPrimType $ funReturnTypes fun

-- | Given a function that is to be closure converted or a procedure that is to
--   be moved to the top level, return the closure-converted function.
--
--   Only the function's direct entry is constructed.  Other parts of the
--   converted function must be built elsewhere.
ccHoistedFun :: [Var] -> Fun -> CC Fun
ccHoistedFun free_vars fun 
  | isPrimFun fun && not (null free_vars) =
      let free_variables = intercalate ", " $ map show free_vars
      in error $ "Procedure has free variables: " ++ free_variables
                                            
  | otherwise = do
      body <- ccFunBody fun

      -- Add the free variables as extra parameters
      let new_params = free_vars ++ funParams fun
          new_fun = mkFun PrimCall (funInlineRequest fun) (funFrameSize fun)
                    new_params (funReturnTypes fun) body

      return new_fun

-- | Perform closure conversion on a function that won't be hoisted.
--   The function body is closure-converted.  A primitive-call function 
--   is returned.
ccUnhoistedFun :: Fun -> CC Fun
ccUnhoistedFun fun = do
  body <- ccFunBody fun
  return $ primFun (funParams fun) (funReturnTypes fun) body

-- | Perform closure conversion on a letrec-bound function group.
--
--   Either all functions in the group are hoisted, or all functions are
--   un-hoisted. Hoisted functions become closures.
--   Un-hoisted functions become a new 'letrec'.
ccLocalGroup :: Group FunDef -> GenM a -> GenM a
ccLocalGroup defs do_body = do
  m_hoist_info <-
    lift $ lookupHoistInfo $ definiendum $ head $ groupMembers defs

  case m_hoist_info of
    Just (Just c) -> ccHoistedGroup c defs do_body
    Just Nothing -> ccUnhoistedGroup defs do_body
    Nothing -> internalError "ccLocalGroup: No hoisting information"

mapDef f (Def v fun) = do
  f' <- f fun
  return (Def v f')

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

closureConvertTopLevelFunction :: Set.Set Var -> FunDef -> CC Fun
closureConvertTopLevelFunction globals def@(Def v f) = do
  hoist_vars <- runIOCC $ \id_supply ->
    findFunctionsToHoist id_supply globals def
  withHoistInfo hoist_vars $ ccHoistedFun [] f

closureConvertTopLevelFunctions :: IdentSupply Var
                                -> [Var]
                                -> [Import]
                                -> [Group GlobalDef]
                                -> IO [GlobalDef]
closureConvertTopLevelFunctions var_ids globals imports defs =
  runCC var_ids globals $ withImports imports $ cc_globals defs
  where
    global_set = Set.fromList globals

    cc_globals (group : groups) =
      withGlobalFunctions group (closureConvertTopLevelFunction global_set) $
      cc_globals groups
    cc_globals [] = return ()

-- | Perform closure conversion on a data value.
scanDataValue :: Val -> Val
scanDataValue value = 
  case value
  of LamV {} -> internalError "scanDataValue"
     RecV r vs -> RecV r $ map scanDataValue vs
     _       -> value

-- | Perform closure conversion on a data definition.
--
-- Currently we don't allow lambda functions inside static data structures,
-- so this is just a validity check.
convertDataDef :: DataDef -> DataDef
convertDataDef (Def v (StaticData record vals)) =
  let vals' = map scanDataValue vals
  in Def v (StaticData record vals')

convertDataDefs = map convertDataDef

-- | Perform closure conversion.
--
--   FIXME: We must globally rename functions to avoid name collisions!
closureConvert :: Module -> IO Module
closureConvert mod =
  withTheLLVarIdentSupply $ \var_ids -> do
    -- Perform closure conversion
    let imports = moduleImports mod
        global_vars = [globalDefiniendum d
                      | g <- moduleGlobals mod, d <- groupMembers g] ++
                      map importVar imports
    defs' <-
      closureConvertTopLevelFunctions var_ids global_vars imports $
      moduleGlobals mod
        
    -- Rename variables so that variable names are unique
    -- within a top-level function
    renamed_defs <- runFreshVarM var_ids $ mapM rename_global_fun defs'
    return $ mod {moduleGlobals = [Rec renamed_defs]}
  where
    rename_global_fun (GlobalFunDef fdef) =
      liftM GlobalFunDef $ renameInFunDef RenameParameters fdef
    rename_global_fun ddef@(GlobalDataDef _) = return ddef
