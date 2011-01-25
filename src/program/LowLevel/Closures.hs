{-| Closure conversion.

This pass converts all functions into primitive (non-closure-based)
functions.  Lambda values and letrec expressions are eliminated.  This pass
runs before reference counting is inserted.

Data structures should be flattened before running closure conversion.
CSE and DCE must be performed (at least once) before running closure
conversion, to fix up frame pointer references.

'RecV' values are not allowed.  'PackA' and 'UnpackA' atoms are not allowed.
Frame pointers may only be accessed in top-level functions.
-}

{-# LANGUAGE FlexibleInstances #-}
module LowLevel.Closures(closureConvert)
where

import Control.Monad
import Control.Monad.Trans
import Data.List
import Data.Maybe
import Data.Monoid
import qualified Data.Set as Set
import Debug.Trace

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

-- | Perform closure conversion on a value.
-- 
ccValue :: Val -> CC (GenM Val)
ccValue value =
  case value
  of VarV v  -> do mention v
                   return (return value)
     LamV f  -> ccLambdaFunction f
     RecV {} -> internalError "ccValue"
     _       -> return (return value)

ccValues xs = mapM ccValue xs

-- | Perform closure conversion on an atom.
ccAtom :: [PrimType]         -- ^ atom's return types
          -> Atom               -- ^ atom to convert
          -> CC (GenM Atom)
ccAtom returns atom =
  case atom
  of ValA vs -> do
       vs' <- ccValues vs
       return $ ValA `liftM` sequence vs'

     -- Generate a direct call if possible
     CallA ClosureCall (VarV v) vs -> 
       genVarCall returns v =<< ccValues vs

     -- General case
     CallA conv v vs -> do
       v' <- ccValue v
       vs' <- ccValues vs
       case conv of
         ClosureCall -> genIndirectCall returns v' vs'
         -- Primitive calls are always direct
         PrimCall    -> return (liftM2 primCallA v' (sequence vs'))

     PrimA prim vs -> do
       vs' <- ccValues vs
       return $ PrimA prim `liftM` sequence vs'

     UnpackA record (VarV v) -> do
       mention v
       return (return $ UnpackA record (VarV v))

     PackA {} -> internalError "ccAtom: unexpected 'pack'"
     UnpackA {} -> internalError "ccAtom: unexpected 'unpack'"

ccStm :: [PrimType] -> Stm -> CC (GenM Stm)
ccStm returns stm =
  case stm
  of LetE params rhs body -> do
       mk_rhs <- ccAtom (map varPrimType params) rhs
       mk_body <- withParameters params $ ccStm returns body
       return $ do rhs <- mk_rhs
                   bindAtom params rhs 
                   mk_body
     LetrecE defs body ->
       ccLocalGroup defs $ \mk_defs -> do
         body' <- ccStm returns body
         return (mk_defs >> body')
     SwitchE val alts -> do
       val' <- ccValue val
       alts' <- mapM cc_alt alts
       return (rebuild_switch val' alts')
     ReturnE atom -> do
       mk_atom <- ccAtom returns atom
       return (fmap ReturnE mk_atom)
  where
    cc_alt (lit, stm) = do
      stm' <- ccStm returns stm
      return (lit, stm')

    rebuild_switch mk_val mk_alts = do
      val' <- mk_val
      alts' <- forM mk_alts $ \(lit, mk_stm) -> do
        stm <- lift (execBuild (map PrimType returns) mk_stm)
        return (lit, stm)
      return (SwitchE val' alts')

-- | Perform closure conversion on a lambda function.  Return the
-- closure-converted function.  New top-level functions and data are produced
-- as a side effect.
ccLambdaFunction :: Fun -> CC (GenM Val)
ccLambdaFunction fun = do
  (direct_fun, captured_vars) <- ccHoistedFun fun
  emitLambdaClosure (funType fun) False direct_fun captured_vars

-- | Perform closure conversion on the body of a function.
ccFunBody :: Fun -> CC (GenM Stm)
ccFunBody fun =
  withParameters (funParams fun) $ ccStm return_prim_types (funBody fun)
  where
    return_prim_types = map valueToPrimType $ funReturnTypes fun

-- | Perform closure conversion on the body of a function and return the
--   closure-converted function.  Only the direct entry is constructed; if
--   a function closure is desired, the other parts must be built elsewhere.
--
--   The direct entry point function and a list of captured variables
--   are returned.
ccHoistedFun :: Fun -> CC (Fun, [Var])
ccHoistedFun fun = do
  -- Do closure conversion in the function body, and get the set of variables
  -- mentioned in the function body
  (mk_body, free_vars) <- listenFreeVars $ ccFunBody fun
  body <- execBuild (funReturnTypes fun) mk_body

  -- Add the free variables as extra parameters
  let free_var_list = Set.toList free_vars
      new_params = free_var_list ++ funParams fun
      new_fun = mkFun PrimCall (funInlineRequest fun) (funFrameSize fun) new_params (funReturnTypes fun) body
      
  -- If the input function was a primitive-call function, then there is no
  -- way to deal with free variables
  when (isPrimFun fun && not (null free_var_list)) $
    error "Procedure has free variables"

  return (new_fun, free_var_list)

-- | Perform closure conversion on a function that won't be hoisted.
--   The function body is closure-converted.  A primitive-call function 
--   is returned.
ccUnhoistedFun :: Fun -> CC Fun
ccUnhoistedFun fun = do
  body <- execBuild (funReturnTypes fun) =<< ccFunBody fun
  return $ primFun (funParams fun) (funReturnTypes fun) body

-- | Perform closure conversion on a letrec-bound function group.
--
--   Functions in the group that are hoisted become closures.
--   Functions in the group that are un-hoisted become a new 'letrec'.
--
--   Because of the way functions are selected for hoisting, hoisted functions 
--   never reference un-hoisted functions in the same group.  Therefore
--   hoisted function definitions appear first in the transformed code,
--   followed by un-hoisted functions.
ccLocalGroup :: [FunDef] -> (GenM () -> CC (GenM a)) -> CC (GenM a) 
ccLocalGroup defs do_body = withParameters (map definiendum defs) $ do
  -- Determine which functions are hoisted
  hoisted <- mapM (isHoisted . definiendum) defs
  let (h_defs, l_defs) = partition_by hoisted defs

  generate_hoisted_functions h_defs $ \hoisted_code -> 
    withUnhoistedVariables (map definiendum l_defs) $ do
      unhoisted_code <- generate_unhoisted l_defs
      do_body (hoisted_code >> emitLetrec unhoisted_code)
  where
    generate_hoisted_functions :: [FunDef]
                               -> (GenM () -> CC a)
                               -> CC a
    generate_hoisted_functions [] k = k (return ())
    generate_hoisted_functions h_defs k =
      withLocalFunctions h_defs (mapM (ccHoistedFun . definiens) h_defs) k

    generate_unhoisted l_defs = mapM gen l_defs
      where
        gen (Def v f) = do
          f' <- ccUnhoistedFun f
          return $ Def v f'

    -- Partition list 2 by the boolean value in list 1
    partition_by flags values = par id id flags values
      where
        par hd_l hd_r (True:flags)  (x:xs) = par (hd_l . (x:)) hd_r flags xs
        par hd_l hd_r (False:flags) (x:xs) = par hd_l (hd_r . (x:)) flags xs
        par hd_l hd_r []            _      = (hd_l [], hd_r [])

closureConvertTopLevelFunction :: FunDef -> CC Fun
closureConvertTopLevelFunction def@(Def v f) =
  let hoist_vars = findFunctionsToHoist def
  in withHoistedVariables hoist_vars $ do
    (f', captured) <- ccHoistedFun f
    unless (null captured) $ error "Global procedure captures variables"
    return f'

closureConvertTopLevelFunctions :: IdentSupply Var
                                -> [Var]
                                -> [Import]
                                -> [FunDef]
                                -> IO ([FunDef], [DataDef])
closureConvertTopLevelFunctions var_ids globals imports defs =
  runCC var_ids globals $ do
    withGlobalFunctions imports defs (mapM closureConvertTopLevelFunction defs) (return ())

-- | Perform closure conversion on a data value.
scanDataValue :: Val -> Val
scanDataValue value = 
  case value
  of LamV {} -> internalError "scanDataValue"
     RecV {} -> internalError "scanDataValue"
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

{-
-------------------------------------------------------------------------------

scanBlock :: Block -> [PrimType] -> CC Block
scanBlock (Block stms atom) returns = withMany scanStm stms $ \stms' -> do
  atom' <- scanAtom atom returns
  execBuild $ sequence stms' >> atom'

scanStm :: Stm -> (GenM () -> CC a) -> CC a
scanStm statement k =
  case statement
  of LetE vs atom -> do
       atom' <- scanAtom atom (map varPrimType vs)
       withParameters vs $ k $ bindAtom vs =<< atom'
     LetrecE defs -> 
       withDefGroup defs k

scanAtom :: Atom -> [PrimType] -> CC (GenM Atom)
scanAtom atom returns =
  case atom
  of ValA vs -> do
       vs' <- mapM scanValue vs
       return $ ValA `liftM` sequence vs'

     -- Generate a direct call if possible
     CallA (VarV v) vs -> genVarCall returns v =<< mapM scanValue vs

     -- General case, indirect call
     CallA v vs -> do
       v' <- scanValue v
       vs' <- mapM scanValue vs
       genIndirectCall returns v' vs'
     PrimCallA v vs -> do
       v' <- scanValue v
       vs' <- mapM scanValue vs
       return $ PrimCallA `liftM` v' `ap` sequence vs'
     PrimA prim vs -> do
       vs' <- mapM scanValue vs
       return $ PrimA prim `liftM` sequence vs'
     SwitchA scr alts -> do
       scr' <- scanValue scr
       alts' <- mapM scan_alt alts
       return $ SwitchA `liftM` scr' `ap` return alts'
     PackA {} -> internalError "scanAtom: unexpected 'pack'"
     UnpackA {} -> internalError "scanAtom: unexpected 'unpack'"
  where
    scan_alt (lit, block) = do
      block' <- scanBlock block returns
      return (lit, block')

-- | Perform closure conversion on a value.
-- 
scanValue :: Val -> CC (GenM Val)
scanValue value =
  case value
  of VarV v  -> do mention v
                   return (return value)
     LamV f  -> scanLambdaFunction f
     RecV {} -> internalError "scanValue"
     _       -> return (return value)

withDefGroup :: [FunDef] -> (GenM () -> CC a) -> CC a
withDefGroup defs k =
  -- Functions are bound here
  withParameters (map funDefiniendum defs) $
  -- Scan functions and add them to environment
  withLocalFunctions defs (mapM (scanFun . funDefiniens) defs) k

-- | Perform closure conversion on a lambda function; generate entry 
--   points and data structures for it.  As a side effect, global objects
--   are created and statements are emitted in the current block.
scanLambdaFunction :: Fun -> CC (GenM Val)
scanLambdaFunction lambda_fun = do
  -- Closure-convert the function
  (direct_fun, captured_vars) <- scanFun lambda_fun
  emitLambdaClosure (funType lambda_fun) direct_fun captured_vars

-- | Perform closure conversion on a function.  The closure-converted
-- function is returned, along with a list of the captured variables.
--
-- If the function is a primitive call function, it must not have free
-- variables.
--
-- First, closure conversion is performed on the function body.
-- Then the function is converted to one with no free variables that takes
-- an extra argument for each free variable in the original function.
scanFun :: Fun -> CC (Fun, [Var])
scanFun fun = do
  -- Do closure conversion in the function body, and get the set of variables
  -- mentioned in the function body
  let return_prim_types = map valueToPrimType $ funReturnTypes fun
        
  (body', free_vars) <-
    listenFreeVars $
    withParameters (funParams fun) $
    scanBlock (funBody fun) return_prim_types

  -- Add the free variables as extra parameters
  let free_var_list = Set.toList free_vars
      new_params = free_var_list ++ funParams fun
      new_fun = primFun new_params (funReturnTypes fun) body'
      
  -- If the input function was a primitive-call function, then there is no
  -- way to deal with free variables
  when (isPrimFun fun && not (null free_var_list)) $
    error "Procedure has free variables"


  return (new_fun, free_var_list)

-- | Perform closure conversion on a data value.
scanDataValue :: Val -> CC Val
scanDataValue value = 
  case value
  of LamV {} -> internalError "scanDataValue"
     RecV {} -> internalError "scanDataValue"
     _       -> return value

-- | Perform closure conversion on a data definition.
--
-- Currently we don't allow lambda functions inside static data structures,
-- so this is just a validity check.
convertDataDef :: DataDef -> CC ()
convertDataDef (DataDef v record vals) = do 
  vals' <- mapM scanDataValue vals
  writeData $ DataDef v record vals'

-- | Perform closure conversion on the set of global functions.  Unlike
-- local functions, closures are not needed because it's only possible to 
-- reference global functions.  A dummy closure object is created for
-- compatibility with the way functions are called.
--
-- Global data definitions aren't allowed to contain lambda functions, so we
-- can ignore them.
scanTopLevel :: [FunDef] -> [DataDef] -> CC ()
scanTopLevel fun_defs data_defs =
  withGlobalFunctions fun_defs
  (mapM scan_fun fun_defs)
  (mapM_ convertDataDef data_defs)
  where
    fun_variables = map funDefiniendum fun_defs
    data_variables = map dataDefiniendum data_defs

    -- Scan a function and create the direct entry point.  There must be no
    -- captured variables.
    scan_fun fdef = do
      (f, captured) <- scanFun $ funDefiniens fdef
      check_captured_vars captured
      return f

    -- If something other than a top-level variable is captured, it means
    -- there's a compiler bug
    check_captured_vars captured_vars =
      unless (all (`Set.member` valid_vars) captured_vars) $
      traceShow (Set.fromList captured_vars Set.\\ valid_vars) $ 
      internalError "scanTopLevel: Impossible variable capture"

    valid_vars = Set.fromList $ fun_variables ++ data_variables ++ allBuiltins
-}

-- | Perform closure conversion.
--
-- FIXME: We must globally rename variables before closure conversion
-- to avoid name collisions!
closureConvert :: Module -> IO Module
closureConvert mod =
  withTheLLVarIdentSupply $ \var_ids -> do

    -- Perform closure conversion
    let (fun_defs, data_defs) = partitionGlobalDefs $ moduleGlobals mod
        imports = moduleImports mod
        global_vars = map globalDefiniendum (moduleGlobals mod) ++
                      map importVar imports
    (fun_defs', fun_data_defs') <-
      closureConvertTopLevelFunctions var_ids global_vars imports fun_defs
    let data_defs' = convertDataDefs data_defs
        
    -- Rename variables so that variable names are unique
    -- within a top-level function
    renamed_fun_defs <-
      runFreshVarM var_ids $ mapM (renameInFunDef RenameParameters) fun_defs'
    
    let new_global_defs = map GlobalFunDef renamed_fun_defs ++
                          map GlobalDataDef (data_defs' ++ fun_data_defs')
    
    return $ mod {moduleGlobals = new_global_defs}

