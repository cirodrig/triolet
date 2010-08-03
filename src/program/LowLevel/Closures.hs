{-| Closure conversion.

This pass converts all functions into primitive (non-closure-based)
functions.  Lambda values and letrec expressions are eliminated.  This pass
runs before reference counting is inserted.

Data structures should be flattened before running closure conversion.
'RecV' values are not allowed.  'PackA' and 'UnpackA' atoms are not allowed.
-}

{-# LANGUAGE FlexibleInstances #-}
module LowLevel.Closures(closureConvert)
where

import Control.Monad
import Data.List
import Data.Maybe
import qualified Data.Set as Set
import Debug.Trace

import Gluon.Common.Error
import Gluon.Common.MonadLogic
import LowLevel.Builtins
import LowLevel.Print
import LowLevel.Syntax
import LowLevel.Types
import LowLevel.Build
import LowLevel.ClosureCode
import Globals

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

-- | Perform closure conversion on a data value.
scanDataValue :: Val -> CC Val
scanDataValue value = 
  case value
  of LamV {} -> internalError "scanDataValue"
     RecV {} -> internalError "scanDataValue"
     _       -> return value

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
-- First, closure conversion is performed on the function body.
-- Then the function is converted to one with no free variables that takes
-- an extra argument for each free variable in the original function.
scanFun :: Fun -> CC (Fun, [Var])
scanFun fun = do
  unless (isClosureFun fun) $
    internalError "scanFun: Given function has wrong calling convention"

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
  return (new_fun, free_var_list)

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

closureConvert :: Module -> IO Module
closureConvert (Module fun_defs data_defs) =
  withTheLLVarIdentSupply $ \var_ids -> do
    let global_vars = map funDefiniendum fun_defs ++
                      map dataDefiniendum data_defs ++
                      allBuiltins
    (fun_defs', data_defs') <- runCC var_ids global_vars $
                               scanTopLevel fun_defs data_defs
    return $ Module fun_defs' data_defs'
  

