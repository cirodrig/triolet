{-| Initialization of global variables.
--  This is in a separate module to eliminate dependences on the gluon-eval 
--  package when executing Template Haskell.
-}
module InitializeGlobals where

import Control.Monad
import Control.Concurrent.MVar

-- This group of imports is for debugging
import Common.PrecDoc
import qualified Data.IntMap as IntMap
import Data.IORef
import Text.PrettyPrint.HughesPJ
import Type.Type

import Parser.Driver
import Parser.ParserSyntax(createParserGlobals)
import qualified CParser2.Driver
import LowLevel.InitializeBuiltins
import Builtins.Builtins
import Type.Environment
import qualified SystemF.TypecheckMem
import SystemF.Datatypes.TypeLayout
import SystemF.Datatypes.Structure
import SystemF.Datatypes.Size
import CommandLine
import Globals
import GlobalVar

-- | Initialization is performed here
loadBuiltins :: CommandLineGlobals -> IO ()
loadBuiltins cl_globals = do
  -- Initialize globals from command_line
  initializeGlobalVar the_fuel (newIORef $ initValueForFuel cl_globals)

  -- Initialize the Core builtins
  --withTheNewVarIdentSupply Builtins.Builtins.initializeBuiltins
  
  -- Initialize the parser's index of global variables
  initializeGlobalVar parserGlobals $
    modifyStaticGlobalVar the_nextParserVarID $ \n ->
    let vars = createParserGlobals n
    in return (n + length vars, vars)

  -- DEBUG: new core IR initialization
  withTheNewVarIdentSupply $ \supply -> do
    (sf_types, spec_types, mem_types, core_module, core_variables) <-
      CParser2.Driver.parseCoreModule2 supply
    initializeGlobalVar the_systemFTypes (return sf_types)
    initializeGlobalVar the_specTypes (return spec_types)
    initializeGlobalVar the_memTypes (return mem_types)
    initializeGlobalVar the_coreModule (return core_module)
    Builtins.Builtins.initializeBuiltins2 core_variables

  -- Check core module for type errors
  when (useCoreIR cl_globals) $ do
    core_module <- readInitGlobalVarIO the_coreModule
    SystemF.TypecheckMem.typeCheckModule core_module

  -- Initialize the low-level builtins
  withTheLLVarIdentSupply $ \ll_supply -> do
    withTheNewVarIdentSupply $ \supply -> do
      mem_types <- readInitGlobalVarIO the_memTypes
      initializeLowLevelBuiltins supply ll_supply mem_types

  -- IN DEVELOPMENT: Compute size and alignment of each built-in type
  withTheNewVarIdentSupply $ \supply -> do
    mem_types <- readInitGlobalVarIO the_memTypes
    computeAllDataSizes supply mem_types

    withTheLLVarIdentSupply $ \ll_supply -> do
      testMemoryLayout supply ll_supply mem_types
  
  {- -- IN DEVELOPMENT: Compute size and alignment of each built-in type
  mem_types <- readInitGlobalVarIO the_memTypes
  withTheNewVarIdentSupply $ \supply -> do
    layouts <- computeTypeLayouts supply mem_types
    initializeGlobalVar the_layouts (return layouts) -}

