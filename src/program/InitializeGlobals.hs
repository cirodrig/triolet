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
import CommandLine
import Globals
import GlobalVar

-- | Initialization is performed here
loadBuiltins :: CommandLineGlobals -> IO ()
loadBuiltins cl_globals = do
  -- Initialize globals from command_line
  initializeGlobalVar the_fuel (newIORef $ initValueForFuel cl_globals)

  -- Initialize the Core builtins
  withTheNewVarIdentSupply Builtins.Builtins.initializeBuiltins

  -- Initialize the parser's index of global variables
  initializeGlobalVar parserGlobals $
    modifyStaticGlobalVar the_nextParserVarID $ \n ->
    let vars = createParserGlobals n
    in return (n + length vars, vars)

  -- Initialize core IR data structures
  withTheNewVarIdentSupply $ \supply -> do
    core_types <- CParser2.Driver.parseCoreModule supply
    initializeGlobalVar the_specTypes (return core_types)
    initializeGlobalVar the_systemFTypes (return $ specToPureTypeEnv core_types)
    let mem_types = specToMemTypeEnv core_types
    initializeGlobalVar the_memTypes (return mem_types)

  -- Initialize core functions if needed
  when (useCoreIR cl_globals) $ do
    mem_types <- readInitGlobalVarIO the_memTypes
    core_module <- withTheNewVarIdentSupply $ \supply -> do
      CParser2.Driver.parseCoreFunctions supply mem_types
      
    -- Typecheck the module to detect errors
    SystemF.TypecheckMem.typeCheckModule core_module
    initializeGlobalVar the_coreModule (return core_module)

  -- Initialize the low-level builtins
  withTheLLVarIdentSupply $ \ll_supply -> do
    withTheNewVarIdentSupply $ \supply -> do
      mem_types <- readInitGlobalVarIO the_memTypes
      initializeLowLevelBuiltins supply ll_supply mem_types
