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
-- import qualified CParser.Driver
import qualified CParser2.Driver
import LowLevel.InitializeBuiltins
import Builtins.Builtins
import Type.Environment
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
  
  withTheNewVarIdentSupply $ \supply -> do
    -- core_types <- CParser.Driver.parseCoreModule supply
    -- initializeGlobalVar the_newCoreTypes (return core_types)
    -- initializeGlobalVar the_systemFTypes (return $ convertToPureTypeEnv core_types)
    -- initializeGlobalVar the_memTypes (return $ convertToMemTypeEnv core_types)

    -- This will eventually replace the old core types
    core2_types <- CParser2.Driver.parseCoreModule supply
    initializeGlobalVar the_specTypes (return core2_types)
    initializeGlobalVar the_systemFTypes (return $ specToPureTypeEnv core2_types)
    initializeGlobalVar the_memTypes (return $ specToMemTypeEnv core2_types)
    -- print $ vcat [hang (text $ show n) 6 (unparenthesized $ pprReturn t) | (n, t) <- IntMap.toList $ getAllTypes core2_types]

  -- Initialize the low-level builtins
  withTheLLVarIdentSupply $ \ll_supply -> do
    withTheNewVarIdentSupply $ \supply -> do
      mem_types <- readInitGlobalVarIO the_memTypes
      initializeLowLevelBuiltins supply ll_supply mem_types
