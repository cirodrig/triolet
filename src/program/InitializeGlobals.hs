{-| Initialization of global variables.
--  This is in a separate module to eliminate dependences on the gluon-eval 
--  package when executing Template Haskell.
-}
module InitializeGlobals where

import Control.Monad
import Control.Concurrent.MVar

import Parser.Driver
import Parser.ParserSyntax(createParserGlobals)
import qualified CParser2.Driver
import LowLevel.InitializeBuiltins
import Builtins.Builtins
import Type.Environment
import Globals
import GlobalVar

loadBuiltins :: IO ()
loadBuiltins = do
  -- Initialize the Core builtins
  withTheNewVarIdentSupply Builtins.Builtins.initializeBuiltins

  -- Initialize the parser's index of global variables
  initializeGlobalVar parserGlobals $
    modifyStaticGlobalVar the_nextParserVarID $ \n ->
    let vars = createParserGlobals n
    in return (n + length vars, vars)
  
  withTheNewVarIdentSupply $ \supply -> do
    core_types <- CParser2.Driver.parseCoreModule supply
    initializeGlobalVar the_newCoreTypes (return core_types)
    initializeGlobalVar the_systemFTypes (return $ convertToPureTypeEnv core_types)
    initializeGlobalVar the_memTypes (return $ convertToMemTypeEnv core_types)

  -- Initialize the low-level builtins
  withTheLLVarIdentSupply $ \supply -> do
    mem_types <- readInitGlobalVarIO the_memTypes
    initializeLowLevelBuiltins supply mem_types
