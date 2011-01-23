{-| Initialization of global variables.
--  This is in a separate module to eliminate dependences on the gluon-eval 
--  package when executing Template Haskell.
-}
module InitializeGlobals where

import Control.Monad
import Control.Concurrent.MVar

import Gluon.Parser.Driver
import Parser.Driver
import Parser.ParserSyntax(createParserGlobals)
import SystemF.Builtins
import CParser.Driver
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

  withTheVarIdentSupply $ \varIDs ->
    withTheConIdentSupply $ \conIDs -> do

      -- Load the Gluon builtin module
      initializeGlobalVar the_builtinModule $ do
        result <- Gluon.Parser.Driver.loadBuiltins varIDs conIDs
        case result of
          Just bi -> return bi
          Nothing -> fail "Could not load Gluon builtins"
          
      gluon_builtins <- readInitGlobalVarIO the_builtinModule
      
      -- Initialize the parser's index of global variables
      initializeGlobalVar parserGlobals $
        modifyStaticGlobalVar the_nextParserVarID $ \n ->
        let vars = createParserGlobals n
        in return (n + length vars, vars)
      
      -- Initialize the System F builtins
      result <- loadPyonBuiltins varIDs conIDs gluon_builtins
      case result of
        Just _ -> return () 
        Nothing -> fail "Could not load Pyon builtins"
        
      -- Initialize the Core types
      initializeGlobalVar the_coreTypes (parseCoreModule varIDs)

      withTheNewVarIdentSupply $ \supply -> do
        core_types <- CParser2.Driver.parseCoreModule supply
        initializeGlobalVar the_newCoreTypes (return core_types)
        initializeGlobalVar the_systemFTypes (return $ convertToPureTypeEnv core_types)
        initializeGlobalVar the_memTypes (return $ convertToMemTypeEnv core_types)

      -- Initialize the low-level builtins
      withTheLLVarIdentSupply $ \supply -> do
        mem_types <- readInitGlobalVarIO the_memTypes
        initializeLowLevelBuiltins supply mem_types
