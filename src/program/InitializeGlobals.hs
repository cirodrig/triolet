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
import LowLevel.InitializeBuiltins
import Globals
import GlobalVar

loadBuiltins :: IO ()
loadBuiltins =
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

      -- Initialize the low-level builtins
      withTheLLVarIdentSupply initializeLowLevelBuiltins
