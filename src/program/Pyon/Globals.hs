
module Pyon.Globals where

import Control.Monad
import Control.Concurrent.MVar
import Data.Maybe
import System.IO.Unsafe

import Gluon.Common.Supply
import Gluon.Common.Identifier
import Gluon.Core
import Gluon.Core.Module
import Gluon.Parser.Driver
import qualified Pyon.SystemF.Syntax as SystemF
import Pyon.SystemF.Builtins
import qualified Pyon.LowLevel.Syntax as LowLevel
import Pyon.LowLevel.InitializeBuiltins

the_varIdentSupply :: MVar (Supply (Ident Var))
{-# NOINLINE the_varIdentSupply #-}
the_varIdentSupply = unsafePerformIO $ newMVar =<< newIdentSupply

the_conIdentSupply :: MVar (Supply (Ident Con))
{-# NOINLINE the_conIdentSupply #-}
the_conIdentSupply = unsafePerformIO $ newMVar =<< newIdentSupply

the_llVarIdentSupply :: MVar (Supply (Ident LowLevel.Var))
{-# NOINLINE the_llVarIdentSupply #-}
the_llVarIdentSupply = unsafePerformIO $ newMVar =<< newIdentSupply

-- | The Gluon builtin module.  This starts out empty, and is written
-- when the module is loaded.
the_builtinModule :: MVar (Module ())
the_builtinModule = unsafePerformIO $ newEmptyMVar

withTheVarIdentSupply :: (Supply (Ident Var) -> IO a) -> IO a
withTheVarIdentSupply f = withMVar the_varIdentSupply f

withTheConIdentSupply :: (Supply (Ident Con) -> IO a) -> IO a
withTheConIdentSupply f = withMVar the_conIdentSupply f

withTheLLVarIdentSupply :: (Supply (Ident LowLevel.Var) -> IO a) -> IO a
withTheLLVarIdentSupply f = withMVar the_llVarIdentSupply f

getNextVarIdent :: IO (Ident Var)
getNextVarIdent = supplyValue =<< readMVar the_varIdentSupply

setNextVarIdent :: Ident Var -> IO ()
setNextVarIdent ident =
  let last = toIdent $ pred $ fromIdent ident
  in do swapMVar the_varIdentSupply =<< newIdentSupplyAfter last
        return ()

getNextConIdent :: IO (Ident Con)
getNextConIdent = supplyValue =<< readMVar the_conIdentSupply

setNextConIdent :: Ident Con -> IO ()
setNextConIdent ident =
  let last = toIdent $ pred $ fromIdent ident
  in do swapMVar the_conIdentSupply =<< newIdentSupplyAfter last
        return ()

-- Return True if builtins are loaded, False otherwise
checkBuiltinsStatus :: IO Bool
checkBuiltinsStatus = return . not =<< isEmptyMVar the_builtinModule

loadBuiltins :: IO ()
loadBuiltins = do
  -- Builtins must not have been loaded already
  builtinsLoaded <- checkBuiltinsStatus
  when builtinsLoaded $ fail "Builtins already loaded"
  
  withTheVarIdentSupply $ \varIDs ->
    withTheConIdentSupply $ \conIDs -> do
      result <- Gluon.Parser.Driver.loadBuiltins varIDs conIDs
      case result of
        Just bi -> do putMVar the_builtinModule bi
                      Just pbi <- loadPyonBuiltins varIDs conIDs bi
                      withTheLLVarIdentSupply initializeLowLevelBuiltins
                      -- _ <- Pyon.SystemF.SpclBuiltins.loadPyonBuiltins varIDs conIDs bi
                      return ()
        Nothing -> fail "Could not load builtins"
