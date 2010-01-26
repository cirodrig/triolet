
module GluonBackend where

import Control.Monad
import Data.IORef
import Data.Maybe
import System.IO.Unsafe

import Gluon.Builtins.Pyon
import Gluon.Common.Supply
import Gluon.Common.Identifier
import Gluon.Core
import Gluon.Core.Module
import Gluon.Parser.Driver

the_varIdentSupply :: IORef (Supply (Ident Var))
the_varIdentSupply = unsafePerformIO $ newIORef =<< newIdentSupply

the_conIdentSupply :: IORef (Supply (Ident Con))
the_conIdentSupply = unsafePerformIO $ newIORef =<< newIdentSupply

the_builtinModule :: IORef (Maybe (Module ()))
the_builtinModule = unsafePerformIO $ newIORef Nothing

getNextVarIdent :: IO (Ident Var)
getNextVarIdent = supplyValue =<< readIORef the_varIdentSupply

setNextVarIdent :: Ident Var -> IO ()
setNextVarIdent ident = 
  let last = toIdent $ pred $ fromIdent ident
  in writeIORef the_varIdentSupply =<< newIdentSupplyAfter last

getNextConIdent :: IO (Ident Con)
getNextConIdent = supplyValue =<< readIORef the_conIdentSupply

setNextConIdent :: Ident Con -> IO ()
setNextConIdent ident = 
  let last = toIdent $ pred $ fromIdent ident
  in writeIORef the_conIdentSupply =<< newIdentSupplyAfter last

loadBuiltins :: IO ()
loadBuiltins = do
  -- Builtins must not have been loaded already 
  oldBuiltins <- readIORef the_builtinModule
  unless (isNothing oldBuiltins) $ fail "Builtins already loaded"
  
  varIDs <- readIORef the_varIdentSupply
  conIDs <- readIORef the_conIdentSupply
  result <- Gluon.Parser.Driver.loadBuiltins varIDs conIDs
  case result of
    Just bi -> do writeIORef the_builtinModule (Just bi)
                  _ <- loadPyonBuiltins varIDs conIDs bi
                  return ()
    Nothing -> fail "Could not load builtins"
