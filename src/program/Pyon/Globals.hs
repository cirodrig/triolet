
module Pyon.Globals where

import Control.Monad
import Data.IORef
import Data.Maybe
import System.IO.Unsafe

import Gluon.Common.Supply
import Gluon.Common.Identifier
import Gluon.Core
import Gluon.Core.Module
import Gluon.Parser.Driver
import qualified Pyon.SystemF.Syntax as SystemF
import Pyon.SystemF.Builtins

the_systemFVarIdentSupply :: IORef (Supply (Ident SystemF.Var))
the_systemFVarIdentSupply = unsafePerformIO $ newIORef =<< newIdentSupply

the_varIdentSupply :: IORef (Supply (Ident Var))
the_varIdentSupply = unsafePerformIO $ newIORef =<< newIdentSupply

the_conIdentSupply :: IORef (Supply (Ident Con))
the_conIdentSupply = unsafePerformIO $ newIORef =<< newIdentSupply

the_builtinModule :: IORef (Maybe (Module ()))
the_builtinModule = unsafePerformIO $ newIORef Nothing

getNextSystemFVarIdent :: IO (Ident SystemF.Var)
getNextSystemFVarIdent = supplyValue =<< readIORef the_systemFVarIdentSupply

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

-- Return True if builtins are loaded, False otherwise
checkBuiltinsStatus :: IO Bool
checkBuiltinsStatus = return . isJust =<< readIORef the_builtinModule

loadBuiltins :: IO ()
loadBuiltins = do
  -- Builtins must not have been loaded already
  builtinsLoaded <- checkBuiltinsStatus
  when builtinsLoaded $ fail "Builtins already loaded"
  
  varIDs <- readIORef the_varIdentSupply
  conIDs <- readIORef the_conIdentSupply
  result <- Gluon.Parser.Driver.loadBuiltins varIDs conIDs
  case result of
    Just bi -> do writeIORef the_builtinModule (Just bi)
                  _ <- loadPyonBuiltins varIDs conIDs bi
                  return ()
    Nothing -> fail "Could not load builtins"
