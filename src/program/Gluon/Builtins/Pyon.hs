
module Gluon.Builtins.Pyon
       (loadPyonBuiltins,
        the_Action, the_Stream
       )
where

import Control.Monad
import Control.Concurrent.MVar
import Data.List
import System.FilePath
import System.IO.Unsafe

import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.Label
import Gluon.Core
import Gluon.Core.Module
import Gluon.Parser.Setup
import Gluon.Parser.Driver
import Paths_pyon

the_ActionType :: MVar Con
{-# NOINLINE the_ActionType #-}
the_ActionType = unsafePerformIO newEmptyMVar

the_StreamType :: MVar Con
{-# NOINLINE the_StreamType #-}
the_StreamType = unsafePerformIO newEmptyMVar

the_Action :: Con
{-# NOINLINE the_Action #-}
the_Action = unsafePerformIO $ readMVar the_ActionType

the_Stream :: Con
{-# NOINLINE the_Stream #-}
the_Stream = unsafePerformIO $ readMVar the_StreamType

-- Look up a value in a module and store it in the given reference
setBuiltinValue :: String -> MVar Con -> Module () -> IO ()
setBuiltinValue name ref mod =
  let label = pgmLabel (moduleName "PyonBuiltin") name
  in case find ((label ==) . conName) $ moduleConstructors mod
     of Just c -> putMVar ref c
        Nothing -> internalError $ "Missing Pyon builtin '" ++ name ++ "'"

initializePyonBuiltins :: Module () -> IO ()
initializePyonBuiltins mod =
  setBuiltinValues [ ("Action", the_ActionType)
                   , ("Stream", the_StreamType)
                   ]
  where
    setBuiltinValues xs =
      forM_ xs $ \(name, ref) -> setBuiltinValue name ref mod  

loadPyonBuiltins :: IdentSupply Var
                 -> IdentSupply Con
                 -> Module ()
                 -> IO (Maybe (Module ()))
loadPyonBuiltins varIDs conIDs builtins = do
  let setup = contextParserSetup varIDs conIDs [builtins]
  fileName <- getDataFileName ("library"</>"PyonBuiltin.glu")
  m <- loadSourceFile setup fileName
  case m of
    Just cu -> do initializePyonBuiltins cu
                  return $ Just cu
    Nothing -> return Nothing