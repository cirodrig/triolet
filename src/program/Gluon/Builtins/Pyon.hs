
module Gluon.Builtins.Pyon
       (loadPyonBuiltins,
        the_Action, the_Stream, the_NoneType, the_Bool, the_List,
        the_NthTupleType
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

the_NoneTypeType :: MVar Con
{-# NOINLINE the_NoneTypeType #-}
the_NoneTypeType = unsafePerformIO newEmptyMVar

the_BoolType :: MVar Con
{-# NOINLINE the_BoolType #-}
the_BoolType = unsafePerformIO newEmptyMVar

the_ListType :: MVar Con
{-# NOINLINE the_ListType #-}
the_ListType = unsafePerformIO newEmptyMVar

the_TupleTypes :: MVar [Con]
{-# NOINLINE the_TupleTypes #-}
the_TupleTypes = unsafePerformIO newEmptyMVar

the_Action :: Con
the_Action = unsafePerformIO $ readMVar the_ActionType

the_Stream :: Con
the_Stream = unsafePerformIO $ readMVar the_StreamType

the_NoneType :: Con
the_NoneType = unsafePerformIO $ readMVar the_NoneTypeType

the_Bool :: Con
the_Bool = unsafePerformIO $ readMVar the_BoolType

the_List :: Con
the_List = unsafePerformIO $ readMVar the_ListType

the_NthTupleType :: Int -> Maybe Con
the_NthTupleType n =
  let ts = unsafePerformIO $ readMVar the_TupleTypes
  in if n >= 0 && n < length ts 
     then Just (ts !! n) 
     else Nothing

findConByName mod name =
  let label = pgmLabel (moduleName "PyonBuiltin") name
  in case find ((label ==) . conName) $ moduleConstructors mod
     of Just c  -> return c
        Nothing -> internalError $ "Missing Pyon builtin '" ++ name ++ "'"

-- Look up a value in a module and store it in the given reference
setBuiltinValue :: String -> MVar Con -> Module () -> IO ()
setBuiltinValue name ref mod = do
  c <- findConByName mod name 
  putMVar ref c

initializePyonBuiltins :: Module () -> IO ()
initializePyonBuiltins mod = do
  setBuiltinValues [ ("Action", the_ActionType)
                   , ("Stream", the_StreamType)
                   , ("NoneType", the_NoneTypeType)
                   , ("Bool", the_BoolType)
                   ]
  setTupleTypes
  where
    setBuiltinValues xs =
      forM_ xs $ \(name, ref) -> setBuiltinValue name ref mod
    
    setTupleTypes = do
      tupleTypes <- mapM (findConByName mod) $
                    map (("PyonTuple" ++) . show) [0..5]
      putMVar the_TupleTypes tupleTypes

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