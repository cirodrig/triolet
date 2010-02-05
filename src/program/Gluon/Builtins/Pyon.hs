
module Gluon.Builtins.Pyon
       (loadPyonBuiltins, getPyonBuiltin,
        the_Action, the_Stream, the_bool, the_list,
        the_NoneType, the_EqDict, the_OrdDict, getPyonTupleType
       )
where

import Control.Exception
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

data PyonBuiltins =
  PyonBuiltins
  { the_Action :: Con
  , the_Stream :: Con
  , the_bool   :: Con
  , the_list   :: Con
  , the_NoneType :: Con
  , the_EqDict :: Con
  , the_OrdDict :: Con
  , the_tuples :: [Con]
  }

assign_Action x b = b {the_Action = x}
assign_Stream x b = b {the_Stream = x}
assign_bool x b = b {the_bool = x}
assign_list x b = b {the_list = x}
assign_NoneType x b = b {the_NoneType = x}
assign_EqDict x b = b {the_EqDict = x}
assign_OrdDict x b = b {the_OrdDict = x}

the_PyonBuiltins :: MVar PyonBuiltins
{-# NOINLINE the_PyonBuiltins #-}
the_PyonBuiltins = unsafePerformIO newEmptyMVar

getPyonBuiltin :: (PyonBuiltins -> Con) -> Con
getPyonBuiltin field = unsafePerformIO $ do
  -- Ensure that we've already initialized these
  bi_is_empty <- isEmptyMVar the_PyonBuiltins
  when bi_is_empty $ internalError "Pyon builtins are uninitialized"
  
  -- Load and return the desired field
  bi <- readMVar the_PyonBuiltins
  return $ field bi

getPyonTupleType :: Int -> Maybe Con
getPyonTupleType size = unsafePerformIO $ do
  -- Ensure that we've already initialized these
  bi_is_empty <- isEmptyMVar the_PyonBuiltins
  when bi_is_empty $ internalError "Pyon builtins are uninitialized"
  
  bi <- readMVar the_PyonBuiltins
  let ts = the_tuples bi
  return $! if size >= 0 && size < length ts
            then Just (ts !! size)
            else Nothing

findConByName mod name =
  let label = pgmLabel (moduleName "PyonBuiltin") name
  in case find ((label ==) . conName) $ moduleConstructors mod
     of Just c  -> c
        Nothing -> internalError $ "Missing Pyon builtin '" ++ name ++ "'"

-- Look up a constructor in a module, and store it.
setBuiltinValue :: Module ()
                -> String 
                -> (Con -> PyonBuiltins -> PyonBuiltins) 
                -> PyonBuiltins
                -> PyonBuiltins
setBuiltinValue mod name updater bi =
  let c = findConByName mod name
  in c `seq` updater c bi

-- Load symbols from the module and use them to initialize the builtins
initializePyonBuiltins :: Module () -> IO ()
initializePyonBuiltins mod =
  let bi = setTupleTypes $ 
           setBuiltinValues [ ("Action", assign_Action)
                            , ("Stream", assign_Stream)
                            , ("bool", assign_bool)
                            , ("list", assign_list)
                            , ("NoneType", assign_NoneType)
                            , ("EqDict", assign_EqDict)
                            , ("OrdDict", assign_OrdDict)
                            ] $ 
           PyonBuiltins { the_Action = uninitialized
                        , the_Stream = uninitialized
                        , the_bool = uninitialized
                        , the_list = uninitialized
                        , the_NoneType = uninitialized
                        , the_EqDict = uninitialized
                        , the_OrdDict = uninitialized
                        , the_tuples = uninitialized
                        }
  in do evaluate bi
        putMVar the_PyonBuiltins bi
  where
    uninitialized = internalError $ "Uninitialized Pyon builtin accessed"
    setBuiltinValues xs bi =
      foldl' (\bi (name, ref) -> setBuiltinValue mod name ref bi) bi xs
    
    setTupleTypes bi =
      let tupleTypeNames = ["PyonTuple" ++ show n | n <- [0..5]]
          tupleTypes = map (findConByName mod) tupleTypeNames
          bi' = bi {the_tuples = tupleTypes}
      in foldl' (flip seq) bi' tupleTypes

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