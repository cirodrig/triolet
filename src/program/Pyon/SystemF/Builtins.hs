
module Pyon.SystemF.Builtins
       (EqDictMembers(..), OrdDictMembers(..), TraversableDictMembers(..),
        loadPyonBuiltins, pyonBuiltin,
        the_Action, the_Stream, the_bool, the_list,
        the_NoneType, the_EqDict, the_OrdDict, the_TraversableDict,
        the_EqDict_Int, the_OrdDict_Int,
        the_EqDict_Float, the_OrdDict_Float,
        the_EqDict_Tuple2, the_OrdDict_Tuple2,
        the_TraversableDict_Stream, the_TraversableDict_list,
        getPyonTupleType
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

data EqDictMembers =
  EqDictMembers
  { eqMember :: !Con
  , neMember :: !Con
  }

data OrdDictMembers =
  OrdDictMembers
  { ltMember :: !Con
  , leMember :: !Con
  , gtMember :: !Con
  , geMember :: !Con
  }

data TraversableDictMembers =
  TraversableDictMembers
  { traverseMember :: !Con
  }

data PyonBuiltins =
  PyonBuiltins
  { the_Action :: Con
  , the_Stream :: Con
  , the_bool   :: Con
  , the_list   :: Con
  , the_iter   :: Con
  , the_NoneType :: Con
  , the_EqDict :: Con
  , the_OrdDict :: Con
  , the_TraversableDict :: Con
    
    -- Class dictionary members
  , the_EqDict_Int :: EqDictMembers
  , the_OrdDict_Int :: OrdDictMembers
  , the_EqDict_Float :: EqDictMembers
  , the_OrdDict_Float :: OrdDictMembers
  , the_EqDict_Tuple2 :: EqDictMembers
  , the_OrdDict_Tuple2 :: OrdDictMembers
  , the_TraversableDict_Stream :: TraversableDictMembers
  , the_TraversableDict_list :: TraversableDictMembers
  
  , the_tuples :: [Con]
  }

assign_Action x b = b {the_Action = x}
assign_Stream x b = b {the_Stream = x}
assign_bool x b = b {the_bool = x}
assign_list x b = b {the_list = x}
assign_NoneType x b = b {the_NoneType = x}
assign_EqDict x b = b {the_EqDict = x}
assign_OrdDict x b = b {the_OrdDict = x}
assign_TraversableDict x b = b {the_TraversableDict = x}
assign_EqDict_Int x b = b {the_EqDict_Int = x}
assign_OrdDict_Int x b = b {the_OrdDict_Int = x}
assign_EqDict_Float x b = b {the_EqDict_Float = x}
assign_OrdDict_Float x b = b {the_OrdDict_Float = x}
assign_EqDict_Tuple2 x b = b {the_EqDict_Tuple2 = x}
assign_OrdDict_Tuple2 x b = b {the_OrdDict_Tuple2 = x}
assign_TraversableDict_Stream x b = b {the_TraversableDict_Stream = x}
assign_TraversableDict_list x b = b {the_TraversableDict_list = x}

the_PyonBuiltins :: MVar PyonBuiltins
{-# NOINLINE the_PyonBuiltins #-}
the_PyonBuiltins = unsafePerformIO newEmptyMVar

pyonBuiltin :: (PyonBuiltins -> a) -> a
pyonBuiltin field = unsafePerformIO $ do
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

setBuiltinEqDict mod eq_name ne_name updater bi =
  let c_eq = findConByName mod eq_name
      c_ne = findConByName mod ne_name
      dict = EqDictMembers c_eq c_ne
  in dict `seq` updater dict bi

setBuiltinOrdDict mod lt_name le_name gt_name ge_name updater bi =
  let c_lt = findConByName mod lt_name
      c_le = findConByName mod le_name
      c_gt = findConByName mod gt_name
      c_ge = findConByName mod ge_name
      dict = OrdDictMembers c_lt c_le c_gt c_ge
  in dict `seq` updater dict bi

setBuiltinTraversableDict mod traverse_name updater bi =
  let c = findConByName mod traverse_name
      dict = TraversableDictMembers c
  in dict `seq` updater dict bi

-- Load symbols from the module and use them to initialize the builtins
initializePyonBuiltins :: Module () -> IO ()
initializePyonBuiltins mod =
  let start = PyonBuiltins { the_Action = uninitialized
                           , the_Stream = uninitialized
                           , the_bool = uninitialized
                           , the_list = uninitialized
                           , the_NoneType = uninitialized
                           , the_EqDict = uninitialized
                           , the_OrdDict = uninitialized
                           , the_TraversableDict = uninitialized
                           , the_EqDict_Int = uninitialized
                           , the_OrdDict_Int = uninitialized
                           , the_EqDict_Float = uninitialized
                           , the_OrdDict_Float = uninitialized
                           , the_EqDict_Tuple2 = uninitialized
                           , the_OrdDict_Tuple2 = uninitialized
                           , the_TraversableDict_Stream = uninitialized
                           , the_TraversableDict_list = uninitialized
                           , the_tuples = uninitialized
                           }
      setGlobalCons =
        setBuiltinValues [ ("Action", assign_Action)
                         , ("Stream", assign_Stream)
                         , ("bool", assign_bool)
                         , ("list", assign_list)
                         , ("NoneType", assign_NoneType)
                         , ("EqDict", assign_EqDict)
                         , ("OrdDict", assign_OrdDict)
                         , ("TraversableDict", assign_TraversableDict)
                         ]
      setClassDicts =
        setEqDict "Eq_EQ_Int" "Eq_NE_Int" assign_EqDict_Int .
        setOrdDict "Ord_LT_Int" "Ord_LE_Int" 
                   "Ord_GT_Int" "Ord_GE_Int" assign_OrdDict_Int .
        setEqDict "Eq_EQ_Float" "Eq_NE_Float" assign_EqDict_Float .
        setOrdDict "Ord_LT_Float" "Ord_LE_Float" 
                   "Ord_GT_Float" "Ord_GE_Float" assign_OrdDict_Float .
        setEqDict "Eq_EQ_Tuple2" "Eq_NE_Tuple2" assign_EqDict_Tuple2 .
        setOrdDict "Ord_LT_Tuple2" "Ord_LE_Tuple2"
                   "Ord_GT_Tuple2" "Ord_GE_Tuple2" assign_OrdDict_Tuple2 .
        setTraversableDict "Traversable_TRAVERSE_Stream" 
                           assign_TraversableDict_Stream .
        setTraversableDict "Traversable_TRAVERSE_list"
                           assign_TraversableDict_list
  in do bi <- evaluate $ setTupleTypes $ setGlobalCons $ setClassDicts start
        putMVar the_PyonBuiltins bi
  where
    uninitialized = internalError $ "Uninitialized Pyon builtin accessed"
    
    setBuiltinValues xs bi =
      foldl' (\bi (name, ref) -> setBuiltinValue mod name ref bi) bi xs
    
    setEqDict = setBuiltinEqDict mod
    setOrdDict = setBuiltinOrdDict mod
    setTraversableDict = setBuiltinTraversableDict mod
    
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