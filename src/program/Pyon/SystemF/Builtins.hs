
module Pyon.SystemF.Builtins
       (EqDictMembers(..), OrdDictMembers(..), TraversableDictMembers(..),
        loadPyonBuiltins, pyonBuiltin, isPyonBuiltin,
        the_Action, the_Stream, the_bool, the_list,
        the_NoneType, the_Any, 
        the_EqDict, the_OrdDict, the_TraversableDict,
        the_EqDict_Int, the_OrdDict_Int,
        the_EqDict_Float, the_OrdDict_Float,
        the_EqDict_Tuple2, the_OrdDict_Tuple2,
        the_TraversableDict_Stream, the_TraversableDict_list,
        the_oper_ADD,
        the_oper_SUB,
        the_oper_MUL,
        the_oper_DIV,
        the_oper_MOD,
        the_oper_POWER,
        the_oper_FLOORDIV,
        the_oper_BITWISEAND,
        the_oper_BITWISEOR,
        the_oper_BITWISEXOR,
        the_oper_NEGATE,
        the_oper_CAT_MAP,
        the_oper_GUARD,
        the_oper_DO,
        the_fun_makelist,
        the_fun_map,
        the_fun_reduce,
        the_fun_reduce1,
        the_fun_zip,
        the_fun_iota,
        the_fun_undefined,
        getPyonTupleType, getPyonTupleType'
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
  , the_NoneType :: Con
  , the_Any :: Con
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
    
    -- Functions
  , the_oper_ADD :: Con
  , the_oper_SUB :: Con
  , the_oper_MUL :: Con
  , the_oper_DIV :: Con
  , the_oper_MOD :: Con
  , the_oper_POWER :: Con
  , the_oper_FLOORDIV :: Con
  , the_oper_BITWISEAND :: Con
  , the_oper_BITWISEOR :: Con
  , the_oper_BITWISEXOR :: Con
  , the_oper_NEGATE :: Con
  , the_oper_CAT_MAP :: Con
  , the_oper_GUARD :: Con
  , the_oper_DO :: Con
  , the_fun_makelist :: Con
  , the_fun_map :: Con
  , the_fun_reduce :: Con
  , the_fun_reduce1 :: Con
  , the_fun_zip :: Con
  , the_fun_iota :: Con
  , the_fun_undefined :: Con
  }

assign_Action x b = b {the_Action = x}
assign_Stream x b = b {the_Stream = x}
assign_bool x b = b {the_bool = x}
assign_list x b = b {the_list = x}
assign_NoneType x b = b {the_NoneType = x}
assign_Any x b = b {the_Any = x}
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
assign_oper_ADD x b = b {the_oper_ADD = x}
assign_oper_SUB x b = b {the_oper_SUB = x}
assign_oper_MUL x b = b {the_oper_MUL = x}
assign_oper_DIV x b = b {the_oper_DIV = x}
assign_oper_MOD x b = b {the_oper_MOD = x}
assign_oper_POWER x b = b {the_oper_POWER = x}
assign_oper_FLOORDIV x b = b {the_oper_FLOORDIV = x}
assign_oper_BITWISEAND x b = b {the_oper_BITWISEAND = x}
assign_oper_BITWISEOR x b = b {the_oper_BITWISEOR = x}
assign_oper_BITWISEXOR x b = b {the_oper_BITWISEXOR = x}
assign_oper_NEGATE x b = b {the_oper_NEGATE = x}
assign_oper_CAT_MAP x b = b {the_oper_CAT_MAP = x}
assign_oper_GUARD x b = b {the_oper_GUARD = x}
assign_oper_DO x b = b {the_oper_DO = x}
assign_fun_makelist x b = b {the_fun_makelist = x}
assign_fun_map x b = b {the_fun_map = x}
assign_fun_reduce x b = b {the_fun_reduce = x}
assign_fun_reduce1 x b = b {the_fun_reduce1 = x}
assign_fun_zip x b = b {the_fun_zip = x}
assign_fun_iota x b = b {the_fun_iota = x}
assign_fun_undefined x b = b {the_fun_undefined = x}

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

isPyonBuiltin :: Con -> (PyonBuiltins -> Con) -> Bool
c `isPyonBuiltin` name = c == pyonBuiltin name

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

getPyonTupleType' :: Int -> Con
getPyonTupleType' n = case getPyonTupleType n
                      of Just t -> t
                         Nothing -> internalError "Unsupported tuple size"

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
                           , the_Any = uninitialized
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
                           , the_oper_ADD = uninitialized
                           , the_oper_SUB = uninitialized
                           , the_oper_MUL = uninitialized
                           , the_oper_DIV = uninitialized
                           , the_oper_MOD = uninitialized
                           , the_oper_POWER = uninitialized
                           , the_oper_FLOORDIV = uninitialized
                           , the_oper_BITWISEAND = uninitialized
                           , the_oper_BITWISEOR = uninitialized
                           , the_oper_BITWISEXOR = uninitialized
                           , the_oper_NEGATE = uninitialized
                           , the_oper_CAT_MAP = uninitialized
                           , the_oper_GUARD = uninitialized
                           , the_oper_DO = uninitialized
                           , the_fun_makelist = uninitialized
                           , the_fun_map = uninitialized
                           , the_fun_reduce = uninitialized
                           , the_fun_reduce1 = uninitialized
                           , the_fun_zip = uninitialized
                           , the_fun_iota = uninitialized
                           , the_fun_undefined = uninitialized
                           }
      setGlobalCons =
        setBuiltinValues [ ("Action", assign_Action)
                         , ("Stream", assign_Stream)
                         , ("bool", assign_bool)
                         , ("list", assign_list)
                         , ("NoneType", assign_NoneType)
                         , ("Any", assign_Any)
                         , ("EqDict", assign_EqDict)
                         , ("OrdDict", assign_OrdDict)
                         , ("TraversableDict", assign_TraversableDict)
                         , ("oper_ADD", assign_oper_ADD)
                         , ("oper_SUB", assign_oper_SUB)
                         , ("oper_MUL", assign_oper_MUL)
                         , ("oper_DIV", assign_oper_DIV)
                         , ("oper_MOD", assign_oper_MOD)
                         , ("oper_POWER", assign_oper_POWER)
                         , ("oper_FLOORDIV", assign_oper_FLOORDIV)
                         , ("oper_BITWISEAND", assign_oper_BITWISEAND)
                         , ("oper_BITWISEOR", assign_oper_BITWISEOR)
                         , ("oper_BITWISEXOR", assign_oper_BITWISEXOR)
                         , ("oper_NEGATE", assign_oper_NEGATE)
                         , ("oper_CAT_MAP", assign_oper_CAT_MAP)
                         , ("oper_GUARD", assign_oper_GUARD)
                         , ("oper_DO", assign_oper_DO)
                         , ("fun_makelist", assign_fun_makelist)
                         , ("fun_map", assign_fun_map)
                         , ("fun_reduce", assign_fun_reduce)
                         , ("fun_reduce1", assign_fun_reduce1)
                         , ("fun_zip", assign_fun_zip)
                         , ("fun_iota", assign_fun_iota)
                         , ("fun_undefined", assign_fun_undefined)
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