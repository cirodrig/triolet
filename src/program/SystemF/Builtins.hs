
{-# LANGUAGE TemplateHaskell #-}
module SystemF.Builtins
       (EqDictMembers(..), OrdDictMembers(..), TraversableDictMembers(..),
        AdditiveDictMembers(..), VectorDictMembers(..),
        loadPyonBuiltins, arePyonBuiltinsInitialized,
        pyonBuiltin, isPyonBuiltin,
        the_Stream,
        the_LazyStream,
        the_Ptr,
        the_Own,
        the_Def,
        the_Undef,
        the_Action,
        the_bool,
        the_int,
        the_float,
        the_list,
        the_NoneType, 
        the_Any, 
        the_PassConv,
        the_passConv_int,
        the_passConv_float,
        the_passConv_bool,
        the_passConv_NoneType,
        the_passConv_iter,
        the_passConv_list,
        the_passConv_Any,
        the_EqDict, the_OrdDict, the_TraversableDict,
        the_AdditiveDict, the_VectorDict,
        the_EqDict_int, the_OrdDict_int,
        the_EqDict_float, the_OrdDict_float,
        the_EqDict_Tuple2, the_OrdDict_Tuple2,
        the_TraversableDict_Stream, the_TraversableDict_list,
        the_AdditiveDict_int, the_AdditiveDict_float,
        the_None, the_True, the_False,
        the_eqDict, the_ordDict, the_traversableDict,
        the_additiveDict, the_vectorDict,
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
        the_fun_map_Stream,
        the_fun_reduce,
        the_fun_reduce1,
        the_fun_reduce1_Stream,
        the_fun_zip,
        the_fun_zip_SS, the_fun_zip_NS, the_fun_zip_SN,
        the_fun_iota,
        the_fun_undefined,
        {-the_fun_copy,-}
        the_fun_store_int,
        the_fun_store_float,
        the_fun_store_bool,
        the_fun_store_NoneType,
        the_fun_load_int,
        the_fun_load_float,
        the_fun_load_bool,
        the_fun_load_NoneType,
        getPyonTupleType, getPyonTupleType',
        getPyonTupleCon, getPyonTupleCon',
        getPyonTuplePassConv, getPyonTuplePassConv',
        whichPyonTupleCon, whichPyonTupleTypeCon,
        isDictionaryCon
       )
where

import Control.Exception
import Control.Monad
import Control.Concurrent.MVar
import Data.List
import qualified Data.IntSet as IntSet
import Language.Haskell.TH(stringE)
import System.FilePath
import System.IO.Unsafe

import Gluon.Common.THRecord
import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.Label
import Gluon.Core
import Gluon.Core.Module
import Gluon.Parser.Setup
import Gluon.Parser.Driver
import Paths_pyon

import SystemF.BuiltinsTH

$(do d <- declareRecord pyonBuiltinsSpecification
     return [d])

$(do declareFieldReaders pyonBuiltinsSpecification "the")
$(do declareFieldWriters pyonBuiltinsSpecification "setThe")

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

infix 4 `isPyonBuiltin`
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

getPyonTupleCon :: Int -> Maybe Con
getPyonTupleCon size = unsafePerformIO $ do
  -- Ensure that we've already initialized these
  bi_is_empty <- isEmptyMVar the_PyonBuiltins
  when bi_is_empty $ internalError "Pyon builtins are uninitialized"
  
  bi <- readMVar the_PyonBuiltins
  let ts = the_tupleConstructors bi
  return $! if size >= 0 && size < length ts
            then Just (ts !! size)
            else Nothing

getPyonTupleCon' :: Int -> Con
getPyonTupleCon' n = case getPyonTupleCon n
                     of Just t -> t
                        Nothing -> internalError "Unsupported tuple size"

getPyonTuplePassConv :: Int -> Maybe Con
getPyonTuplePassConv size = unsafePerformIO $ do
  -- Ensure that we've already initialized these
  bi_is_empty <- isEmptyMVar the_PyonBuiltins
  when bi_is_empty $ internalError "Pyon builtins are uninitialized"

  bi <- readMVar the_PyonBuiltins
  let ts = the_tuplePassConvConstructors bi
  return $! if size >= 0 && size < length ts
            then Just (ts !! size)
            else Nothing
  
getPyonTuplePassConv' :: Int -> Con
getPyonTuplePassConv' size =
  case getPyonTuplePassConv size
  of Just t -> t
     Nothing -> internalError "Unsupported tuple size"

-- | If the parameter is a tuple constructor, return the tuple size.
-- Otherwise return Nothing.
whichPyonTupleCon :: Con -> Maybe Int
whichPyonTupleCon c = unsafePerformIO $ do
  -- Ensure that we've already initialized these
  bi_is_empty <- isEmptyMVar the_PyonBuiltins
  when bi_is_empty $ internalError "Pyon builtins are uninitialized"
  
  bi <- readMVar the_PyonBuiltins
  return $ findIndex (c ==) $ the_tupleConstructors bi
  
-- | If the parameter is a tuple type constructor, return the tuple size.
-- Otherwise return Nothing.
whichPyonTupleTypeCon :: Con -> Maybe Int
whichPyonTupleTypeCon c = unsafePerformIO $ do
  -- Ensure that we've already initialized these
  bi_is_empty <- isEmptyMVar the_PyonBuiltins
  when bi_is_empty $ internalError "Pyon builtins are uninitialized"
  
  bi <- readMVar the_PyonBuiltins
  return $ findIndex (c ==) $ the_tuples bi

-- | Determine whether the given constructor builds a dictionary object
-- or passing convention object.
isDictionaryCon :: Con -> Bool
isDictionaryCon c =
  fromIdent (conID c) `IntSet.member` dictionary_constructor_ids
  where
    dictionary_constructor_ids =
      IntSet.fromList $
      map (fromIdent . conID . pyonBuiltin) dictionary_constructors

    dictionary_constructors =
      [the_eqDict, the_ordDict, the_traversableDict, the_additiveDict,
       the_vectorDict,
       the_passConv_int, the_passConv_float, the_passConv_bool,
       the_passConv_NoneType, the_passConv_iter, the_passConv_list,
       the_passConv_Any]

findConByName mod name =
  let label = pgmLabel pyonBuiltinModuleName name
  in case find ((label ==) . conName) $ getConstructors mod
     of Just c  -> c
        Nothing -> internalError $ "Missing Pyon builtin '" ++ name ++ "'"
  where
    getConstructors mod = concat [c : conCtors c | c <- moduleConstructors mod]

-- | Read a list of tuple type constructors from the module
readTupleTypes mod =
  let tupleTypeNames = ["PyonTuple" ++ show n | n <- [0..5]]
      tupleTypes = map (findConByName mod) tupleTypeNames
      force x = foldl' (flip seq) x tupleTypes
  in force $ return tupleTypes

-- | Read a list of tuple data constructors from the module
readTuples mod =
  let tupleNames = ["pyonTuple" ++ show n | n <- [0..5]]
      tupleConstructors = map (findConByName mod) tupleNames
      force x = foldl' (flip seq) x tupleConstructors
  in force $ return tupleConstructors

-- | Read a list of tuple parameter-passing convention constructors from
-- the module
readTuplePassConvs mod =
  let names = ["passConv_pyonTuple" ++ show n | n <- [0..5]]
      cons = map (findConByName mod) names
      force x = foldl' (flip seq) x cons
  in force $ return cons

-- Load symbols from the module and use them to initialize the builtins
initializePyonBuiltins :: Module () -> IO ()
initializePyonBuiltins mod = do
  -- Must not have been initialized yet
  is_empty <- isEmptyMVar the_PyonBuiltins
  unless is_empty $ fail "Cannot re-initialize pyon builtins"
  
  -- Load and create builtins
  bi <-
    $(let -- Initialize each constructor field
        assign_ctor_field fname name =
          (fname, [| evaluate $ findConByName mod name |])
        constructors = zipWith assign_ctor_field
                       pyonBuiltinConstructorNames pyonBuiltinConstructors
        
        -- Initialize class dictionaries
        findNameWithPrefix name pfx =
          [| findConByName mod $(stringE $ pfx ++ name) |]
        eq_dict name =
          ("_EqDict_" ++ name, 
           [| let c_eq = $(findNameWithPrefix name "Eq_EQ_")
                  c_ne = $(findNameWithPrefix name "Eq_NE_")
              in evaluate $ EqDictMembers c_eq c_ne |])

        ord_dict name =
          ("_OrdDict_" ++ name,
           [| let c_gt = $(findNameWithPrefix name "Ord_GT_")
                  c_ge = $(findNameWithPrefix name "Ord_GE_")
                  c_lt = $(findNameWithPrefix name "Ord_LT_")
                  c_le = $(findNameWithPrefix name "Ord_LE_")
              in evaluate $ OrdDictMembers c_lt c_le c_gt c_ge |])

        traversable_dict name =
          ("_TraversableDict_" ++ name,
           [| let c = $(findNameWithPrefix name "Traversable_TRAVERSE_")
              in evaluate $ TraversableDictMembers c |])

        additive_dict name =
          ("_AdditiveDict_" ++ name,
           [| let c_zero = $(findNameWithPrefix name "Additive_ZERO_")
                  c_add = $(findNameWithPrefix name "Additive_ADD_")
                  c_sub = $(findNameWithPrefix name "Additive_SUB_")
              in evaluate $ AdditiveDictMembers c_zero c_add c_sub |])

        -- All field initializers
        initializers =
          constructors ++
          [ ("_tuples", [| readTupleTypes mod |])
          , ("_tupleConstructors", [| readTuples mod |])
          , ("_tuplePassConvConstructors", [| readTuplePassConvs mod |])
          , eq_dict "int"
          , eq_dict "float"
          , eq_dict "Tuple2"
          , ord_dict "int"
          , ord_dict "float"
          , ord_dict "Tuple2"
          , traversable_dict "Stream"
          , traversable_dict "list"
          , additive_dict "int"
          , additive_dict "float"
          ]
      in initializeRecordM pyonBuiltinsSpecification initializers)

  -- Store builtins in a global variable
  putMVar the_PyonBuiltins bi

arePyonBuiltinsInitialized :: IO Bool
arePyonBuiltinsInitialized =
  liftM not $ isEmptyMVar the_PyonBuiltins

loadPyonBuiltins :: IdentSupply Var
                 -> IdentSupply Con
                 -> Module ()
                 -> IO (Maybe (Module ()))
loadPyonBuiltins varIDs conIDs builtins = do
  let setup = contextParserSetup varIDs conIDs [builtins]
  fileName <- getDataFileName ("symbols"</>"SFBuiltin.glu")
  m <- loadSourceFile setup fileName
  case m of
    Just cu -> do initializePyonBuiltins cu
                  return $ Just cu
    Nothing -> return Nothing