
{-# LANGUAGE TemplateHaskell #-}
module Builtins.Builtins where

import Control.Concurrent.MVar
import Control.Monad
import Data.Array
import qualified Data.Map as Map
import System.IO.Unsafe

import Language.Haskell.TH
import Common.Supply
import Common.Identifier
import Common.Error
import Common.Label

import Builtins.BuiltinsTH
import Type.Type

-- | The built-in variables are stored in an array
type CoreBuiltins = Array Int Var

$(do let cons = [mkName ("The_" ++ nm)
                | nm <- builtinTypeNames ++ builtinVariableNames]
         num_cons = length cons
         con_decls = [return $ NormalC c [] | c <- cons]

     -- Declare a data type
     data_decl <-
       dataD (cxt []) (mkName "BuiltinThing") [] con_decls [mkName "Enum"]
     return [data_decl])

allBuiltinVars :: [Var]
allBuiltinVars = elems builtins
  where
    builtins = unsafePerformIO $ do
      -- Ensure that we've already initialized these
      bi_is_empty <- isEmptyMVar the_CoreBuiltins
      when bi_is_empty $ internalError "Core builtins are uninitialized"

      readMVar the_CoreBuiltins

coreBuiltin :: BuiltinThing -> Var

-- Because 'coreBuiltin' is normally called with a constant argument, it's 
-- beneficial to inline it
{-# INLINE coreBuiltin #-}
coreBuiltin field = coreBuiltin' (fromEnum field)

coreBuiltin' field_index = field_index `seq` unsafePerformIO get_value 
  where
    get_value = do
      -- Ensure that we've already initialized these
      bi_is_empty <- isEmptyMVar the_CoreBuiltins
      when bi_is_empty $ internalError "Core builtins are uninitialized"
      
      -- Load and return the desired field
      bi <- readMVar the_CoreBuiltins
      return $! bi ! field_index

infix 4 `isCoreBuiltin`
isCoreBuiltin :: Var -> BuiltinThing -> Bool
v `isCoreBuiltin` name = v == coreBuiltin name

tupleTypeCon :: Int -> Var
tupleTypeCon n | n < 0 = internalError "tupleTypeCon"
               | n >= 5 = internalError "tupleTypeCon: Unsupported size"
               | otherwise = cons !! n
  where
    cons = [ coreBuiltin The_Tuple0
           , coreBuiltin The_Tuple1
           , coreBuiltin The_Tuple2
           , coreBuiltin The_Tuple3
           , coreBuiltin The_Tuple4
           ]

isTupleTypeCon :: Var -> Bool
isTupleTypeCon v = v `elem` cons
  where
    cons = [ coreBuiltin The_Tuple0
           , coreBuiltin The_Tuple1
           , coreBuiltin The_Tuple2
           , coreBuiltin The_Tuple3
           , coreBuiltin The_Tuple4
           ]

tupleCon :: Int -> Var
tupleCon n | n < 0 = internalError "tupleCon"
           | n >= 5 = internalError $ "tupleCon: Unsupported size"
           | otherwise = cons !! n
  where
    cons = [ coreBuiltin The_tuple0
           , coreBuiltin The_tuple1
           , coreBuiltin The_tuple2
           , coreBuiltin The_tuple3
           , coreBuiltin The_tuple4
           ]

isTupleCon :: Var -> Bool
isTupleCon v = v `elem` cons
  where
    cons = [ coreBuiltin The_tuple0
           , coreBuiltin The_tuple1
           , coreBuiltin The_tuple2
           , coreBuiltin The_tuple3
           , coreBuiltin The_tuple4
           ]

{-
tupleReprCon :: Int -> Var
tupleReprCon n | n < 0 = internalError "tupleReprCon"
                   | n >= 5 = internalError "tupleReprCon: Unsupported size"
                   | otherwise = cons !! n
  where
    cons = [ coreBuiltin The_repr_Tuple0
           , coreBuiltin The_repr_Tuple1
           , coreBuiltin The_repr_Tuple2
           , coreBuiltin The_repr_Tuple3
           , coreBuiltin The_repr_Tuple4
           ]
-}

-- | Fully boxed wrappers around representation dictionaries for use by
--   the frontend
feTupleReprCon :: Int -> Var
feTupleReprCon n | n < 0 = internalError "feTupleReprCon"
                   | n >= 5 = internalError "feTupleReprCon: Unsupported size"
                   | otherwise = cons !! n
  where
    cons = [ coreBuiltin The_frontend_repr_Tuple0
           , coreBuiltin The_frontend_repr_Tuple1
           , coreBuiltin The_frontend_repr_Tuple2
           , coreBuiltin The_frontend_repr_Tuple3
           , coreBuiltin The_frontend_repr_Tuple4
           ]

-------------------------------------------------------------------------------
-- Initializing the builtins

the_CoreBuiltins :: MVar CoreBuiltins
{-# NOINLINE the_CoreBuiltins #-}
the_CoreBuiltins = unsafePerformIO newEmptyMVar

-- | Look up builtin variable names in the map
initializeBuiltins :: Map.Map String Var -> IO ()
initializeBuiltins name_environment = do
  -- Ensure that we haven't already initialized these
  bi_is_empty <- isEmptyMVar the_CoreBuiltins
  unless bi_is_empty $ internalError "Attempted to re-initialize core builtins"

  putStrLn "DEBUG: not forcing builtins"
  -- eval_builtins $ elems builtin_array
  putMVar the_CoreBuiltins builtin_array
  where
    -- Look up each builtin type and variable
    get_variable level name =
      case Map.lookup name name_environment
      of Just v
           | getLevel v == level -> v
           | otherwise -> internalError $
                          "Wrong level for builtin variable: " ++ name
         Nothing -> internalError $ "Missing builtin variable: " ++ name

    builtin_list =
      map (get_variable TypeLevel) builtinTypeNames ++
      map (get_variable ObjectLevel) builtinVariableNames

    builtin_array = listArray (0, num_builtins-1) builtin_list

    num_builtins = length builtinTypeNames + length builtinVariableNames

    -- Force evaluation of the entire list
    eval_builtins xs = foldr seq (return ()) xs
