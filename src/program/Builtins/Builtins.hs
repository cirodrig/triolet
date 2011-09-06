
{-# LANGUAGE TemplateHaskell #-}
module Builtins.Builtins where

import Control.Concurrent.MVar
import Control.Monad
import Data.Array
import System.IO.Unsafe

import Language.Haskell.TH
import Common.Supply
import Common.Identifier
import Common.Error
import Common.Label

import Builtins.BuiltinsTH
import Type.Type

-- | The built-in variables are stored in an array
type PyonBuiltins = Array Int Var

$(do let cons = [mkName ("The_" ++ nm)
                | nm <- pyonBuiltinTypeNames ++ pyonBuiltinVariableNames]
         num_cons = length cons
         con_decls = [return $ NormalC c [] | c <- cons]

     -- Declare a data type
     data_decl <-
       dataD (cxt []) (mkName "BuiltinThing") [] con_decls [mkName "Enum"]

     -- Declare a function to initialize the global variable
     initializer_decl <-
       [d| createBuiltins var_ids = do
             type_vars <-
               mapM (mk_builtin_var TypeLevel) pyonBuiltinTypeNames
             obj_vars <-
               mapM (mk_builtin_var ObjectLevel) pyonBuiltinVariableNames
             return $ listArray (0, num_cons - 1) (type_vars ++ obj_vars)
             where
               mk_builtin_var lv nm = do
                 var_id <- supplyValue var_ids
                 return $ mkVar var_id (Just $ builtinLabel nm) lv
       |]
     return $ data_decl : initializer_decl)

allBuiltinVars :: [Var]
allBuiltinVars = elems builtins
  where
    builtins = unsafePerformIO $ do
      -- Ensure that we've already initialized these
      bi_is_empty <- isEmptyMVar the_PyonBuiltins
      when bi_is_empty $ internalError "Pyon builtins are uninitialized"

      readMVar the_PyonBuiltins

pyonBuiltin :: BuiltinThing -> Var
pyonBuiltin field = unsafePerformIO $ do
  -- Ensure that we've already initialized these
  bi_is_empty <- isEmptyMVar the_PyonBuiltins
  when bi_is_empty $ internalError "Pyon builtins are uninitialized"
  
  -- Load and return the desired field
  bi <- readMVar the_PyonBuiltins
  return $ bi ! fromEnum field

infix 4 `isPyonBuiltin`
isPyonBuiltin :: Var -> BuiltinThing -> Bool
v `isPyonBuiltin` name = v == pyonBuiltin name

pyonTupleTypeCon :: Int -> Var
pyonTupleTypeCon n | n < 0 = internalError "pyonTupleTypeCon"
                   | n >= 5 = internalError "pyonTupleTypeCon: Unsupported size"
                   | otherwise = cons !! n
  where
    cons = [ pyonBuiltin The_PyonTuple0
           , pyonBuiltin The_PyonTuple1
           , pyonBuiltin The_PyonTuple2
           , pyonBuiltin The_PyonTuple3
           , pyonBuiltin The_PyonTuple4
           ]

pyonTupleCon :: Int -> Var
pyonTupleCon n | n < 0 = internalError "pyonTupleCon"
               | n >= 5 = internalError $ "pyonTupleCon: Unsupported size"
               | otherwise = cons !! n
  where
    cons = [ pyonBuiltin The_pyonTuple0
           , pyonBuiltin The_pyonTuple1
           , pyonBuiltin The_pyonTuple2
           , pyonBuiltin The_pyonTuple3
           , pyonBuiltin The_pyonTuple4
           ]

isPyonTupleCon :: Var -> Bool
isPyonTupleCon v = v `elem` cons
  where
    cons = [ pyonBuiltin The_pyonTuple0
           , pyonBuiltin The_pyonTuple1
           , pyonBuiltin The_pyonTuple2
           , pyonBuiltin The_pyonTuple3
           , pyonBuiltin The_pyonTuple4
           ]

pyonTupleReprCon :: Int -> Var
pyonTupleReprCon n | n < 0 = internalError "pyonTupleReprCon"
                   | n >= 5 = internalError "pyonTupleReprCon: Unsupported size"
                   | otherwise = cons !! n
  where
    cons = [ pyonBuiltin The_repr_PyonTuple0
           , pyonBuiltin The_repr_PyonTuple1
           , pyonBuiltin The_repr_PyonTuple2
           , pyonBuiltin The_repr_PyonTuple3
           , pyonBuiltin The_repr_PyonTuple4
           ]

-------------------------------------------------------------------------------
-- Initializing the builtins

the_PyonBuiltins :: MVar PyonBuiltins
{-# NOINLINE the_PyonBuiltins #-}
the_PyonBuiltins = unsafePerformIO newEmptyMVar

initializeBuiltins :: IdentSupply Var -> IO ()
initializeBuiltins id_supply = do
  -- Ensure that we haven't already initialized these
  bi_is_empty <- isEmptyMVar the_PyonBuiltins
  unless bi_is_empty $ internalError "Attempted to re-initialize Pyon builtins"

  bi <- createBuiltins id_supply
  putMVar the_PyonBuiltins bi
