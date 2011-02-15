
{-# LANGUAGE TemplateHaskell #-}
module Builtins.Builtins where

import Control.Concurrent.MVar
import Control.Monad
import System.IO.Unsafe

import Language.Haskell.TH(Strict(..), listE, varE, mkName)
import Common.THRecord
import Common.Supply
import Common.Identifier
import Common.Error
import Common.Label

import Builtins.BuiltinsTH
import Type.Type

$(do d <- declareRecord pyonBuiltinsSpecification
     return [d])

$(do declareFieldReaders pyonBuiltinsSpecification "the")

allBuiltinVars :: [Var]
allBuiltinVars =
  $(listE [ [| $(varE (mkName $ '_' : nm)) builtins |]
             | nm <- pyonBuiltinTypeNames ++ pyonBuiltinVariableNames])
  where
    builtins = unsafePerformIO $ do
      -- Ensure that we've already initialized these
      bi_is_empty <- isEmptyMVar the_PyonBuiltins
      when bi_is_empty $ internalError "Pyon builtins are uninitialized"

      readMVar the_PyonBuiltins

pyonBuiltin :: (PyonBuiltins -> a) -> a
pyonBuiltin field = unsafePerformIO $ do
  -- Ensure that we've already initialized these
  bi_is_empty <- isEmptyMVar the_PyonBuiltins
  when bi_is_empty $ internalError "Pyon builtins are uninitialized"
  
  -- Load and return the desired field
  bi <- readMVar the_PyonBuiltins
  return $ field bi

infix 4 `isPyonBuiltin`
isPyonBuiltin :: Var -> (PyonBuiltins -> Var) -> Bool
v `isPyonBuiltin` name = v == pyonBuiltin name

pyonTupleTypeCon :: Int -> Var
pyonTupleTypeCon n | n < 0 = internalError "pyonTupleTypeCon"
                   | n >= 5 = internalError "pyonTupleTypeCon: Unsupported size"
                   | otherwise = cons !! n
  where
    cons = [ pyonBuiltin the_PyonTuple0
           , pyonBuiltin the_PyonTuple1
           , pyonBuiltin the_PyonTuple2
           , pyonBuiltin the_PyonTuple3
           , pyonBuiltin the_PyonTuple4
           ]

pyonTupleCon :: Int -> Var
pyonTupleCon n | n < 0 = internalError "pyonTupleCon"
               | n >= 5 = internalError $ "pyonTupleCon: Unsupported size"
               | otherwise = cons !! n
  where
    cons = [ pyonBuiltin the_pyonTuple0
           , pyonBuiltin the_pyonTuple1
           , pyonBuiltin the_pyonTuple2
           , pyonBuiltin the_pyonTuple3
           , pyonBuiltin the_pyonTuple4
           ]

isPyonTupleCon :: Var -> Bool
isPyonTupleCon v = v `elem` cons
  where
    cons = [ pyonBuiltin the_pyonTuple0
           , pyonBuiltin the_pyonTuple1
           , pyonBuiltin the_pyonTuple2
           , pyonBuiltin the_pyonTuple3
           , pyonBuiltin the_pyonTuple4
           ]

pyonTupleReprCon :: Int -> Var
pyonTupleReprCon n | n < 0 = internalError "pyonTupleReprCon"
                   | n >= 5 = internalError "pyonTupleReprCon: Unsupported size"
                   | otherwise = cons !! n
  where
    cons = [ pyonBuiltin the_repr_PyonTuple0
           , pyonBuiltin the_repr_PyonTuple1
           , pyonBuiltin the_repr_PyonTuple2
           , pyonBuiltin the_repr_PyonTuple3
           , pyonBuiltin the_repr_PyonTuple4
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

mk_builtin_var supply nm lv = do
  var_id <- supplyValue supply
  return $ mkVar var_id (Just $ builtinLabel nm) lv

createBuiltins :: IdentSupply Var -> IO PyonBuiltins
createBuiltins id_supply =
  $(let initializers = [ ('_':nm, [| mk_builtin_var id_supply nm TypeLevel |])
                       | nm <- pyonBuiltinTypeNames] ++
                       [ ('_':nm, [| mk_builtin_var id_supply nm ObjectLevel |])
                       | nm <- pyonBuiltinVariableNames]
    in initializeRecordM pyonBuiltinsSpecification initializers)
