
{-# LANGUAGE TemplateHaskell #-}
module Builtins.Builtins where

import Control.Concurrent.MVar
import Control.Monad
import System.IO.Unsafe

import Language.Haskell.TH(Strict(..), listE, varE, mkName)
import Gluon.Common.THRecord
import Gluon.Common.Supply
import Gluon.Common.Identifier
import Gluon.Common.Error
import Gluon.Core.Level

import Builtins.BuiltinsTH
import LowLevel.Label
import Type.Var

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
