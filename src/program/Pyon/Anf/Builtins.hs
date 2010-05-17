
{-# LANGUAGE TemplateHaskell #-}
module Pyon.Anf.Builtins
       {-(AnfBuiltins,
        anfBuiltin, isAnfBuiltin,
        loadAnfBuiltins,
        the_Ptr,
        the_Undef,
        the_Action,
        the_copy,
        the_reading,
        the_local,
        the_elim_bool,
        the_elim_PyonTuple2,
        the_PassConv_int,
        the_PassConv_float,
        the_PassConv_PyonTuple2,
        the_store_int,
        the_store_float,
        the_store_bool,
        the_store_NoneType
       ) -}
where

import Control.Concurrent.MVar
import Control.Exception
import Control.Monad
import Data.List 
import System.FilePath
import System.IO.Unsafe

import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.Label
import Gluon.Common.THRecord
import Gluon.Core
import Gluon.Core.Module
import Gluon.Parser.Driver
import Gluon.Parser.Setup
import Pyon.Anf.BuiltinsTH
import Paths_pyon

$(do d <- declareRecord anfBuiltinsSpecification
     return [d])

$(do declareFieldReaders anfBuiltinsSpecification "the")
$(do declareFieldWriters anfBuiltinsSpecification "setThe")

the_AnfBuiltins :: MVar AnfBuiltins
{-# NOINLINE the_AnfBuiltins #-}
the_AnfBuiltins = unsafePerformIO newEmptyMVar

anfBuiltin :: (AnfBuiltins -> a) -> a
anfBuiltin field = unsafePerformIO $ do
  -- Ensure that we've already initialized these
  bi_is_empty <- isEmptyMVar the_AnfBuiltins
  when bi_is_empty $ internalError "Anf builtins are uninitialized"
  
  -- Load and return the desired field
  bi <- readMVar the_AnfBuiltins
  return $ field bi

infix 4 `isAnfBuiltin`
isAnfBuiltin :: Con -> (AnfBuiltins -> Con) -> Bool
c `isAnfBuiltin` name = c == anfBuiltin name

findConByName mod name =
  let label = pgmLabel anfBuiltinModuleName name
  in case find ((label ==) . conName) $ getConstructors mod
     of Just c  -> c
        Nothing -> internalError $ "Missing Anf builtin '" ++ name ++ "'"
  where
    getConstructors mod = concat [c : conCtors c | c <- moduleConstructors mod]

initializeAnfBuiltins :: Module () -> IO ()
initializeAnfBuiltins mod = do
  -- Must not have been initialized yet
  is_empty <- isEmptyMVar the_AnfBuiltins
  unless is_empty $ fail "Cannot re-initialize anf builtins"

  -- Load and create builtins
  bi <-
    $(let assign_ctor_field fname name =
            (fname, [| evaluate $ findConByName mod name |])
          initializers =
            zipWith assign_ctor_field
            anfBuiltinConstructorNames anfBuiltinConstructors
      in initializeRecordM anfBuiltinsSpecification initializers)
  
  putMVar the_AnfBuiltins bi

areAnfBuiltinsInitialized :: IO Bool
areAnfBuiltinsInitialized =
  liftM not $ isEmptyMVar the_AnfBuiltins

loadAnfBuiltins :: IdentSupply Var
                -> IdentSupply Con
                -> Module ()
                -> IO (Maybe (Module ()))
loadAnfBuiltins varIDs conIDs builtins = do
  let setup = contextParserSetup varIDs conIDs [builtins]
  fileName <- getDataFileName ("library"</>"AnfBuiltin.glu")
  m <- loadSourceFile setup fileName
  case m of
    Just cu -> do initializeAnfBuiltins cu
                  return $ Just cu
    Nothing -> return Nothing
