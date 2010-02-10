
{-# LANGUAGE ForeignFunctionInterface #-}
module Main(main) where

import Control.Monad
import Foreign.C.Types
import System.Environment
import System.Exit
import System.IO
import PythonInterface.Python

-- Defined in Main_c.c
foreign import ccall createHaskellModule :: IO ()

-- Defined in Gluon_c.c
foreign import ccall createGluonModule :: IO Bool

-- Defined in SystemF_c.c
foreign import ccall createSystemFModule :: IO Bool

-- Try to load a module; exit on error
tryLoad :: String -> IO Bool -> IO ()
tryLoad moduleName loader = do
  rc <- loader
  unless rc $ do 
    putStrLn $ "Could not initialize module '" ++ moduleName ++ "'"
    exitFailure

-- Main: initialize Python runtime and
-- launch the interpreter
main = do
  progName <- getProgName
  args <- getArgs
  
  -- Initialize Python
  initializePython
  
  -- Create Python modules and initialize Gluon
  createHaskellModule
  tryLoad "gluon" createGluonModule
  tryLoad "system_f" createSystemFModule

  -- Run interpreter
  runPythonMain progName args