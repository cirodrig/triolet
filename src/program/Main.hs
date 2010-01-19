
{-# LANGUAGE ForeignFunctionInterface #-}
module Main where

import System.Environment
import System.IO
import Python

-- Defined in Main_c.c
foreign import ccall createHaskellModule :: IO ()

-- Defined in Gluon_c.c
foreign import ccall createGluonModule :: IO ()

-- Main: initialize Python runtime and
-- launch the interpreter
main = do
  progName <- getProgName
  args <- getArgs
  
  -- Initialize Python
  initializePython
  
  -- Create Python modules and initialize Gluon
  createHaskellModule
  createGluonModule
  
  -- Run interpreter
  runPythonMain progName args