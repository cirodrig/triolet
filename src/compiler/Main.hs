
{-# LANGUAGE ForeignFunctionInterface #-}
module Main where

import System.IO
import Python

-- Defined in Main_c.c
foreign import ccall createHaskellModule :: IO ()

-- Main: initialize Python runtime and
-- launch the interpreter
main = do
  initializePython
  createHaskellModule
  runPythonMain