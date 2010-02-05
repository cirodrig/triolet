
{-# LANGUAGE ForeignFunctionInterface #-}
module Main where

import Control.Monad
import Foreign.C.Types
import System.Environment
import System.Exit
import System.IO
import PythonInterface.Python

-- Defined in Main_c.c
foreign import ccall createHaskellModule :: IO ()

-- Defined in Gluon_c.c
foreign import ccall createGluonModule :: IO CInt

-- Main: initialize Python runtime and
-- launch the interpreter
main = do
  progName <- getProgName
  args <- getArgs
  
  -- Initialize Python
  initializePython
  
  -- Create Python modules and initialize Gluon
  createHaskellModule
  rc <- createGluonModule
  when (rc == 0) $ do putStrLn "Could not initialize Gluon module"
                      exitFailure
  
  -- Run interpreter
  runPythonMain progName args