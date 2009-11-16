
module Main where

import Prelude hiding(catch)
import Control.Exception
import System.Environment
import System.IO
import System.IO.Error hiding(catch)
import Parser
import Python
import PythonPrint

parseArgs [filePath] = return filePath
parseArgs _          = fail "Expecting one command-line argument"

putResult (Left errs) = toPython (map showErrorString errs)
putResult (Right defs) = toPython defs

showErrorString e =
    Eval $ call1 (readEnv py_RuntimeError) (AsString e)


-- Main:
-- Read a file name from command line, parse the file, and write the result
-- to stdout.  The result is written as a Python expression. 
main :: IO PyPtr
main = do args <- getArgs
          initializePython
          hSetBuffering stdout LineBuffering -- for debugging
          inPath <- parseArgs args
          catchJust isFileException (parseFile inPath) fileErrorHandler `catch`
                    fallbackErrorHandler
    where
      parseFile inPath = do
        text <- readFile inPath
        let outputExpression = parseModule text inPath
        putResult outputExpression

      isFileException e
          | or $ map ($ ioeGetErrorType e)
            [ isDoesNotExistErrorType
            , isPermissionErrorType
            , isAlreadyInUseErrorType] = Just e
          | otherwise = Nothing

      -- Error opening file: create an error object
      fileErrorHandler e = toPython (showErrorString $ show e)

      -- Run the fallback error handler for any uncaught errors
      fallbackErrorHandler e = toPython (showErrorString $ show (e :: SomeException))
          