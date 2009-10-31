
module Main where

import Control.Exception
import System.Environment
import System.IO
import System.IO.Error
import Parser
import PythonPrint

parseArgs [filePath] = return filePath
parseArgs _          = fail "Expecting one command-line argument"

showResult (Left errs) = showPythonList (map showErrorString errs)
showResult (Right defs) = pyShow defs

showErrorString e = PyFunCall "RuntimeError" [P (PyShowString e)]


-- Main:
-- Read a file name from command line, parse the file, and write the result
-- to stdout.  The result is written as a Python expression. 
main = do args <- getArgs
          inPath <- parseArgs args
          catchJust isFileException (parseFile inPath) fileErrorHandler
    where
      parseFile inPath = do
        text <- readFile inPath
        let outputExpression = showResult (parseModule text inPath) ""
        putStrLn outputExpression

      isFileException e
          | or $ map ($ ioeGetErrorType e)
            [ isDoesNotExistErrorType
            , isPermissionErrorType
            , isAlreadyInUseErrorType] = Just e
          | otherwise = Nothing

      -- Error opening file: create an error object
      fileErrorHandler e = putStrLn $ pyShow (showErrorString $ show e) ""
