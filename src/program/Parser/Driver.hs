-- The parser driver.  This exports a function to be called via C.
-- The driver function takes a filename, reads the file, and returns a
-- Python object.

{-# LANGUAGE ForeignFunctionInterface #-}
module Parser.Driver() where

import Prelude hiding(catch)
import Control.Exception
import Control.Monad
import Foreign.C.Types
import Foreign.C.String
import System.Environment
import System.IO
import System.IO.Error hiding(catch)
import Python
import Parser.Parser
import Parser.Output

foreign export ccall parsePyonFile :: CString
                                   -> PyPtr
                                   -> CInt
                                   -> IO PyPtr

readGlobalsList :: PyPtr -> IO [(String, Int)]
readGlobalsList globals = do
  is_list <- isList globals
  unless is_list $ throwPythonExc pyTypeError "Expecting a list" 
  sz <- getListSize globals
  
  mapM fromListItem [0 .. sz - 1]
  where
    -- Exceptions may occur in this code, so take care not to adjust
    -- Python reference counts
    fromListItem index = do
      item <- getListItem globals index
      is_tuple <- isTuple item
      unless is_tuple $ throwPythonExc pyTypeError "Expecting a list of tuples"
      
      s <- fromPythonString =<< getTupleItem item 0
      n <- fromPythonInt =<< getTupleItem item 1
      return (s, n)

-- Read and parse a Pyon file.  On success, a pointer to a Python
-- object is returned.
parsePyonFile filename_ptr globals_ptr next_id = 
  rethrowExceptionsInPython $ do
    -- Marshal filename
    filename <- peekCString filename_ptr

    -- Marshal global names
    globals <- readGlobalsList globals_ptr

    -- Marshal next ID
    let next_id' = fromIntegral next_id
    parseFile filename globals next_id'

-- Parse a Pyon file.  On parser error, raise an exception.
parseFile inPath globals nextID = do
  text <- readFile inPath
  case parseModule text inPath globals nextID of
    Left errs  -> raisePythonExc pyRuntimeError (head errs)
    Right defs -> case defs
                  of (n, mod) -> runExport $ toPythonEx (Inherit n, mod)

