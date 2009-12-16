-- The parser driver.  This exports a function to be called via C.
-- The driver function takes a filename, reads the file, and returns a
-- Python object.

{-# LANGUAGE ForeignFunctionInterface #-}
module Parser.Driver() where

import Prelude hiding(catch)
import Control.Exception
import Foreign.C.String
import System.Environment
import System.IO
import System.IO.Error hiding(catch)
import Python
import Parser.Parser
import Parser.Output

foreign export ccall parsePyonFile :: CString -> IO PyPtr

-- Read and parse a Pyon file.  On success, a pointer to a Python
-- object is returned.
parsePyonFile filename_ptr = rethrowExceptionsInPython $ do
  filename <- peekCString filename_ptr
  parseFile filename

-- Parse a Pyon file.  On parser error, raise an exception.
parseFile inPath = do
  text <- readFile inPath
  case parseModule text inPath of
    Left errs  -> raisePythonExc pyRuntimeError (head errs)
    Right defs -> case defs
                  of (n, mod) -> runExport $ toPythonEx (Inherit n, mod)

