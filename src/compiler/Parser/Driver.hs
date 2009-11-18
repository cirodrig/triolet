-- The parser driver.  This exports a function to C.
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

parsePyonFile filename_ptr = throwAsPythonException $ do
  filename <- peekCString filename_ptr
  parseFile filename

parseFile inPath = do
  text <- readFile inPath
  case parseModule text inPath of
    Left errs  -> runExport $ toPythonEx (Inherit $ AsString $ head errs)
    Right defs -> runExport $ toPythonEx defs

