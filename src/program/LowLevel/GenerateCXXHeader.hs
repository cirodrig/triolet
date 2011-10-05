
{-# LANGUAGE ForeignFunctionInterface #-}
module LowLevel.GenerateCXXHeader
       (hasCXXExports, writeCxxHeader)
where

import Foreign.C.Types
import Foreign.C.String
import Foreign.Ptr
import System.IO
import System.Posix
import System.Posix.IO

import Common.Error
import CxxInterface.SignatureHS
import LowLevel.Syntax
import Export

data FILE

foreign import ccall fdopen :: CInt -> CString -> IO (Ptr FILE)
foreign import ccall fclose :: Ptr FILE -> IO ()

-- | Get the module's exported C++ functions
cxxExports :: Module -> [(Var, CXXSignature)]
cxxExports m = [(v, s) | (v, CXXExportSig s) <- moduleExports m]

hasCXXExports :: Module -> Bool
hasCXXExports m = not $ null $ cxxExports m

-- | Write wrapper functions to a C++ header file.  The handle is closed
--   by this operation.
writeCxxHeader :: Module -> Handle -> IO ()
writeCxxHeader mod hdl = do
  -- Convert handle to a "FILE *"
  fd <- handleToFd hdl
  let Fd fd_int = fd
  file_ptr <- withCString "w" $ \str -> fdopen fd_int str
  mapM_ (writeCxxWrapper file_ptr) $ cxxExports mod
  fclose file_ptr

-- | The C function that generates wrapper code for one function.
--
--   Arguments are:
--
--   * File to write to
--   * Pyon function name
--   * Wrapper function name
--   * The function type
foreign import ccall printCxxFunction ::
  Ptr FILE -> CString -> CString -> Ptr PyonSignature -> IO ()

-- | Write one wrapper function to a C++ header file
writeCxxWrapper :: Ptr FILE -> (Var, CXXSignature) -> IO ()
writeCxxWrapper file (pyon_var, CXXSignature wrapper_name domain range) = do
  -- Get the name of the function that the wrapper will call
  let pyon_function_name = mangledVarName False pyon_var
  
  -- Marshal data and call the wraper generator
  withCString pyon_function_name $ \c_pyon_function_name ->
    withCString wrapper_name $ \c_wrapper_name -> do
      c_signature <- sendExportSig domain range
      printCxxFunction file c_pyon_function_name c_wrapper_name c_signature
      pyonSignature_destroy c_signature
      