{- Low-level routines for interaction between the Haskell and Python
-- runtimes.
--
-- * Conventions
--
-- When calling into Python, the result should be checked against NULL.
-- A NULL value indicates that an exception occurred.  Exceptions should be
-- re-thrown as a PythonExc.  The 'checkNull' function assists with this.
--
-- Most calls made from the Python interpreter expect a non-NULL PyPtr as
-- the return value, or NULL to signify an exception.  In the case an
-- exception is thrown, a Haskell function that may be called from Python
-- should catch it, ensure that an exception is been set in the Python
-- runtime, and return NULL.
-}

{-# LANGUAGE ForeignFunctionInterface,
             EmptyDataDecls,
             DeriveDataTypeable,
             BangPatterns #-}
module Python where

import Prelude hiding(catch)

import Control.Monad
import Control.Exception
import Data.Typeable
import Data.Int
import Foreign.C.String
import Foreign.C.Types
import Foreign.Marshal
import Foreign.Ptr
import Foreign.Storable

#undef _POSIX_C_SOURCE // Silences a warning. Defined in HsFFI.h and Python.h
#include <Python.h>

#if PY_MINOR_VERSION <= 5
type Py_ssize_t = CInt
#else
type Py_ssize_t = #{type Py_ssize_t}
#endif

-- Like mapM_, but also keep track of the current array index
mapMIndex_ :: Monad m => (Int -> a -> m b) -> [a] -> m ()
mapMIndex_ f xs = go 0 xs
    where
      go (!n) (x:xs) = do f n x
                          go (n + 1) xs
      go _ []        = return ()

-- Python objects
data PyObject
type PyPtr = Ptr PyObject

-- A class for data that can be marshaled to Python
class Python a where
    toPython :: a -> IO PyPtr

-------------------------------------------------------------------------------
-- Python exceptions

-- Indicates that an error occurred in the Python runtime.
-- The Python runtime has the details of the error.
data PythonExc = PythonExc deriving(Typeable)

instance Show PythonExc where
    show PythonExc = "Error in Python runtime"

instance Exception PythonExc

-- An exception type from Python.
newtype PythonExcType = PythonExcType {fromPythonExcType :: Ptr PyPtr}

foreign import ccall "Python.h &PyExc_RuntimeError"
    pyExc_RuntimeError :: Ptr PyPtr

foreign import ccall "Python.h &PyExc_TypeError"
    pyExc_TypeError :: Ptr PyPtr

pyRuntimeError :: PythonExcType
pyRuntimeError = PythonExcType pyExc_RuntimeError

pyTypeError :: PythonExcType
pyTypeError = PythonExcType pyExc_TypeError

foreign import ccall safe "Python.h PyErr_SetString"
    pyErr_SetString :: PyPtr -> CString -> IO ()

-- Raise an exception in the Python runtime.
setPythonExc :: PythonExcType -> String -> IO ()
setPythonExc exctypePtr msg =
    withCString msg $ \msgPtr -> do
      exctype <- peek (fromPythonExcType exctypePtr)
      pyErr_SetString exctype msgPtr
      
-- Raise an exception in the Python runtime and throw an exception.
throwPythonExc :: PythonExcType -> String -> IO a
throwPythonExc exctypePtr msg = do
  setPythonExc exctypePtr msg
  throwIO PythonExc

-- Raise an exception in the Python runtime and return a null pointer.
-- This function behaves as the Python interpreter expects from a C
-- function: set an exception, then return NULL.
raisePythonExc :: PythonExcType -> String -> IO PyPtr
raisePythonExc exctypePtr msg = do
  setPythonExc exctypePtr msg
  return nullPtr

-- Run some code and, if an exception is detected, marshal it as a
-- Python exception.
rethrowExceptionsInPython :: IO PyPtr -> IO PyPtr
rethrowExceptionsInPython m =
    -- If a Python exception is active, return NULL.
    -- If a Haskell exception is active, set a Python exception and
    -- return NULL.
    convertPythonExcToNull m `catch` fallbackHandler
    where
      fallbackHandler e =
          raisePythonExc pyRuntimeError (show (e :: SomeException))

-- Convenience function for running C/Python code that returns a PyPtr.
--
-- If the function returns NULL, this means a Python exception was raised, so
-- throw a Haskell exception.
checkNull :: IO PyPtr -> IO PyPtr
checkNull m = do p <- m
                 if p == nullPtr then throwIO PythonExc else return p

-- Run code and catch a Python error, if one occurred.
catchPythonExc :: IO a -> IO (Maybe a)
catchPythonExc m = liftM Just m `catch` \PythonExc -> return Nothing

-- Catch exceptions, and return NULL if an exception was caught.
convertPythonExcToNull :: IO PyPtr -> IO PyPtr
convertPythonExcToNull m = m `catch` \PythonExc -> return nullPtr

-------------------------------------------------------------------------------

foreign import ccall safe "Python.h Py_Initialize"
    py_Initialize :: IO ()

initializePython = py_Initialize

foreign import ccall "Python.h Py_Main"
    py_Main :: CInt -> Ptr CString -> IO CInt

runPythonMain :: String -> [String] -> IO CInt
runPythonMain progName args = do
  withCArgs (progName : args) $ \argc argv -> py_Main argc argv
  where
    -- Create a C array that acts like argv
    withCArgs args m =
      bracket (makeCArgs args) freeCArgs $ \(argc, argv) -> 
      m (fromIntegral argc) argv
    
    makeCArgs args = do 
      let argc = length args
      argv <- newArray =<< mapM newCString args
      return (argc, argv)
    
    freeCArgs (argc, argv) = do
      forM_ [0..argc - 1] $ \n -> freeElem n
      free argv
      where
        freeElem n = free =<< peekElemOff argv n

-------------------------------------------------------------------------------
-- Reference counting

foreign import ccall safe "Python.h Py_IncRef"
    py_IncRef :: PyPtr -> IO ()

foreign import ccall "Python.h Py_DecRef"
    py_DecRef :: PyPtr -> IO ()

-- Create a temporary Python object reference.
-- Decrement its reference count when leaving the scope, whether
-- normally or by an exception.
withPyPtr :: IO PyPtr -> (PyPtr -> IO a) -> IO a
withPyPtr m f = bracket m py_DecRef f

-- Like withPyPtr, but only decref on an exception.
withPyPtrExc :: IO PyPtr -> (PyPtr -> IO a) -> IO a
withPyPtrExc m f = bracketOnError m py_DecRef f

-- Convert an object to a Python object temporarily, and decrement its
-- reference count when done.
safeToPython :: Python a => a -> (PyPtr -> IO b) -> IO b
safeToPython x f = withPyPtr (toPython x) f

-- Like safeToPython, but only decrement the reference counter on an exception.
safeToPythonExc :: Python a => a -> (PyPtr -> IO b) -> IO b
safeToPythonExc x f = withPyPtrExc (toPython x) f

-------------------------------------------------------------------------------
-- Python objects

foreign import ccall "Python.h PyObject_IsInstance" py_IsInstance 
  :: PyPtr -> PyPtr -> IO CInt

isInstance :: PyPtr -> PyPtr -> IO Bool
x `isInstance` t = do
  n <- py_IsInstance x t
  case n of
    1 -> return True
    0 -> return False
    _ -> throwIO PythonExc      -- Other values indicate an error

foreign import ccall "Python.h &_Py_NoneStruct"
    py_None :: PyPtr

pyNone :: IO PyPtr
pyNone = do py_IncRef py_None
            return py_None

foreign import ccall "Python.h PyString_FromString"
    pyString_FromString :: CString -> IO PyPtr

stringToPython :: String -> IO PyPtr
stringToPython s = checkNull $ withCString s $ \p -> pyString_FromString p

foreign import ccall "Python.h PyString_AsString"
  pyString_AsString :: PyPtr -> IO CString
                       
fromPythonString :: PyPtr -> IO String
fromPythonString p = do
  s <- pyString_AsString p
  when (s == nullPtr) $ throwIO PythonExc
  peekCString s

newtype AsString = AsString String

foreign import ccall "Python.h PyInt_FromLong"
    pyInt_FromLong :: CLong -> IO PyPtr

foreign import ccall "Python.h PyNumber_Int"
  pyNumber_Int :: PyPtr -> IO PyPtr

foreign import ccall "Python.h PyInt_AsLong"
  pyInt_AsLong :: PyPtr -> IO CLong

fromPythonInt :: PyPtr -> IO Int
fromPythonInt p = do
  withPyPtr (checkNull $ pyNumber_Int p) $ \intp ->
    return . fromIntegral =<< pyInt_AsLong intp

instance Python Int where
    toPython n = pyInt_FromLong $ fromIntegral n

instance Python Integer where
    toPython n = pyInt_FromLong $ fromIntegral n

foreign import ccall "Python.h PyFloat_FromDouble"
    pyFloat_FromDouble :: CDouble -> IO PyPtr

instance Python Float where
    toPython d = pyFloat_FromDouble $ fromRational $ toRational d

instance Python Double where
    toPython d = pyFloat_FromDouble $ fromRational $ toRational d

foreign import ccall "Python.h &_Py_ZeroStruct"
    py_False :: PyPtr

foreign import ccall "Python.h &_Py_TrueStruct"
    py_True :: PyPtr

instance Python Bool where
    toPython b = do let bool = if b then py_True else py_False
                    py_IncRef bool
                    return bool

instance Python AsString where
    toPython (AsString s) = stringToPython s

newtype Eval = Eval (IO PyPtr)

instance Python Eval where
    toPython (Eval m) = m

foreign import ccall "Python.h PyList_New"
    pyList_New :: Py_ssize_t -> IO PyPtr

newList :: Int -> IO PyPtr
newList n = checkNull $ pyList_New (fromIntegral n)


-- | Function defined in Python_c.c, which just invokes the CPP macro 
-- \'PyList_Check\'.
foreign import ccall "PyList_Check_Function"
  pyList_Check :: PyPtr -> IO CInt
                  
isList :: PyPtr -> IO Bool
isList p = do
  liftM (0 /=) $ pyList_Check p

foreign import ccall "Python.h PyList_Size"
  pyList_Size :: PyPtr -> IO Py_ssize_t

getListSize :: PyPtr -> IO Int
getListSize xs = do
  n <- pyList_Size xs
  return $ fromIntegral n

foreign import ccall "Python.h PyList_SetItem"
    pyList_SetItem :: PyPtr -> Py_ssize_t -> PyPtr -> IO CInt

setListItem :: PyPtr -> Int -> PyPtr -> IO ()
setListItem list index obj = do
  rc <- pyList_SetItem list (fromIntegral index) obj
  when (rc == -1) $ throwIO PythonExc

-- Convert Haskell lists to Python lists
instance Python a => Python [a] where
    toPython xs =
        withPyPtrExc (newList $ length xs) $ \list ->
            let marshalItem index x =
                    safeToPythonExc x $ setListItem list index
            in do mapMIndex_ marshalItem xs
                  return list

foreign import ccall "Python.h PyList_GetItem"
  pyList_GetItem :: PyPtr -> Py_ssize_t -> IO PyPtr
                    
-- | Get a borrowed reference to the n_th list item.
getListItem :: PyPtr -> Int -> IO PyPtr
getListItem xs n = do
  checkNull $ pyList_GetItem xs (fromIntegral n)

foreign import ccall "Python.h PyDict_New"
    pyDict_New :: IO PyPtr

foreign import ccall "Python.h PyDict_SetItem"
    pyDict_SetItem :: PyPtr -> PyPtr -> PyPtr -> IO CInt

setDictItem :: PyPtr -> PyPtr -> PyPtr -> IO ()
setDictItem dict key val = do
  rc <- pyDict_SetItem dict key val
  when (rc /= 0) $ throwIO PythonExc

foreign import ccall "Python.h PyTuple_New"
    pyTuple_New :: Py_ssize_t -> IO PyPtr

newTuple :: Int -> IO PyPtr
newTuple n = checkNull $ pyTuple_New (fromIntegral n)

foreign import ccall "Python.h PyTuple_Check_Function"
  pyTuple_Check :: PyPtr -> IO CInt

isTuple p = liftM (/= 0) $ pyTuple_Check p

foreign import ccall "Python.h PyTuple_SetItem"
    pyTuple_SetItem :: PyPtr -> Py_ssize_t -> PyPtr -> IO CInt

setTupleItem :: PyPtr -> Int -> PyPtr -> IO ()
setTupleItem tup index obj = do
  rc <- pyTuple_SetItem tup (fromIntegral index) obj
  when (rc /= 0) $ throwIO PythonExc

-- Convert Haskell tuples to Python tuples
toPythonTuple :: [IO PyPtr] -> IO PyPtr
toPythonTuple xs =
    withPyPtrExc (newTuple $ length xs) $ \tuple ->
        let marshalItem index x =
                withPyPtrExc x $ setTupleItem tuple index
        in do mapMIndex_ marshalItem xs
              return tuple

instance (Python a, Python b) => Python (a, b) where
    toPython (x, y) =
        toPythonTuple [toPython x, toPython y]

instance (Python a, Python b, Python c) => Python (a, b, c) where
    toPython (x, y, z) =
        toPythonTuple [toPython x, toPython y, toPython z]

foreign import ccall "Python.h PyTuple_GetItem"
  pyTuple_GetItem :: PyPtr -> Py_ssize_t -> IO PyPtr

-- | Get a borrowed reference to the n_th tuple item.
getTupleItem :: PyPtr -> Int -> IO PyPtr
getTupleItem ptr n = do
  checkNull $ pyTuple_GetItem ptr (fromIntegral n)

foreign import ccall "Python.h PyObject_CallObject"
  pyObject_CallObject :: PyPtr -> PyPtr -> IO PyPtr

call0 :: PyPtr -> IO PyPtr
call0 ptr = checkNull $ pyObject_CallObject ptr nullPtr

call1 :: Python a => PyPtr -> a -> IO PyPtr
call1 ptr a = withPyPtr (toPythonTuple [toPython a]) $ \tuple ->
              checkNull $ pyObject_CallObject ptr tuple

call2 :: (Python a, Python b) => PyPtr -> a -> b -> IO PyPtr
call2 ptr a b = withPyPtr (toPythonTuple [toPython a, toPython b]) $ \tuple ->
                checkNull $ pyObject_CallObject ptr tuple

call3 :: (Python a, Python b, Python c) => PyPtr -> a -> b -> c -> IO PyPtr
call3 ptr a b c = withPyPtr (toPythonTuple [ toPython a
                                           , toPython b
                                           , toPython c]) $ \tuple ->
                  checkNull $ pyObject_CallObject ptr tuple

call4 :: (Python a, Python b, Python c, Python d) =>
         PyPtr -> a -> b -> c -> d -> IO PyPtr
call4 ptr a b c d = withPyPtr (toPythonTuple [ toPython a
                                             , toPython b
                                             , toPython c
                                             , toPython d]) $ \tuple ->
                    checkNull $ pyObject_CallObject ptr tuple

foreign import ccall "Python.h PyImport_ImportModule"
  pyImport_ImportModule :: CString -> IO PyPtr

importModule :: String -> IO PyPtr
importModule name =
    checkNull $ withCString name $ \ptr -> pyImport_ImportModule ptr

foreign import ccall "Python.h PyObject_GetAttrString"
  pyObject_GetAttrString :: PyPtr -> CString -> IO PyPtr

getAttr :: PyPtr -> String -> IO PyPtr
getAttr obj name = checkNull $ withCString name $ \cName ->
                   pyObject_GetAttrString obj cName

foreign import ccall "Python.h PyMapping_GetItemString"
  pyMapping_GetItemString :: PyPtr -> CString -> IO PyPtr

getItemString :: PyPtr -> String -> IO PyPtr
getItemString obj name = checkNull $ withCString name $ \cName ->
                         pyMapping_GetItemString obj cName

foreign import ccall "Python.h PyEval_GetBuiltins"
  pyEval_GetBuiltins :: IO PyPtr

getBuiltins = pyEval_GetBuiltins
