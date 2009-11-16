
{-# LANGUAGE ForeignFunctionInterface, EmptyDataDecls, DeriveDataTypeable #-}
module Python where

import Prelude hiding(catch)

import Control.Monad
import Control.Exception
import Data.Typeable
import Foreign.C.String
import Foreign.C.Types
import Foreign.Ptr

data PyObject

type PyPtr = Ptr PyObject

#include <Python.h>

#if PY_MINOR_VERSION <= 5
type Py_ssize_t = CInt
#else
type Py_ssize_t = #{type Py_ssize_t}
#endif

-- Indicates that an error occurred in the Python runtime.
-- The Python runtime has the details of the error.
data PythonErr = PythonErr deriving(Typeable)

instance Show PythonErr where
    show PythonErr = "Error in Python runtime"

instance Exception PythonErr

foreign import ccall safe "Python.h Py_Initialize"
    py_Initialize :: IO ()

initializePython = py_Initialize

foreign import ccall safe "Python.h Py_IncRef"
    py_IncRef :: PyPtr -> IO ()

foreign import ccall "Python.h Py_DecRef"
    py_DecRef :: PyPtr -> IO ()

checkNull :: IO PyPtr -> IO PyPtr
checkNull m = do p <- m
                 if p == nullPtr then throwIO PythonErr else return p

-- Data that can be marshaled to Python
class Python a where
    toPython :: a -> IO PyPtr

-- Create a temporary Python object reference.
-- Decrement its reference count when leaving the scope, whether
-- normally or by an exception.
withPyPtr :: IO PyPtr -> (PyPtr -> IO a) -> IO a
withPyPtr m f = bracket m py_DecRef f

-- Like withPyPtr, but only decref on an exception.
withPyPtrExc :: IO PyPtr -> (PyPtr -> IO a) -> IO a
withPyPtrExc m f = bracketOnError m py_DecRef f

-- Run code and catch a Python error, if one occurred.
catchPythonErr :: IO a -> IO (Maybe a)
catchPythonErr m = liftM Just m `catch` \PythonErr -> return Nothing

-- Convert an object to a Python object temporarily, and decrement its
-- reference count when done.
safeToPython :: Python a => a -> (PyPtr -> IO b) -> IO b
safeToPython x f = withPyPtr (toPython x) f

safeToPythonExc :: Python a => a -> (PyPtr -> IO b) -> IO b
safeToPythonExc x f = withPyPtrExc (toPython x) f

foreign import ccall "Python.h _Py_NoneStruct"
    py_None :: PyPtr

pyNone :: IO PyPtr
pyNone = do py_IncRef py_None
            return py_None

foreign import ccall "Python.h PyString_FromString"
    pyString_FromString :: CString -> IO PyPtr

stringToPython :: String -> IO PyPtr
stringToPython s = checkNull $ withCString s $ \p -> pyString_FromString p

newtype AsString = AsString String

foreign import ccall "Python.h PyInt_FromLong"
    pyInt_FromLong :: CLong -> IO PyPtr

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

foreign import ccall "Python.h _Py_ZeroStruct"
    py_False :: PyPtr

foreign import ccall "Python.h _Py_TrueStruct"
    py_True :: PyPtr

instance Python Bool where
    toPython b = let bool = if b then py_True else py_False
                 in do py_IncRef bool
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

foreign import ccall "Python.h PyList_SetItem"
    pyList_SetItem :: PyPtr -> Py_ssize_t -> PyPtr -> IO CInt

setListItem :: PyPtr -> Int -> PyPtr -> IO ()
setListItem list index obj = do
  rc <- pyList_SetItem list (fromIntegral index) obj
  when (rc == -1) $ throwIO PythonErr

-- Convert Haskell lists to Python lists
instance Python a => Python [a] where
    toPython xs =
        withPyPtrExc (newList $ length xs) $ \list ->
            let marshalItems index (x:xs) = do
                    safeToPythonExc x $ setListItem list index
                    marshalItems (index + 1) xs
                marshalItems _ [] = return ()
            in do marshalItems 0 xs
                  return list

foreign import ccall "Python.h PyTuple_New"
    pyTuple_New :: Py_ssize_t -> IO PyPtr

newTuple :: Int -> IO PyPtr
newTuple n = checkNull $ pyTuple_New (fromIntegral n)

foreign import ccall "Python.h PyTuple_SetItem"
    pyTuple_SetItem :: PyPtr -> Py_ssize_t -> PyPtr -> IO CInt

setTupleItem :: PyPtr -> Int -> PyPtr -> IO ()
setTupleItem tup index obj = do
  rc <- pyTuple_SetItem tup (fromIntegral index) obj
  when (rc /= 0) $ throwIO PythonErr

-- Convert Haskell tuples to Python tuples
toPythonTuple :: [IO PyPtr] -> IO PyPtr
toPythonTuple xs =
    withPyPtrExc (newTuple $ length xs) $ \tuple ->
        let marshalItems index (x:xs) = do
              withPyPtrExc x $ setTupleItem tuple index
              marshalItems (index + 1) xs
            marshalItems _ [] = return ()
        in do marshalItems 0 xs
              return tuple

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

foreign import ccall "Python.h PyEval_GetBuiltins"
  pyEval_GetBuiltins :: IO PyPtr

getBuiltins = pyEval_GetBuiltins