-- Code for creating Python-to-Haskell references.

{-# LANGUAGE ForeignFunctionInterface #-}
module PythonInterface.HsObject where

import Control.Monad
import Data.Typeable
import Foreign.StablePtr
import Foreign.Storable
import Python

#include "PythonInterface/HsObject.h"

foreign import ccall "HsObject.h &HsObject_type" hsObject_type :: PyPtr

foreign import ccall "HsObject.h HsObject_new" hsObject_new 
  :: StablePtr a -> StablePtr TypeRep -> IO PyPtr
     
-- | Create a new Python reference to the given value 
newHsObject :: Typeable a => a -> IO PyPtr
newHsObject x = do
  x_ptr <- newStablePtr x
  x_type_ptr <- newStablePtr (typeOf x)
  hsObject_new x_ptr x_type_ptr

-- | Extract a Haskell value of type 'a' from the given object,
-- which must be an HsObject (this property is not checked).
-- Reference counts are not adjusted.
fromHsObject :: Typeable a => PyPtr -> IO (Maybe a)
fromHsObject x = do
  return_type <- return undefined
  type_rep_ptr <- #{peek struct HsObject, type_rep} x
  type_rep <- deRefStablePtr type_rep_ptr
  if type_rep /= typeOf return_type then return Nothing else do
    value_ptr <- #{peek struct HsObject, value} x
    value <- deRefStablePtr value_ptr
    return $ Just (value `asTypeOf` return_type)

-- | Extract a Haskell value of type 'a' from the given object,
-- which must be an HsObject (this property is not checked).
-- If it has the wrong type, throw an exception.
fromHsObject' :: Typeable a => PyPtr -> IO a
fromHsObject' x = do 
  return_type <- return undefined
  type_rep_ptr <- #{peek struct HsObject, type_rep} x
  type_rep <- deRefStablePtr type_rep_ptr
  if type_rep /= typeOf return_type
    then let expected_type = show (typeOf return_type)
             got_type = show type_rep
             message = "Expected Haskell object of type " ++ expected_type ++
                       ", got " ++ got_type
         in throwPythonExc pyTypeError message
    else do
      value_ptr <- #{peek struct HsObject, value} x
      value <- deRefStablePtr value_ptr
      return (value `asTypeOf` return_type)

-- | Extract a Haskell value of type 'a' from the given object.
-- Interpret Python 'None' as 'Nothing' and other values as 'Just' values.
fromMaybeHsObject' :: Typeable a => PyPtr -> IO (Maybe a)
fromMaybeHsObject' x
  | x == py_None = return Nothing
  | otherwise = do
      isinst <- isInstance x hsObject_type
      if isinst 
        then return . Just =<< fromHsObject' x
        else throwPythonExc pyTypeError "Expecting None or HsObject"

-- | Extract a list of Haskell values of type 'a' from the given object.
-- The object must be a Python list.
fromListOfHsObject' :: Typeable a => PyPtr -> IO [a]
fromListOfHsObject' x = do
  is_list <- isList x
  unless is_list $ throwPythonExc pyTypeError "Expecting a list"
  sz <- getListSize x
  
  -- Read list elements, starting at the end.
  -- We don't need to clean up after execeptions, so no try/bracket/finally.
  mapM fromListItem [0 .. sz - 1]
  where
    fromListItem index = fromHsObject' =<< getListItem x index
