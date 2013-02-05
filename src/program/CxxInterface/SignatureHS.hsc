
{-# LANGUAGE ForeignFunctionInterface #-}
module CxxInterface.SignatureHS where

import Control.Monad
import Foreign.C.Types
import Foreign.Ptr
import Foreign.Storable

import Common.Error
import Export

#include "CxxInterface/Signature.h"

#let alignment t = "%lu", (unsigned long)offsetof(struct {char x__; t (y__); }, y__)

-- | Array of 'ExportDataType' in C
data PyonTypes
-- | Function signature type in C
data PyonSignature

data PyonTypeTag = PyonIntTag | PyonFloatTag | PyonBoolTag | PyonNoneTag

foreign import ccall "PyonType_Int" pyonType_Int :: IO (Ptr ExportDataType)
foreign import ccall "PyonType_Float" pyonType_Float :: IO (Ptr ExportDataType)
foreign import ccall "PyonType_Bool" pyonType_Bool :: IO (Ptr ExportDataType)
foreign import ccall "PyonType_NoneType" pyonType_NoneType :: IO (Ptr ExportDataType)
foreign import ccall "PyonType_Tuple" pyonType_Tuple :: CInt -> IO (Ptr ExportDataType)
foreign import ccall "PyonType_List" pyonType_List :: CInt -> Ptr ExportDataType -> IO (Ptr ExportDataType)
foreign import ccall "PyonType_Array" pyonType_Array :: CInt -> CInt -> Ptr ExportDataType -> IO (Ptr ExportDataType)

sendExportDataType :: ExportDataType -> IO (Ptr ExportDataType)
sendExportDataType TrioletNoneET = pyonType_NoneType
sendExportDataType TrioletIntET = pyonType_Int
sendExportDataType TrioletFloatET = pyonType_Float
sendExportDataType TrioletBoolET = pyonType_Bool
sendExportDataType (TupleET ts) = do
  let tuple_size = length ts
  ptr <- pyonType_Tuple (fromIntegral tuple_size)

  -- Send the tuple elements
  array_ptr <- #{peek PyonType, tuple.elems} ptr
  forM_ (zip ts [0..]) $ \(t, index) ->
    pokeElemOff array_ptr index =<< sendExportDataType t
  return ptr

sendExportDataType (ListET b t) = do
  c_t <- sendExportDataType t
  pyonType_List (fromIntegral $ fromEnum b) c_t

sendExportDataType (ArrayET n b t) = do
  c_t <- sendExportDataType t 
  pyonType_Array (fromIntegral n) (fromIntegral $ fromEnum b) c_t

sendExportDataType _ =
  internalError "sendExportDataType: Not implemented for this constructor"

foreign import ccall "PyonTypes_alloc" pyonTypes_alloc ::
  CInt -> IO (Ptr PyonTypes)

sendExportDataTypes :: [ExportDataType] -> IO (Ptr PyonTypes)
sendExportDataTypes xs = do
  -- Create object
  ptr <- pyonTypes_alloc (fromIntegral $ length xs)

  -- Write elements
  array_ptr <- #{peek PyonTypes, elems} ptr
  forM_ (zip xs [0..]) $ \(x, index) ->
    pokeElemOff array_ptr index =<< sendExportDataType x
  return ptr

foreign import ccall "PyonSignature_create" pyonSignature_create ::
  Ptr PyonTypes -> Ptr ExportDataType -> IO (Ptr PyonSignature)

foreign import ccall "PyonSignature_destroy" pyonSignature_destroy ::
  Ptr PyonSignature -> IO ()

sendExportSig :: [ExportDataType] -> ExportDataType -> IO (Ptr PyonSignature)
sendExportSig param_types return_type = do
  params_ptr <- sendExportDataTypes param_types
  return_ptr <- sendExportDataType return_type
  pyonSignature_create params_ptr return_ptr
