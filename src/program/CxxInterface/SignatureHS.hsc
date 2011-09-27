
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

data PyonTypes                  -- ^ Array of 'ExportDataType' in C
data PyonSignature              -- ^ Function signature type in C

data PyonTypeTag = PyonIntTag | PyonFloatTag | PyonBoolTag | PyonNoneTag

foreign import ccall "PyonType_Int" pyonType_Int :: IO (Ptr ExportDataType)
foreign import ccall "PyonType_Float" pyonType_Float :: IO (Ptr ExportDataType)
foreign import ccall "PyonType_Bool" pyonType_Bool :: IO (Ptr ExportDataType)
foreign import ccall "PyonType_NoneType" pyonType_NoneType :: IO (Ptr ExportDataType)

sendExportDataType :: ExportDataType -> IO (Ptr ExportDataType)
sendExportDataType PyonIntET = pyonType_Int
sendExportDataType PyonFloatET = pyonType_Float
sendExportDataType PyonBoolET = pyonType_Bool
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

sendExportSig :: [ExportDataType] -> ExportDataType -> IO (Ptr PyonSignature)
sendExportSig param_types return_type = do
  params_ptr <- sendExportDataTypes param_types
  return_ptr <- sendExportDataType return_type
  pyonSignature_create params_ptr return_ptr
