
module LowLevel.Records where

import Data.Word
import Gluon.Common.Error
import LowLevel.Types
import LowLevel.Record

-- | Tags indicating the run-time representation of a dynamically typed value.
--
-- The tag represents only the minimum information required at run time.
-- Tags distinguish different data type sizes because they are stored using
-- different numbers of bytes.  Tags distinguish integers from floats 
-- because they use different registers.  Owned references are also
-- distinguished to assist run-time memory management.  However, the
-- distinction between pointer and integer is not retained, and neither is
-- the distinction between signed and unsigned.
data TypeTag =
    Int8Tag | Int16Tag | Int32Tag | Int64Tag 
  | Float32Tag | Float64Tag 
  | OwnedRefTag
  deriving(Eq, Ord, Enum, Show)

intSizeTypeTag S8 = Int8Tag
intSizeTypeTag S16 = Int16Tag
intSizeTypeTag S32 = Int32Tag
intSizeTypeTag S64 = Int64Tag

-- | An info table tag, which indicates an info table's type
data InfoTag = FunTag | PAPTag
  deriving(Eq, Ord, Enum, Show)

-- | Get the type tag of a primitive type
toTypeTag :: PrimType -> TypeTag
toTypeTag BoolType = Int8Tag
toTypeTag (IntType _ sz)  = intSizeTypeTag sz
toTypeTag (FloatType S32) = Float32Tag
toTypeTag (FloatType S64) = Float64Tag
toTypeTag PointerType     = intSizeTypeTag pointerSize
toTypeTag OwnedType       = OwnedRefTag

-- | Get the type tag of a primitive type as used in function application.
-- Only the integer/floating distinction is made (because we care about what
-- register it's passed in), and values smaller than a native word are 
-- promoted to native words.
promotedTypeTag :: PrimType -> TypeTag
promotedTypeTag ty =
  case ty
  of BoolType -> toTypeTag nativeWordType
     IntType _ sz
       | sz <= nativeIntSize -> toTypeTag $ IntType Unsigned nativeIntSize
       | otherwise           -> toTypeTag $ IntType Unsigned sz
     t@(FloatType _) -> toTypeTag t
     PointerType -> pointerTypeTag
     OwnedType -> pointerTypeTag

pointerTypeTag =
  if pointerSize < nativeIntSize
  then internalError "pointerTypeTag"
  else toTypeTag nativeWordType


-- | An info table is a piece of statically defined global data.  Every 
-- reference-counted, dynamically allocated object contains a pointer to an 
-- info table.  The info table describes the object's data representation.
--
-- All info tables start with a \"free\" function that can be called to
-- deallocate the associated object, followed by a type tag. 
-- The type tag indicates the layout of the remaining fields.
infoTableHeader :: [StaticFieldType]
infoTableHeader = [ PrimField PointerType
                  , PrimField (IntType Unsigned S8)
                  ]

infoTableHeaderRecord :: StaticRecord
infoTableHeaderRecord = staticRecord infoTableHeader

-- | A function info table describes a function. 
-- 
-- The fields are:
--
--  0. Free function
--
--  1. Info table type tag
--
--  2. Arity (number of arguments)
--
--  3. Number of captured variables
--
--  4. Number of mutually recursive functions
--
--  5. Exact entry point
--
--  6. Inexact entry point
--
--  These are followed by a list of argument types (length is arity)
--  and a list of captured variable types (length is number of captured vars).
funInfoHeader :: [StaticFieldType]
funInfoHeader = infoTableHeader ++
                [ PrimField (IntType Unsigned S16)
                , PrimField (IntType Unsigned S16)
                , PrimField (IntType Unsigned S16)
                , PrimField PointerType
                , PrimField PointerType]

funInfoHeaderRecord :: StaticRecord
funInfoHeaderRecord = staticRecord funInfoHeader

-- | A PAP info table contains only the minimum information. 
papInfoRecord :: StaticRecord
papInfoRecord = infoTableHeaderRecord

-- | All reference-counted objects have a common header format.
--
-- The header consists of a reference count and a pointer to the object's 
-- info table.
objectHeader :: [StaticFieldType]
objectHeader = [ PrimField nativeWordType
               , PrimField PointerType
               ]

objectHeaderRecord :: StaticRecord
objectHeaderRecord = staticRecord objectHeader

-- | A function closure is an object containing a function's captured
-- variables, including pointers to mutually recursive functions.
--
-- The fields that follow the header are function-specific.
closureHeader :: [StaticFieldType]
closureHeader = objectHeader

closureHeaderRecord :: StaticRecord
closureHeaderRecord = objectHeaderRecord

-- | A partial application structure contains a closure and some
-- function arguments.
-- 
-- The fields are:
--
--  0. Reference count
--
--  1. Info table pointer
--
--  2. The function that is applied
--
--  3. Number of function arguments
papHeader :: [StaticFieldType]
papHeader = objectHeader ++
            [ PrimField OwnedType   -- Function
            , PrimField nativeWordType] -- Number of arguments

papHeaderRecord :: StaticRecord
papHeaderRecord = staticRecord papHeader
