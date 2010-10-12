
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

-- | A bits tag, representing the physical representation of a value in memory.
-- Bits-tagged data are always promoted to a value at least as big as the 
-- 'dynamicScalarAlignment'.
--
-- /FIXME/: The fields of this type are platform-dependnet
data BitsTag = Bits32Tag | Bits64Tag | OwnedRefBitsTag
             deriving(Eq, Ord, Enum, Show)

-- | Get the bits tag of a primitive type.  The primitive type must be a
-- suitable size, perhaps by being promoted.
toBitsTag :: PrimType -> BitsTag
toBitsTag ty =
  case ty
  of OwnedType -> OwnedRefBitsTag
     _ | sizeOf ty == 4 -> Bits32Tag
       | sizeOf ty == 8 -> Bits64Tag
       | otherwise ->
         internalError "toBitsTag: Cannot generate tag for this data size"

-- | An info table tag, which indicates an info table's type
data InfoTag = FunTag | PAPTag | ConTag
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
promotedTypeTag ty = toTypeTag $ promoteType ty

pointerTypeTag =
  if pointerSize < nativeIntSize
  then internalError "pointerTypeTag"
  else toTypeTag nativeWordType

-------------------------------------------------------------------------------
-- Record types

-- | A parameter passing convention consists of size, alignment, copy,
-- and finalize functions
passConvRecord :: StaticRecord
passConvRecord = staticRecord [ PrimField nativeWordType
                              , PrimField nativeWordType
                              , PrimField OwnedType
                              , PrimField OwnedType
                              ]

-- | The record type of an additive class dictionary
additiveDictRecord :: StaticRecord
additiveDictRecord =
  staticRecord [ PrimField OwnedType
               , PrimField OwnedType
               , PrimField OwnedType]

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
--  2. Arity (number of arguments; excludes closure)
--
--  3. Exact entry point
--
--  4. Inexact entry point
--
--  These are followed by a list of argument type tags (length is arity).
funInfoHeader :: [StaticFieldType]
funInfoHeader = [ RecordField infoTableHeaderRecord
                , PrimField (IntType Unsigned S16)
                , PrimField PointerType
                , PrimField PointerType]

funInfoHeaderRecord :: StaticRecord
funInfoHeaderRecord = staticRecord funInfoHeader

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

-- | A global closure consists of only an object header
globalClosureRecord :: StaticRecord
globalClosureRecord = staticRecord [RecordField objectHeaderRecord]

-- | A recursive closure consists of an object header and a pointer
recursiveClosureRecord :: StaticRecord
recursiveClosureRecord = staticRecord [ RecordField objectHeaderRecord
                                      , PrimField PointerType]

-- | A non-global, non-recursive closure contains captured variables 
localClosureRecord :: StaticRecord -> StaticRecord
localClosureRecord captured_vars =
  staticRecord [RecordField objectHeaderRecord, RecordField captured_vars]

-- | A function or partial application is an object containing a
-- function's captured variables, including pointers to mutually recursive
-- functions.  The info table together with the 'nargs' field determines the
-- layout of the remaining fields.
papHeader :: [StaticFieldType]
papHeader = [ RecordField objectHeaderRecord
            , PrimField OwnedType
            , PrimField (IntType Unsigned S16)
            ]

papHeaderRecord :: StaticRecord
papHeaderRecord = staticRecord papHeader


-- | A stream object.
--
-- There are several kinds of stream objects.  All stream objects have a
-- common header format consisting of the following fields:
--
-- 1. Reference count
--
-- 2. Info table pointer
--
-- 3. Sequential producer function.  Produces one value and updates state.
--    Parameters: (pointer to state, consumer function, consumer state)
--    Returns: bool
--    The return value is False if the stream is exhausted, in which case
--    the consumer was not invoked.
--
-- 4. Parameter-passing convention of stream state
--
-- 5. Initialization function for stream state
--    Parameters: (pointer to state)
--    Returns: void
streamRecord :: StaticRecord
streamRecord = staticRecord $
               objectHeader ++
               [ PrimField OwnedType -- Function (closure)
               , PrimField OwnedType -- Initializer (closure)
               , RecordField passConvRecord -- Stream data properties
               ]

-- | A Pyon list.
listRecord :: StaticRecord
listRecord = staticRecord
             [ PrimField nativeWordType -- Size
             , PrimField PointerType    -- Pointer to contents
             ]

{-
-- The stream return creator and stream return initializer have nothing
-- in their closures

streamReturnNextClosureRecord :: StaticRecord
streamReturnNextClosureRecord =
  staticRecord $
  closureHeader ++
  [ PrimField OwnedType -- Actual producer function
  , RecordField passConvRecord -- Return data properties
  ]

-- | Closure for the stream bind's producer function
streamBindClosureRecord :: StaticRecord
streamBindClosureRecord =
  staticRecord $
  closureHeader ++ 
  [ PrimField OwnedType -- Producer stream
  , PrimField OwnedType -- Consumer/producer function
  , RecordField passConvRecord -- Return data properties
  ]

-}