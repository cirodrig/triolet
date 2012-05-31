
module LowLevel.Records where

import Data.Word

import Common.Error
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
    UnitTag
  | Int8Tag | Int16Tag | Int32Tag | Int64Tag
  | Float32Tag | Float64Tag
  deriving(Eq, Ord, Enum, Show)

intSizeTypeTag S8 = Int8Tag
intSizeTypeTag S16 = Int16Tag
intSizeTypeTag S32 = Int32Tag
intSizeTypeTag S64 = Int64Tag

-- | A bits tag, representing the physical representation of a value in memory.
-- Bits-tagged data are always promoted to a value at least as big as the 
-- 'dynamicScalarAlignment'.
data BitsTag = Bits0Tag | Bits32Tag | Bits64Tag
             deriving(Eq, Ord, Enum, Show)

-- | Get the bits tag of a primitive type.  The primitive type must be a
-- suitable size, perhaps by being promoted.
toBitsTag :: PrimType -> BitsTag
toBitsTag ty
  | sizeOf ty == 0 = Bits0Tag
  | sizeOf ty == 4 = Bits32Tag
  | sizeOf ty == 8 = Bits64Tag
  | otherwise =
    internalError "toBitsTag: Cannot generate tag for this data size"

-- | An info table tag, which indicates an info table's type
data InfoTag = FunTag | PAPTag | ConTag
  deriving(Eq, Ord, Enum, Show)

-- | Get the type tag of a primitive type
toTypeTag :: PrimType -> TypeTag
toTypeTag BoolType = Int8Tag
toTypeTag UnitType = UnitTag
toTypeTag (IntType _ sz)  = intSizeTypeTag sz
toTypeTag (FloatType S32) = Float32Tag
toTypeTag (FloatType S64) = Float64Tag
toTypeTag PointerType     = intSizeTypeTag pointerSize
toTypeTag OwnedType       = intSizeTypeTag pointerSize

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

-- | An indexed int is a record containing an int.
indexedIntRecord :: StaticRecord
indexedIntRecord =
  constStaticRecord [ PrimField (IntType Unsigned S8)
                    , RecordField indexedIntDataRecord]

indexedIntDataRecord = constStaticRecord [RecordField finIndexedIntRecord]

-- | A finite indexed int
finIndexedIntRecord = constStaticRecord [PrimField nativeIntType]

-- | A structure containing size and alignment fields
sizeAlignRecord :: StaticRecord
sizeAlignRecord = constStaticRecord
                  [ PrimField nativeWordType -- Size
                  , PrimField nativeWordType -- Alignment
                  ]
-- | A parameter passing convention consists of size, alignment, copy,
-- and finalize functions, and a flag indicating whether the object is
-- pointerless.
--
-- Pointerless data does not need to be scanned during GC.
passConvRecord :: StaticRecord
passConvRecord = constStaticRecord
                 [ RecordField objectHeaderRecord
                 , RecordField sizeAlignRecord 
                 , PrimField OwnedType      -- Copy function
                 , PrimField OwnedType      -- Convert to boxed function
                 , PrimField OwnedType      -- Convert to bare function
                 , PrimField BoolType       -- Is pointerless?
                 ]

-- | A closure created in C and passed to triolet code. 
--   The closure is a struct with two fields.  The first
--   is a function pointer, the second is a pointer to data.
cClosureRecord = constStaticRecord [ PrimField PointerType
                                   , PrimField PointerType]

-- | The record type of a traversable class dictionary
traversableDictRecord :: StaticRecord
traversableDictRecord =
  constStaticRecord [ RecordField objectHeaderRecord
                    , PrimField OwnedType
                    , PrimField OwnedType]

-- | An info table is a piece of statically defined global data.  Every 
--   boxed object contains a pointer to an info table.
--   The info table describes the object's data representation.
--
--   Info tables contain a tag that indicates the layout of the
--   remaining fields.  The tag is the 'fromEnum' value of an 'InfoTag'.
infoTableHeader :: [StaticFieldType]
infoTableHeader = [ PrimField (IntType Unsigned S8)
                  ]

infoTableHeaderRecord :: StaticRecord
infoTableHeaderRecord = constStaticRecord infoTableHeader

-- | A function info table describes a function.
--
--   When reading an info table, we don't know how many type tags there are.
--   Assume there are zero type tags, read the arity, then build the real
--   info table record.
-- 
-- The fields are:
--
--  0. Info table header
--
--  1. Arity (number of arguments; excludes closure)
--
--  2. Exact entry point
--
--  3. Inexact entry point
--
--  4. Argument type tags
funInfoHeader :: StaticRecord -> [StaticFieldType]
funInfoHeader type_tags = [ RecordField infoTableHeaderRecord
                          , PrimField (IntType Unsigned S16)
                          , PrimField PointerType
                          , PrimField PointerType
                          , RecordField type_tags]

funInfoHeaderRecord :: StaticRecord -> StaticRecord
funInfoHeaderRecord tt = constStaticRecord (funInfoHeader tt)

funInfoHeaderRecord0 :: StaticRecord
funInfoHeaderRecord0 = funInfoHeaderRecord (constStaticRecord [])

-- | A record containing @N@ type tags.
typeTagsRecord :: Int -> StaticRecord
typeTagsRecord n =
  constStaticRecord (replicate n $ PrimField (IntType Unsigned S8))

-- | All reference-counted objects have a common header format.
--
-- The header consists of a reference count and a pointer to the object's 
-- info table.
objectHeader :: [(Mutability, StaticFieldType)]
objectHeader = [ (Constant, PrimField PointerType)
               ]

objectHeaderRecord :: StaticRecord
objectHeaderRecord = staticRecord objectHeader

-- | A global closure consists of only an object header
globalClosureRecord :: StaticRecord
globalClosureRecord = constStaticRecord [RecordField objectHeaderRecord]

-- | A recursive closure consists of an object header and a pointer
recursiveClosureRecord :: StaticRecord
recursiveClosureRecord =
  constStaticRecord [ RecordField objectHeaderRecord
                       , PrimField PointerType]

-- | A non-global, non-recursive closure contains captured variables 
localClosureRecord :: StaticRecord -> StaticRecord
localClosureRecord captured_vars =
  constStaticRecord [ RecordField objectHeaderRecord
                       , RecordField captured_vars]

-- | A partial application is an object containing a function and some of
-- its arguments.  The header is followed by some arguments.
papHeader :: [StaticFieldType]
papHeader = [ RecordField objectHeaderRecord
            , PrimField OwnedType              -- The function
            , PrimField (IntType Unsigned S16) -- Number of arguments
            , PrimField (IntType Unsigned S16) -- Size of arguments in words
            ]

papHeaderRecord :: StaticRecord
papHeaderRecord = constStaticRecord papHeader

-- | A complex value.  It consists of a real and an imaginary part.
complexRecord :: StaticFieldType -> StaticRecord
complexRecord ftype = constStaticRecord [ftype, ftype]

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
streamRecord =
  constStaticRecord $
  [ RecordField objectHeaderRecord
  , PrimField OwnedType -- Function (closure)
  , PrimField OwnedType -- Initializer (closure)
  , RecordField passConvRecord -- Stream data properties
  ]

-- | A Triolet list.
listRecord :: StaticRecord
listRecord = constStaticRecord
             [ RecordField finIndexedIntRecord -- Size
             , PrimField PointerType    -- Pointer to contents
             ]

-- | A Triolet matrix.
matrixRecord :: StaticRecord
matrixRecord = constStaticRecord
             [ RecordField finIndexedIntRecord -- Size (y)
             , RecordField finIndexedIntRecord -- Size (x)
             , PrimField PointerType    -- Pointer to contents
             ]
