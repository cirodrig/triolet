{-| Definitions of some record types for data generated by the compiler.

Closure conversion turns curried, local functions into uncurried, global
functions.  After closure conversion, functions become /closures/ that
point to /info tables/.

The layout of closures is given by 'localClosureRecord', and consists of
the following three fields.  The last field, the captured variables,
contains all variables captured by closure conversion; its contents are
specific to each function.

> OWNED   Type info pointer (points to triolet_typeObject_function)
> POINTER Info-table pointer
> Record  Captured variables

Each piece of code has an associated info table.  The layout of info
tables is given by 'infoTableRecord', and consists of the following fields.
The type tags record is a sequence of bytes, one per function parameter 
followed by one per captured variable.

> UINT16  Function arity
> UINT16  Number of captured variables
> POINTER Exact entry point
> POINTER Inexact entry point
> Record  Type tags for parameters and captured variables

If a curried function is not applied to all expected arguments, a new
data structure called a partial application, or /PAP/, is created.
A PAP holds the function and its argument.  When a function is applied to
multiple arguments, a chain of PAPs is created, one for each argument.
The layout of a PAP is given by 'papRecord', and is as follows:

> OWNED   Type info pointer (points to a PAP type object)
> POINTER NULL
> OWNED   Operator
> UINT16  Arity of PAP
> a       Argument

-}
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

-- | A type object for boxed objects.  The fields are:
--
-- 0. The type object's type object
-- 1. Constructor index
typeObjectRecord = constStaticRecord [ PrimField OwnedType
                                     , PrimField nativeIntType
                                     ]

-- | A closure created in C and passed to triolet code. 
--   The closure is a struct with two fields.  The first
--   is a function pointer, the second is a pointer to data.
cClosureRecord = constStaticRecord [ PrimField PointerType
                                   , PrimField PointerType]

-- | A function info table describes a function.  See the module header
--   for a description of the fields.
funInfoTableFields :: StaticRecord -> [StaticFieldType]
funInfoTableFields type_tags = [ PrimField funArityType
                               , PrimField funArityType
                               , PrimField PointerType
                               , PrimField PointerType
                               , RecordField type_tags]

infoTableRecord :: StaticRecord -> StaticRecord
infoTableRecord tt = constStaticRecord (funInfoTableFields tt)

infoTableRecord0 :: StaticRecord
infoTableRecord0 = infoTableRecord (constStaticRecord [])

-- | A record containing @N@ type tags.
typeTagsRecord :: Int -> StaticRecord
typeTagsRecord n =
  constStaticRecord (replicate n $ PrimField (IntType Unsigned S8))

-- | A closure.  See the module header for the meaning of each field.
localClosureRecord :: StaticRecord -> StaticRecord
localClosureRecord captured_vars =
  constStaticRecord [ PrimField OwnedType
                    , PrimField PointerType
                    , RecordField captured_vars]

localClosureRecord0 :: StaticRecord
localClosureRecord0 = localClosureRecord (constStaticRecord [])

-- | A global closure does not capture variables
globalClosureRecord :: StaticRecord
globalClosureRecord = localClosureRecord (constStaticRecord [])

-- | A PAP, or partial application, is an object containing an operator and 
--   an argument.  There are different PAP objects for different argument
--   types.
--
--   See the module header for the meaning of each field.
papRecord :: PrimType -> StaticRecord
papRecord arg = constStaticRecord
                [ PrimField OwnedType
                , PrimField PointerType
                , PrimField OwnedType
                , PrimField funArityType
                , PrimField arg
                ]

papRecord0 :: StaticRecord
papRecord0 = papRecord UnitType

-- | A Triolet list.
listRecord :: StaticRecord
listRecord = constStaticRecord
             [ RecordField finIndexedIntRecord -- Size
             , PrimField PointerType    -- Pointer to contents
             ]

-- | A Triolet list-of-boxed-objects.
blistRecord :: StaticRecord
blistRecord = constStaticRecord [RecordField listRecord]

-- | A Triolet matrix.
matrixRecord :: StaticRecord
matrixRecord = constStaticRecord
             [ RecordField finIndexedIntRecord -- Size (y)
             , RecordField finIndexedIntRecord -- Size (x)
             , PrimField PointerType    -- Pointer to contents
             ]

-- Various array objects (array[0..3], barray[1..3])
array0Record :: StaticRecord
array0Record = constStaticRecord
               [ PrimField OwnedType
               ]

array1Record :: StaticRecord
array1Record = constStaticRecord
               [ PrimField trioletIntType
               , PrimField trioletIntType
               , RecordField finIndexedIntRecord
               , PrimField OwnedType
               ]

array2Record :: StaticRecord
array2Record = constStaticRecord
               [ PrimField trioletIntType
               , PrimField trioletIntType
               , RecordField finIndexedIntRecord
               , PrimField trioletIntType
               , PrimField trioletIntType
               , RecordField finIndexedIntRecord
               , PrimField OwnedType
               ]

array3Record :: StaticRecord
array3Record = constStaticRecord
               [ PrimField trioletIntType
               , PrimField trioletIntType
               , RecordField finIndexedIntRecord
               , PrimField trioletIntType
               , PrimField trioletIntType
               , RecordField finIndexedIntRecord
               , PrimField trioletIntType
               , PrimField trioletIntType
               , RecordField finIndexedIntRecord
               , PrimField OwnedType
               ]

barray1Record, barray2Record, barray3Record :: StaticRecord
barray1Record = constStaticRecord [ RecordField array1Record]
barray2Record = constStaticRecord [ RecordField array2Record]
barray3Record = constStaticRecord [ RecordField array3Record]

