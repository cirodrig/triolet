{-| Machine-level data types.
-}

module LowLevel.Types where

import Control.Applicative
import Control.Monad
import Data.Bits
import Data.Binary

import Common.Error
import LowLevel.BinaryUtils
import Machine

data Signedness = Signed | Unsigned
                deriving(Eq, Ord, Show, Enum)

data Size = S8 | S16 | S32 | S64
          deriving(Eq, Ord, Show, Enum, Bounded)

-- | A type that can be held in an ANF variable.
data PrimType =
    UnitType                    -- ^ A value represented as nothing
  | BoolType                    -- ^ The boolean type

    -- | An integral type
  | IntType
    { intSign :: !Signedness
    , intSize :: !Size
    }

    -- | A floating-point type
  | FloatType
    { floatSize :: !Size
    }
  | PointerType                 -- ^ A pointer
  | OwnedType                   -- ^ An owned reference requiring reference
                                --   count updates when copied or discarded
  | CursorType                  -- ^ A cursor pointing to the interior of 
                                --   an object.  After closure conversion,
                                --   cursors become a (owned, pointer) pair.
    deriving (Eq, Ord, Show)

pointerSize :: Size
nativeIntSize :: Size
nativeFloatSize :: Size

pointerSize
  | targetWordSizeBytes == 4 = S32
  | targetWordSizeBytes == 8 = S64
  | otherwise = internalError $ "Cannot generate code for target word size (" ++ show targetWordSizeBytes ++ ")"
       
nativeIntSize
  | targetIntSizeBytes == 4 = S32
  | targetIntSizeBytes == 8 = S64
  | otherwise = internalError $ "Cannot generate code for target int size (" ++ show targetIntSizeBytes ++ ")"

-- | /FIXME/: This is architecture-dependent.
nativeFloatSize = S32

-- | The maximum alignment of any scalar value, in bytes.
--
-- /FIXME/: This is architecture-dependent.
maxScalarAlignment :: Int
maxScalarAlignment = 8

-- | The smallest representable integer with the given size and alignment.
smallestRepresentableInt :: Signedness -> Size -> Integer
smallestRepresentableInt Unsigned _ = 0
smallestRepresentableInt Signed S8  = -0x80
smallestRepresentableInt Signed S16 = -0x8000
smallestRepresentableInt Signed S32 = -0x80000000
smallestRepresentableInt Signed S64 = -0x8000000000000000

-- | The largest representable integer with the given size and alignment.
largestRepresentableInt :: Signedness -> Size -> Integer
largestRepresentableInt Unsigned S8  = 0xff
largestRepresentableInt Unsigned S16 = 0xffff
largestRepresentableInt Unsigned S32 = 0xffffffff
largestRepresentableInt Unsigned S64 = 0xffffffffffffffff
largestRepresentableInt Signed   S8  = 0x7f
largestRepresentableInt Signed   S16 = 0x7fff
largestRepresentableInt Signed   S32 = 0x7fffffff
largestRepresentableInt Signed   S64 = 0x7fffffffffffffff

isRepresentableInt :: Signedness -> Size -> Integer -> Bool
isRepresentableInt sgn sz n =
  n >= smallestRepresentableInt sgn sz && n <= largestRepresentableInt sgn sz

-- | The number of distinct values an integer of this type has
intCardinality :: Size -> Integer
intCardinality S8  = 1 `shiftL` 8
intCardinality S16 = 1 `shiftL` 16
intCardinality S32 = 1 `shiftL` 32
intCardinality S64 = 1 `shiftL` 64

coerceToRepresentableInt :: Signedness -> Size -> Integer -> Integer
coerceToRepresentableInt Unsigned sz n = n .&. (intCardinality sz - 1)
coerceToRepresentableInt Signed sz n =
  let n' = n .&. (intCardinality sz - 1)
  in if n' > largestRepresentableInt Signed sz
     then n' - intCardinality sz
     else n'

-- | The alignment of scalar values in dynamically constructed data structures,
-- such as stacks and partial application records.
--
-- If unaligned loads are not permissible, this must be equal to
-- 'maxScalarAlignment'.  On architectures supporting unaligned loads, or if
-- unaligned loads are emulated in software, smaller alignments are
-- permissible.  Smaller alignments have the advantage of wasting less space, 
-- but may carry a speed penalty for values with larger natural alignment.
-- 
-- /FIXME/: This is architecture-dependent.
dynamicScalarAlignment :: Int
dynamicScalarAlignment = targetWordSizeBytes

nativeIntType, nativeWordType, nativeFloatType :: PrimType
nativeIntType = IntType Signed nativeIntSize
nativeWordType = IntType Unsigned nativeIntSize
nativeFloatType = FloatType nativeFloatSize

trioletIntSize :: Size
trioletIntSize = S32

trioletFloatSize :: Size
trioletFloatSize = S32

trioletIntType, trioletUintType, trioletFloatType,
  trioletBoolType, trioletByteType, trioletNoneType :: PrimType
trioletIntType = IntType Signed trioletIntSize
trioletInt64Type = IntType Signed S64
trioletUintType = IntType Unsigned trioletIntSize
trioletFloatType = FloatType trioletFloatSize
trioletBoolType = BoolType
trioletByteType = IntType Unsigned S8
trioletNoneType = UnitType

-- | The data type used to keep track of a function's arity in functions
--   and PAPs
funArityType :: PrimType
funArityType = IntType Unsigned S16

-- | A data type that has statically known memory management properties
class HasSize a where
  -- | Get the size
  sizeOf :: a -> Int
  
  -- | Get the alignment.  Alignments must be a power of two.
  alignOf :: a -> Int
  
  -- | Detemrine whether the data is pointerless.  A /pointerless/ value
  --   contains no pointers that need to be tracked by the garbage collector.
  pointerlessness :: a -> Bool

instance HasSize Size where
  sizeOf S8  = 1
  sizeOf S16 = 2
  sizeOf S32 = 4
  sizeOf S64 = 8
  alignOf = sizeOf
  pointerlessness _ = True

instance HasSize PrimType where
  sizeOf UnitType       = 0
  sizeOf BoolType       = 1
  sizeOf (IntType _ sz) = sizeOf sz
  sizeOf (FloatType sz) = sizeOf sz
  sizeOf PointerType    = sizeOf pointerSize
  sizeOf OwnedType      = sizeOf pointerSize
  sizeOf CursorType     = 2 * sizeOf pointerSize
  alignOf UnitType = 1
  alignOf CursorType    = sizeOf pointerSize
  alignOf x = sizeOf x
  pointerlessness PointerType = False
  pointerlessness OwnedType   = False
  pointerlessness CursorType  = False
  pointerlessness _           = True

-- | Promote a type to at least the size of a machine word.  Promoted types
-- are used in function calls, return values, and partial applications.
promoteType :: PrimType -> PrimType
promoteType pt =
  case pt
  of UnitType -> UnitType
     BoolType -> nativeIntType
     IntType sgn sz -> IntType Signed (max sz nativeIntSize)
     FloatType sz -> FloatType (max sz nativeFloatSize)
     PointerType -> PointerType
     OwnedType   -> OwnedType
     CursorType  -> CursorType

-------------------------------------------------------------------------------
-- Binary instances

instance Binary Signedness where
  put = putEnum
  get = getEnum "Signedness.get"

instance Binary Size where
  put = putEnum
  get = getEnum "Size.get"

instance Binary PrimType where
  put UnitType = putWord8 0
  put BoolType = putWord8 1
  put (IntType sgn sz) = putWord8 2 >> put sgn >> put sz 
  put (FloatType sz) = putWord8 3 >> put sz
  put PointerType = putWord8 4
  put OwnedType = putWord8 5
  put CursorType = putWord8 6
  
  get = getWord8 >>= getPrimTypeWithTag
      

getPrimTypeWithTag 0 = return UnitType
getPrimTypeWithTag 1 = return BoolType
getPrimTypeWithTag 2 = IntType <$> get <*> get
getPrimTypeWithTag 3 = FloatType <$> get
getPrimTypeWithTag 4 = return PointerType
getPrimTypeWithTag 5 = return OwnedType
getPrimTypeWithTag 6 = return CursorType
getPrimTypeWithTag _ = readError "PrimType.get"