{-| Machine-level data types.
-}

module LowLevel.Types where

import Control.Applicative
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

pyonIntSize :: Size
pyonIntSize = S32

pyonFloatSize :: Size
pyonFloatSize = S32

pyonIntType, pyonFloatType, pyonBoolType, pyonNoneType :: PrimType
pyonIntType = IntType Signed pyonIntSize
pyonFloatType = FloatType pyonFloatSize
pyonBoolType = BoolType
pyonNoneType = UnitType

-- | A data type that has associated byte-level size and alignment properties
class HasSize a where
  sizeOf :: a -> Int
  
  -- | Get an alignment.  Alignments must be a power of two.
  alignOf :: a -> Int

instance HasSize Size where
  sizeOf S8  = 1
  sizeOf S16 = 2
  sizeOf S32 = 4
  sizeOf S64 = 8
  alignOf = sizeOf

instance HasSize PrimType where
  sizeOf UnitType       = 0
  sizeOf BoolType       = 1
  sizeOf (IntType _ sz) = sizeOf sz
  sizeOf (FloatType sz) = sizeOf sz
  sizeOf PointerType    = sizeOf pointerSize
  sizeOf OwnedType      = sizeOf pointerSize
  alignOf UnitType = 1
  alignOf x = sizeOf x

-- | Promote a type to at least the size of a machine word.  Promoted types
-- are used in function calls, return values, and partial applications.
promoteType :: PrimType -> PrimType
promoteType pt =
  case pt
  of UnitType -> UnitType
     BoolType -> nativeIntType
     IntType sgn sz -> IntType sgn (max sz nativeIntSize)
     FloatType sz -> FloatType (max sz nativeFloatSize)
     PointerType -> PointerType
     OwnedType -> OwnedType

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
  
  get = getWord8 >>= getPrimTypeWithTag
      

getPrimTypeWithTag 0 = return UnitType
getPrimTypeWithTag 1 = return BoolType
getPrimTypeWithTag 2 = IntType <$> get <*> get
getPrimTypeWithTag 3 = FloatType <$> get
getPrimTypeWithTag 4 = return PointerType
getPrimTypeWithTag 5 = return OwnedType
getPrimTypeWithTag _ = readError "PrimType.get"