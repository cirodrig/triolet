{-| Machine-level data types.
-}

module LowLevel.Types where

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

-- | /FIXME/: This is architecture-dependent.
pointerSize :: Size
pointerSize = S32

-- | /FIXME/: This is architecture-dependent.
nativeIntSize :: Size
nativeIntSize = S32

-- | /FIXME/: This is architecture-dependent.
nativeFloatSize :: Size
nativeFloatSize = S32

-- | The maximum alignment of any scalar value, in bytes.
--
-- /FIXME/: This is architecture-dependent.
maxScalarAlignment :: Int
maxScalarAlignment = 8

-- | The alignment of scalar values in dynamically constructed data structures,
-- such as stacks and partial application records.
--
-- All promoted types must have a size that is a multiple of this size.
--
-- If unaligned loads are not permissible, this must be equal to
-- 'maxScalarAlignment'.  On architectures supporting unaligned loads, or if
-- unaligned loads are emulated in software, smaller alignments are
-- permissible.  Smaller alignments have the advantage of wasting less space, 
-- but may carry a speed penalty for values with larger natural alignment.
-- 
-- /FIXME/: This is architecture-dependent.
dynamicScalarAlignment :: Int
dynamicScalarAlignment = 4

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
