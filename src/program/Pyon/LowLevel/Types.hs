{-| Machine-level data types.
-}

module Pyon.LowLevel.Types where

data Signedness = Signed | Unsigned
                deriving(Eq, Ord, Show, Enum)

data Size = S8 | S16 | S32 | S64
          deriving(Eq, Ord, Show, Enum)

-- | A type that can be held in an ANF variable.
data PrimType =
    UnitType                    -- ^ A value represented as nothing
  | BoolType                    -- ^ The boolean type
  | IntType                     -- ^ An integral type
    { intSign :: !Signedness
    , intSize :: !Size
    }
  | FloatType                   -- ^ A floating-point type
    { floatSize :: !Size
    }
  | PointerType                 -- ^ A pointer
  | OwnedType                   -- ^ An owned reference requiring reference
                                --   count updates when copied or discarded
    deriving (Eq, Show)

-- | /FIXME/: This is architecture-dependent.
nativeIntSize :: Size
nativeIntSize = S32

nativeIntType, nativeWordType :: PrimType
nativeIntType = IntType Signed S32
nativeWordType = IntType Unsigned S32

pyonIntSize :: Size
pyonIntSize = S32

pyonFloatSize :: Size
pyonFloatSize = S32

pyonIntType, pyonFloatType, pyonBoolType, pyonNoneType :: PrimType
pyonIntType = IntType Signed pyonIntSize
pyonFloatType = FloatType pyonIntSize
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
  sizeOf PointerType    = 8     -- FIXME: this is architecture-dependent
  sizeOf OwnedType      = 8     -- FIXME: this is architecture-dependent
  alignOf UnitType = 1
  alignOf x = sizeOf x
