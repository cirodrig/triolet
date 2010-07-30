
{-# LANGUAGE FlexibleInstances #-}
module LowLevel.Record where

import Data.Bits
import Gluon.Common.Error
import LowLevel.Types
import {-# SOURCE #-} LowLevel.Syntax

-- | A record type, consisting of fields with known type and alignment.
--
-- Record types are used for computing the physical layout of data and
-- generating load and store instructions.
data Record t =
  Rec { recordFields_ :: ![Field t]
      , recordSize_ :: !t
      , recordAlignment_ :: !t
      }

-- | A record field
data Field t =
  Field { fieldOffset :: !t
        , fieldType  :: !(FieldType t)
        }

-- | A record field type
data FieldType t =
    -- | A primitive data type
    PrimField !PrimType
    -- | An embedded record.
    -- 
    -- The flag has no bearing on the record's data layout, but assists 
    -- lowering by indicating whether this record is pass-by-value or
    -- pass-by-reference.  
  | RecordField !Bool !(Record t)
    -- | Featureless bytes with known size and alignment
  | BytesField !t !t

record :: [Field t] -> t -> t -> Record t
record = Rec

recordFields :: Record t -> [Field t]
recordFields = recordFields_

-- | Select a record field
(!!:) :: Record t -> Int -> Field t
r !!: i = pick i $ recordFields r
  where
    pick 0 (f:_)  = f
    pick n (_:fs) = pick (n-1) fs
    pick _ []     = internalError "(!!:): Record field index out of range"

recordSize :: Record t -> t
recordSize = recordSize_

recordAlignment :: Record t -> t
recordAlignment = recordAlignment_

-- | In a record with static layout, all sizes and offsets are known at compile
-- time
type StaticRecord = Record Int
type StaticField = Field Int
type StaticFieldType = FieldType Int

-- | In a record with dynamic layout, sizes and offsets are computed run-time
-- values
type DynamicRecord = Record Val
type DynamicField = Field Val
type DynamicFieldType = FieldType Val

-------------------------------------------------------------------------------

instance HasSize (FieldType Int) where
  sizeOf (PrimField v) = sizeOf v
  sizeOf (RecordField _ r) = sizeOf r
  sizeOf (BytesField s _) = s

  alignOf (PrimField v) = alignOf v
  alignOf (RecordField _ r) = alignOf r
  alignOf (BytesField _ a) = a

instance HasSize (Record Int) where
  sizeOf = recordSize
  alignOf = recordAlignment

instance HasSize (Field Int) where
  sizeOf f = sizeOf (fieldType f)
  alignOf f = alignOf (fieldType f)

staticRecord :: [StaticFieldType] -> StaticRecord
staticRecord fs = let
  field_offsets = compute_offsets 0 fs
  alignment     = foldr lcm 1 $ map alignOf fs
  size          = if null fs
                  then 0
                  else pad (last field_offsets + sizeOf (last fs)) alignment
  in record (zipWith Field field_offsets fs) size alignment
  where
    -- Each field starts at the offset of the previous field, plus the
    -- previous field's size, plus some padding bytes
    compute_offsets offset (PrimField vt : fields) =
      let start_offset = pad offset $ alignOf vt
          end_offset = start_offset + sizeOf vt
      in start_offset : compute_offsets end_offset fields
    compute_offsets offset (BytesField {} : _) =
      internalError "staticRecord: Field is not statically typed"
    compute_offsets offset [] = []

type Offset = Int

pad :: Offset -> Int -> Offset
pad off alignment = off + (negate off `mod` alignment)

-- | Compute the base-2 logarithm of a power of 2
log2 :: Int -> Int
log2 1 = 0
log2 n = 1 + log2 (n `shiftR` 1)
