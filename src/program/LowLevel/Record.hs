
{-# LANGUAGE FlexibleInstances, StandaloneDeriving, TypeSynonymInstances #-}
module LowLevel.Record where

import Control.Applicative
import Data.Binary
import Data.Bits
import Gluon.Common.Error
import LowLevel.BinaryUtils
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

-- | A record field.
--
-- Record fields never have 'AlignField' type.
data Field t =
  Field { fieldOffset :: !t
        , fieldType  :: !(FieldType t)
        }

-- | A record field type
data FieldType t =
    -- | A primitive data type
    PrimField !PrimType
    -- | An embedded record.  The record fields are inlined.  Note that
    -- record field data may have a different alignment than if the fields
    -- were simply \"inlined\".
  | RecordField !(Record t)
    -- | Featureless bytes with known size and alignment
  | BytesField !t !t
    -- | Unused space inserted for alignment
  | AlignField !t

isAlignField (AlignField {}) = True
isAlignField _ = False

record :: [Field t] -> t -> t -> Record t
record = Rec

recordFields :: Record t -> [Field t]
recordFields = recordFields_

-- | Apply a transformation to all field types in a record.  If there are
--   fields with record type, their fields aren't transformed.  The
--   transformation must preserve sizes and alignments.
mapRecordFieldTypes :: (StaticFieldType -> StaticFieldType)
                    -> StaticRecord -> StaticRecord
mapRecordFieldTypes f rec =
  rec {recordFields_ = map apply_f $ recordFields_ rec}
  where
    apply_f fld =
      let fld' = fld {fieldType = f (fieldType fld)}
      in if sizeOf fld' /= sizeOf fld 
         then internalError "mapRecordFieldTypes: Size wasn't preserved"
         else if alignOf fld' /= alignOf fld
              then internalError "mapRecordFieldTypes: Alignment wasn't preserved"
              else fld'

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

deriving instance Eq StaticRecord
deriving instance Eq StaticFieldType
deriving instance Eq StaticField

-- | In a record with dynamic layout, sizes and offsets are computed run-time
-- values
type DynamicRecord = Record Val
type DynamicField = Field Val
type DynamicFieldType = FieldType Val

-------------------------------------------------------------------------------

instance HasSize (FieldType Int) where
  sizeOf (PrimField v) = sizeOf v
  sizeOf (RecordField r) = sizeOf r
  sizeOf (BytesField s _) = s

  alignOf (PrimField v) = alignOf v
  alignOf (RecordField r) = alignOf r
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
  real_fields   = filter (not . isAlignField) fs
  alignment     = foldr lcm 1 $ map alignOf real_fields
  size          = if null real_fields
                  then 0
                  else last field_offsets + sizeOf (last real_fields)
  in record (zipWith Field field_offsets real_fields) size alignment
  where
    -- Each field starts at the offset of the previous field, plus the
    -- previous field's size, plus some padding bytes
    compute_offsets offset (field : fields) = 
      case field
      of PrimField vt ->
           let start_offset = pad offset $ alignOf vt
               end_offset = start_offset + sizeOf vt
           in start_offset : compute_offsets end_offset fields

         RecordField r ->
           let start_offset = pad offset $ alignOf r
               end_offset = start_offset + sizeOf r
           in start_offset : compute_offsets end_offset fields

         BytesField {} ->
           internalError "staticRecord: Field is not statically typed"

         AlignField n ->
           -- Adjust field alignment; don't output a field
           compute_offsets (pad offset n) fields

    compute_offsets offset [] = []

-- | Flatten a static record.  This produces a record with fields equivalent
-- to the original record, but all fields are inlined.  There are no record
-- fields.
flattenStaticRecord :: StaticRecord -> StaticRecord
flattenStaticRecord rc =
  record (flatten_fields 0 rc) (recordSize rc) (recordAlignment rc)
  where
    flatten_fields off rc = concatMap (flatten off) $ recordFields rc

    flatten base_off f =
      case fieldType f
      of PrimField {}   -> [add_offset base_off f]
         RecordField rc -> flatten_fields (base_off + fieldOffset f) rc

    add_offset off f = f {fieldOffset = off + fieldOffset f}

type Offset = Int

pad :: Offset -> Int -> Offset
pad off alignment = off + (negate off `mod` alignment)

-- | Compute the base-2 logarithm of a power of 2
log2 :: Int -> Int
log2 1 = 0
log2 n = 1 + log2 (n `shiftR` 1)

-------------------------------------------------------------------------------
-- Binary instances

instance Binary StaticField where
  put (Field off ty) = put off >> put ty
  get = Field <$> get <*> get

instance Binary StaticFieldType where
  put (PrimField pt) = putWord8 0 >> put pt
  put (RecordField rt) = putWord8 1 >> put rt
  put (BytesField sz al) = putWord8 2 >> put sz >> put al
  put (AlignField al) = putWord8 3 >> put al
  get = getWord8 >>= pick
    where
      pick 0 = PrimField <$> get
      pick 1 = RecordField <$> get
      pick 2 = BytesField <$> get <*> get
      pick 3 = AlignField <$> get

instance Binary StaticRecord where
  put (Rec fs sz al) = put sz >> put al >> put fs
  get = do sz <- get
           al <- get
           fs <- get
           return (Rec fs sz al)

