
{-# LANGUAGE FlexibleInstances, StandaloneDeriving, TypeSynonymInstances #-}
module LowLevel.Record where

import Control.Applicative
import Data.Binary
import Data.Bits

import Common.Error
import LowLevel.BinaryUtils
import LowLevel.Types
import {-# SOURCE #-} LowLevel.Syntax

-- | A mutability flag
data Mutability = Mutable | Constant
                deriving(Eq, Ord, Show, Enum, Bounded)

-- | A record type, consisting of fields with known type and alignment.
--
-- Record types are used for computing the physical layout of data and
-- generating load and store instructions.
data Record t =
  Record { recordFields_ :: ![Field t]
         , recordSize_ :: !t
         , recordAlignment_ :: !t
         }

-- | A record field.  A field contains information about its offset, whether
--   its value is mutable, and what data type it contains.  Mutability only
--   applies to records stored in memory.
--
--   Note that a 'Constant' field is not necessarily constant: it could be
--   a record containing some mutable fields.  You can check for this with
--   'isFullyConst'.
--
-- If a field is a mutable record, then all its sub-fields are mutable.
--
-- Record fields never have 'AlignField' type.
data Field t =
  Field { fieldOffset :: !t
        , fieldMutable :: !Mutability
        , fieldType  :: !(FieldType t)
        }

-- | Create a record field specification
mkField' :: t -> Mutability -> FieldType t -> Field t
mkField' offset mutable field_type =
  let ftype = case mutable
              of Mutable  -> makeFieldTypeMutable field_type
                 Constant -> field_type
  in case field_type 
     of AlignField _ -> internalError "mkField: Unexpected alignment field"
        _ -> Field offset mutable ftype

mkField :: Int -> Mutability -> StaticFieldType -> StaticField
mkField = mkField'

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
record = Record

recordFields :: Record t -> [Field t]
recordFields = recordFields_

isMutableField :: Field t -> Bool
isMutableField f = fieldMutable f == Mutable

isConstField :: Field t -> Bool
isConstField f = fieldMutable f == Constant

isFullyConst :: Field t -> Bool
isFullyConst f = isConstField f && all_const_fields (fieldType f)
  where
    all_const_fields (RecordField rec) = all isFullyConst $ recordFields rec
    all_const_fields _ = True

-- | Make all fields of a record mutable, recursively.
makeRecordMutable :: Record t -> Record t
makeRecordMutable rec =
  rec {recordFields_ = map makeFieldMutable $ recordFields_ rec} 
    
makeFieldMutable :: Field t -> Field t
makeFieldMutable fld =
  case fieldMutable fld  
  of Mutable  -> fld
     Constant -> fld { fieldMutable = Mutable
                     , fieldType = makeFieldTypeMutable $ fieldType fld}

makeFieldTypeMutable :: FieldType t -> FieldType t
makeFieldTypeMutable (RecordField rec) = RecordField (makeRecordMutable rec)
makeFieldTypeMutable t = t

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

-- | Apply a transformation to all fields of a record, possibly changing
--   the number of fields.  The transformation must preserve the sizes and 
--   alignments of all fields, and of the entire record.
concatMapRecordFields f rc =
  rc {recordFields_ = concatMap f $ recordFields_ rc}

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

deriving instance Ord StaticRecord
deriving instance Ord StaticFieldType
deriving instance Ord StaticField

-- | In a record with dynamic layout, sizes and offsets are computed run-time
-- values.  Offsets are signed native integers.  Size and alignment are
-- unsigned native integers.
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
  
  pointerlessness (PrimField v) = pointerlessness v
  pointerlessness (RecordField r) = pointerlessness r
  pointerlessness (BytesField _ _) = False -- Unknown, assume it has pointers

instance HasSize (Record Int) where
  sizeOf = recordSize
  alignOf = recordAlignment
  pointerlessness = all pointerlessness . recordFields

instance HasSize (Field Int) where
  sizeOf f = sizeOf (fieldType f)
  alignOf f = alignOf (fieldType f)
  pointerlessness f = pointerlessness (fieldType f)

constStaticRecord :: [StaticFieldType] -> StaticRecord
constStaticRecord fs = staticRecord [(Constant, f) | f <- fs]

mutableStaticRecord :: [StaticFieldType] -> StaticRecord
mutableStaticRecord fs = staticRecord [(Mutable, f) | f <- fs]

staticRecord :: [(Mutability, StaticFieldType)] -> StaticRecord
staticRecord fs = let
  field_offsets = compute_offsets 0 fs
  real_fields   = filter (not . isAlignField . snd) fs
  alignment     = foldr lcm 1 $ map (alignOf . snd) real_fields
  size          = if null real_fields
                  then 0
                  else last field_offsets + sizeOf (snd $ last real_fields)
  fields        = [ mkField o m t
                  | (o, (m, t)) <- zip field_offsets real_fields]
  in record fields size alignment
  where
    -- Each field starts at the offset of the previous field, plus the
    -- previous field's size, plus some padding bytes
    compute_offsets offset ((_, field) : fields) = 
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

-- | Remove record fields that have type 'UnitType'.
removeUnitFields :: StaticRecord -> StaticRecord
removeUnitFields rc = concatMapRecordFields flatten_field rc
  where
    flatten_field fld = 
      case fieldType fld
      of PrimField UnitType -> []
         PrimField _        -> [fld]
         RecordField rc     -> [fld {fieldType = RecordField $ removeUnitFields rc}]

type Offset = Int

pad :: Offset -> Int -> Offset
pad off alignment = off + (negate off `mod` alignment)

-- | Compute the base-2 logarithm of a power of 2
log2 :: Int -> Int
log2 1 = 0
log2 n = 1 + log2 (n `shiftR` 1)

-------------------------------------------------------------------------------
-- Binary instances

instance Binary Mutability where
  put = putEnum
  get = getEnum "Mutability.get"

instance Binary StaticField where
  put (Field off m ty) = put off >> put m >> put ty
  get = Field <$> get <*> get <*> get

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
  put (Record fs sz al) = put sz >> put al >> put fs
  get = do sz <- get
           al <- get
           fs <- get
           return (Record fs sz al)

