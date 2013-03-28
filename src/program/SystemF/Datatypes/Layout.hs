{-| Memory layouts and object size computation.

A 'Layout' is a 'Structure' with type information removed.
Whereas a 'Structure' can be dependent on 'Type's, 
a 'Layout' is dependent on 'L.Val's holding run-time type information.
Information about contents may be lost or approximated in this process.

An 'AlgLayout' has more detailed information about the memory layout
strategy for algebraic data types.  Specifically, it expresses
decisions about how data structures are tagged.  All size and layout
computation for algebraic data types is performed by first creating an 
'AlgLayout'.

-}

{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleContexts #-}
module SystemF.Datatypes.Layout
       (Layout(..),
        LayoutField,
        HasAlgHeader(..),
        HeaderType,
        HeaderData, headerType, headerConIndex,
        HeaderOffsets,
        AlgDisjunct, algDisjunctConIndex, algDisjunctHeader, algDisjunctFields,
        AlgData,
        mapMAlgData,
        algDataNumConstructors,
        algDataBoxing,
        algDataTagType,
        algDataHeaderType,
        isEnumeration,
        disjunct,
        disjuncts,
        disjunctData,
        mapDisjuncts, mapMDisjuncts,
        checkDisjunct,
        algebraicData,
        disjunctsTag,
        IntroP, IntroS, IntroE, ElimP, ElimS, ElimE,
        AlgValueType,
        AlgObjectType,
        MemoryField(..),
        memoryFieldSize,
        memoryLayout,
        LLDynTypeInfo,
        computeLayout,
        memorySize,
        headerLayout,
        algUnboxedLayout,
        disjunctLayout,
        disjunctLayout1,
        writeHeader,
        readHeaderTag)
where

import Control.Monad
import Data.Maybe

import Common.Error
import SystemF.Datatypes.DynamicTypeInfo
import SystemF.Datatypes.Structure
import SystemF.Datatypes.Util
import Type.Environment
import Type.Type
import LowLevel.Build
import LowLevel.CodeTypes
import qualified LowLevel.Syntax as L

-- | A 'Layout' contains information about how a data type is stored in
--   local variables and/or in memory.  Layouts are used for computing the
--   size and alignment of types, for computing the low-level data types 
--   corresponding to value types.
--   Layouts also contain 'AlgData' values for computing the
--   low-level representation of algebraic data types.
data Layout =
    -- | A primitive type
    PrimLayout !PrimType

    -- | A block of memory with unspecified contents.  Only the size and
    --   alignment are known.
  | BlockLayout {-# UNPACK #-}!SizeAlign

    -- | A tagged sum of products.  It's given as the common prefix
    --   followed by the members of each sum.
    --
    --   Fields are annotated with a kind (val, box, or bare).
    --   The kind does not affect the representation in registers or memory.
    --   It affects how field read/write code is generated.
  | DataLayout !(AlgData LayoutField)

-- | A field of a 'Layout' includes its kind
type LayoutField = (BaseKind, Layout)

-- | Information about an algebraic data type's header.  A header
--   consists of everything in one disjunct except the data type's fields.
class HasAlgHeader a where
  type AlgBoxInfo a
  type AlgTagInfo a

  -- | Extract the object header description.
  --   Returns 'Nothing' if there is no object header.
  boxInfo :: a -> Maybe (AlgBoxInfo a)
  
  -- | Extract the description of a constructor tag held in a local variable.
  --   Returns 'Nothing' if there is no tag.
  varTagInfo :: a -> Maybe (AlgTagInfo a)

  -- | Extract the description of a constructor tag held in memory.
  --   Returns 'Nothing' if there is no tag.
  memTagInfo :: a -> Maybe (AlgTagInfo a)

-- | A description of a tag.
--
--   For most data types, 'varTag' and 'memTag' hold the same value.
--   The exception is the boolean type, which is represented differently in
--   memory and in local variables.
data TagPair a = TagPair {varTag :: a, memTag :: a}

-- | Representation of an algebraic data type's header fields.
--
--   A header may have a boxed object header and may have a constructor tag.
data HeaderType = HeaderType !Boxing !(Maybe (TagPair ValueType))

instance HasAlgHeader HeaderType where
  type AlgBoxInfo HeaderType = ()
  type AlgTagInfo HeaderType = ValueType
  boxInfo (HeaderType b _) = ifBoxed b ()
  varTagInfo (HeaderType _ t) = fmap varTag t
  memTagInfo (HeaderType _ t) = fmap memTag t

-- | Representation of an algebraic data type's header value.
data HeaderData = HeaderData !HeaderType !Int

instance HasAlgHeader HeaderData where
  type AlgBoxInfo HeaderData = ()
  type AlgTagInfo HeaderData = L.Val
  boxInfo (HeaderData ty _) = boxInfo ty
  varTagInfo (HeaderData ty n) = fmap (\t -> tagValue t n) $ varTagInfo ty
  memTagInfo (HeaderData ty n) = fmap (\t -> tagValue t n) $ memTagInfo ty

headerType :: HeaderData -> HeaderType
headerType (HeaderData ty _) = ty

headerConIndex :: HeaderData -> Int
headerConIndex (HeaderData _ n) = n

-- | Field offsets for an algebraic data type's header.
--
--   The object header, if present, is always at offset 0.
--   The tag is at the given offset.
data HeaderOffsets = HeaderOffsets !Boxing !(Maybe (TagPair Off))

headerOffsetPair :: Maybe Off -> Maybe (TagPair Off)
headerOffsetPair Nothing  = Nothing
headerOffsetPair (Just t) = Just (TagPair e t)
  where
    -- Local variables are not addressible, so there is no value for this field
    e = internalError "headerOffsetPair: No local variable offset"

instance HasAlgHeader HeaderOffsets where
  type AlgBoxInfo HeaderOffsets = ()
  type AlgTagInfo HeaderOffsets = Off
  boxInfo (HeaderOffsets b _) = ifBoxed b ()

  -- This function should not be called.
  -- Local variables are not addressible.
  varTagInfo (HeaderOffsets _ t) =
    internalError "HeaderOffsets.varTagInfo: Unexpected use of this function"

  memTagInfo (HeaderOffsets _ t) = fmap memTag t

-- | One member of an algebraic data type.  Consists of a header
--   and possibly a list of fields.  A list of fields is not given for
--   enumerations, and is given for all other types.
data AlgDisjunct a = AlgDisjunct !HeaderData [a]

instance Functor AlgDisjunct where
  fmap f (AlgDisjunct header fs) = AlgDisjunct header (fmap f fs)

instance HasAlgHeader (AlgDisjunct a) where
  type AlgBoxInfo (AlgDisjunct a) = AlgBoxInfo HeaderData
  type AlgTagInfo (AlgDisjunct a) = AlgTagInfo HeaderData
  boxInfo (AlgDisjunct header _) = boxInfo header  
  varTagInfo (AlgDisjunct header _) = varTagInfo header
  memTagInfo (AlgDisjunct header _) = memTagInfo header

algDisjunctConIndex :: AlgDisjunct a -> Int
algDisjunctConIndex d = headerConIndex $ algDisjunctHeader d

algDisjunctHeader (AlgDisjunct h _) = h

algDisjunctFields (AlgDisjunct _ fs) = fs

-- | Representation of an algebraic data type.
data AlgData a =
    -- | An enumeration
    TagD 
    { adBoxing    :: !Boxing 
    , adTagType   :: !ValueType 
    , adSize      :: !Int
    }
    -- | The boolean type, a special case of an enumeration
  | BoolD
    -- | A product type
  | ProductD
    { adBoxing    :: !Boxing 
    , adFields    :: [a]
    }
    -- | A tagged sum type
  | SumD
    { adBoxing    :: !Boxing
    , adTagType   :: !ValueType
    , adDisjuncts :: [[a]]
    }

instance Functor AlgData where
  fmap f (TagD b t s) = TagD b t s
  fmap f BoolD        = BoolD
  fmap f (ProductD b fs) = ProductD b (map f fs)
  fmap f (SumD b t ds) = SumD b t (map (map f) ds)

mapMAlgData :: Monad m => (a -> m b) -> AlgData a -> m (AlgData b)
mapMAlgData f (TagD b t s)    = return $ TagD b t s
mapMAlgData f BoolD           = return BoolD
mapMAlgData f (ProductD b fs) = ProductD b `liftM` mapM f fs
mapMAlgData f (SumD b t ds)   = SumD b t `liftM` mapM (mapM f) ds

-- | Number of data constructors of this algebraic data type
algDataNumConstructors :: AlgData a -> Int
algDataNumConstructors (TagD {adSize = n})       = n
algDataNumConstructors BoolD                     = 2
algDataNumConstructors (ProductD {})             = 1
algDataNumConstructors (SumD {adDisjuncts = ds}) = length ds

algDataBoxing :: AlgData a -> Boxing
algDataBoxing BoolD = NotBoxed 
algDataBoxing d     = adBoxing d

-- | Get the tag type used to represent this data type in a local variable.
--   For all data types except the boolean type, this is also the tag type
--   used to represent this data type in memory.
algDataTagType :: AlgData a -> Maybe ValueType
algDataTagType (TagD {adTagType = t}) = Just t
algDataTagType BoolD                  = Just $ PrimType nativeIntType
algDataTagType (ProductD {})          = Nothing
algDataTagType (SumD {adTagType = t}) = Just t

algDataHeaderType :: AlgData a -> HeaderType
algDataHeaderType BoolD =
  let var_tag = PrimType nativeIntType
      mem_tag = PrimType (case tagType 2 of Just t -> t)
  in HeaderType NotBoxed (Just $ TagPair var_tag mem_tag)

algDataHeaderType d =
  let tag = do t <- algDataTagType d
               return $ TagPair t t
  in HeaderType (algDataBoxing d) tag

isEnumeration :: AlgData a -> Bool
isEnumeration (TagD {}) = True
isEnumeration BoolD     = True
isEnumeration _         = False

disjunct :: Int -> AlgData a -> AlgDisjunct a
disjunct n d
  | n < 0 || n >= algDataNumConstructors d =
      internalError "disjunct: Out of bounds"

disjunct n d =
  let h_type = algDataHeaderType d
      fields = case d
               of TagD {}                  -> []
                  BoolD {}                 -> []
                  ProductD {adFields = fs} -> fs
                  SumD {adDisjuncts = fss} -> fss !! n
  in AlgDisjunct (HeaderData h_type n) fields                  

disjuncts :: AlgData a -> [AlgDisjunct a]
disjuncts adt = [disjunct i adt | i <- [0 .. algDataNumConstructors adt - 1]]

disjunctData :: Int -> [L.Val] -> AlgData a -> AlgDisjunct L.Val
disjunctData n fs d =
  let header = HeaderData (algDataHeaderType d) n
  in AlgDisjunct header fs

mapDisjuncts :: (AlgDisjunct a -> b) -> AlgData a -> [b]
mapDisjuncts t d = map t $ disjuncts d

mapMDisjuncts :: Monad m => (AlgDisjunct a -> m b) -> AlgData a
              -> m [b]
mapMDisjuncts t d = mapM t $ disjuncts d

-- | This function performs the following consistency checks between a
--   disjunct and an algebraic data type:
--   
-- * It checks that the constructor index is valid
--
-- * It checks that the number of fields is correct
checkDisjunct :: AlgData b -> AlgDisjunct a -> c -> c
checkDisjunct adt dj x
  | i < 0 || i >= algDataNumConstructors adt =
      internalError "checkDisjunct: Constructor index out of range"
  | n_fields /= length (algDisjunctFields $ disjunct i adt) =
      internalError "checkDisjunct: Wrong number of fields"
  | otherwise = x
  where
    i = algDisjunctConIndex dj
    n_fields = length (algDisjunctFields dj)

-- | Create an algebraic data type layout
algebraicData :: Boxing -> [[a]] -> AlgData a
algebraicData boxing disjuncts
  -- An enumeration type: has a tag, but no fields
  -- A unit type also counts as an enumeration type.
  | all null disjuncts = TagD boxing tag_type n_disjuncts

  -- A product type
  | [fields] <- disjuncts = ProductD boxing fields

  -- General case, a sum of products type
  | otherwise = SumD boxing tag_type disjuncts
  where
    n_disjuncts = length disjuncts
    tag_type = case disjunctsTag n_disjuncts
               of Just t  -> PrimType t
                  Nothing -> PrimType UnitType

disjunctsTag = tagType

-------------------------------------------------------------------------------
-- Algebraic data introduction and elimination

type IntroP r = [L.Val] -> GenM r            -- ^ Create a product
type IntroS r = AlgDisjunct L.Val -> GenM r  -- ^ Create a sum
type IntroE r = Int -> GenM r                -- ^ Create an enumeration
type ElimP r = L.Val -> IntroP r -> GenM r   -- ^ Examine a product
type ElimS r = L.Val -> IntroS r -> GenM r   -- ^ Examine a sum
type ElimE r = L.Val -> IntroE r -> GenM r   -- ^ Examine an enumeration

-------------------------------------------------------------------------------
-- Algebraic data layouts in local variables

-- | An algebraic data type of kind @val@, held in local variables.
type AlgValueType = AlgData ValueType

-------------------------------------------------------------------------------
-- Algebraic data layouts in memory

-- | An algebraic data type held in memory.
type AlgObjectType = AlgData MemoryField

-- | A field of an algebraic data type held in memory.
data MemoryField =
    -- | A boxed field.  No information is needed, since boxed field is
    --   just a pointer.
    BoxedField

    -- | A field of value type.  Its memory layout is held here for later use.
    --
    --   The layout may be converted to a value type.  Typing rules
    --   ensure that the layout can be converted to a value type if
    --   needed.  However, it's not possible to convert to a value
    --   type in general.
  | ValField !Layout

    -- | A field of bare type.  Only its size and alignment are needed.
  | BareField !SizeAlign

-- | Get the size of a field as it exists in memory
memoryFieldSize :: MemoryField -> GenM SizeAlign
memoryFieldSize BoxedField    = return $ valueSizeAlign (PrimType OwnedType)
memoryFieldSize (ValField l)  = memorySize l
memoryFieldSize (BareField s) = return s

-- | Compute the memory layout characteristics of a data type's fields
memoryLayout :: AlgData LayoutField -> GenM AlgObjectType
memoryLayout adt = mapMAlgData memory_field adt
  where
    -- Create a 'memoryField' from the fields of a 'Layout'
    memory_field :: LayoutField -> GenM MemoryField
    memory_field (ValK, l)  = return $ ValField l
    memory_field (BoxK, _)  = return $ BoxedField
    memory_field (BareK, l) = liftM BareField $ memorySize l

-------------------------------------------------------------------------------
-- Computing layouts

-- | Dynamic type information in terms of low-level values
type LLDynTypeInfo = DynTypeInfo SizeAlign SizeAlign L.Val

instance DefaultValue SizeAlign where dummy = emptySizeAlign
                                     
instance DefaultValue L.Val where dummy = nativeIntV 0

-- | Determine the physical layout of a type, using the arguments to choose
--   layouts for unknowns.
computeLayout :: LLDynTypeInfo  -- ^ Dynamic type information
              -> BaseKind       -- ^ Kind of the data structure
              -> Structure
              -> GenM Layout
computeLayout type_info kind layout =
  case layout
  of PrimStruct pt            -> return $ PrimLayout pt
     BoolStruct               -> return $ DataLayout BoolD
     ArrStruct t ts           -> arr_layout t ts
     DataStruct (Data tag fs) -> sum_layout tag fs
     ForallStruct fa          -> forall_layout fa
     VarStruct v              -> var_layout v
     UninhabitedStruct        -> internalError "computeLayout: Uninhabited"
  where
    continue k l = computeLayout type_info k l

    var_layout v
      | kind == ValK =
          BlockLayout `liftM` lookupValTypeInfo type_info v
      | kind == BareK =
          BlockLayout `liftM` lookupBareTypeInfo type_info v
      | otherwise =
          internalError "computeLayout: Unexpected kind"

    sum_layout _ [] =
      internalError "computeLayout: Uninhabited type"

    -- General case
    sum_layout tag alts = do
      -- Compute layouts of all fields
      alt_layouts <- mapM alt_layout alts
      -- Decide on representation
      let boxing = case kind
                   of BoxK -> IsBoxed
                      _    -> NotBoxed
      return $ DataLayout $ algebraicData boxing alt_layouts

    -- Layouts of fields of a case alternative
    alt_layout (Alternative decon fs) =
      assumeBinders (deConExTypes decon) $ mapM field_layout fs

    field_layout (k, t)
      | k == BoxK = return (BoxK, PrimLayout OwnedType)
      | otherwise = do l <- continue k =<< computeStructure t
                       return (k, l)

    forall_layout (Forall b t) =
      assumeBinder b $ continue kind =<< computeStructure t

    arr_layout size elem = do
      size_val <- lookupIntTypeInfo type_info size
      -- Array elements are bare objects
      elem_size <- memorySize =<< continue BareK =<< computeStructure elem
      liftM BlockLayout $ arraySize size_val elem_size

-- | Get the size and alignment of an unboxed object
--   described by a physical layout
memorySize :: Layout -> GenM SizeAlign
memorySize (PrimLayout pt) =
  return $ SizeAlign (nativeWordV $ sizeOf pt) (nativeWordV $ alignOf pt)
  
memorySize (BlockLayout sa) =
  return sa

memorySize (DataLayout adt) = do
  (_, _, size) <- algUnboxedLayout =<< memoryLayout adt
  return size

-- | Compute the size and field offsets of an object header
headerLayout :: HeaderType -> GenM (HeaderOffsets, OffAlign)
headerLayout (HeaderType boxing m_tag) = do
  -- Object header, if boxed
  (_, off1) <-
    padOffMaybe emptyOffAlign $
    ifBoxed boxing $ valueSizeAlign (PrimType OwnedType)

  -- Tag, if tagged
  (tag_off, off2) <-
    padOffMaybe off1 $ fmap (valueSizeAlign . memTag) m_tag

  return (HeaderOffsets boxing (headerOffsetPair tag_off), off2)

-- | Compute the size and field offsets of all disjuncts of an unboxed
--   algebraic data type.
algUnboxedLayout :: AlgData MemoryField
                 -> GenM (HeaderOffsets, [[Off]], SizeAlign)
algUnboxedLayout adt = do
  -- Get header layout
  (header_offsets, off1) <- headerLayout $ algDataHeaderType adt

  -- Get field layouts for each disjunct
  let field_layout (AlgDisjunct _ fields) =
        disjunctLayout1 header_offsets off1 fields
  field_layouts <- mapMDisjuncts field_layout adt

  -- Compute actual size
  let (_, field_offsetss, sizes) = unzip3 field_layouts
  total_size <- overlays sizes

  return (header_offsets, field_offsetss, total_size)

-- | Compute the size and field offsets of one disjunct of an algebraic
--   data type.
--
--   For a boxed object, this is the object's actual size.
--   For a bare or value object, the actual size is the maximum over all
--   disjuncts.
disjunctLayout :: AlgDisjunct MemoryField
               -> GenM (HeaderOffsets, [Off], SizeAlign)
disjunctLayout (AlgDisjunct header fields) = do
  (header_offsets, off1) <- headerLayout $ headerType header
  disjunctLayout1 header_offsets off1 fields

-- | This is the remainder of 'disjunctLayout' after the header has been
--   calculated.
disjunctLayout1 header_offsets off1 fs = do
  (field_offsets, size) <- disjunctFieldLayout off1 fs
  return (header_offsets, field_offsets, size)

disjunctFieldLayout :: OffAlign -> [MemoryField] -> GenM ([Off], SizeAlign)
disjunctFieldLayout start_off fields = do
  (field_offsets, end_off) <- layout_fields start_off fields
  size <- offAlignToSize end_off
  return (field_offsets, size)
  where
    layout_fields off (f:fs) = do
      (f_offset, off2) <- layout_field off f
      (fs_offsets, off3) <- layout_fields off2 fs
      return (f_offset : fs_offsets, off3)

    layout_fields off [] = return ([], off)

    layout_field off f = padOff off =<< memoryFieldSize f

-------------------------------------------------------------------------------
-- Header operations

-- | Write an object header to memory
writeHeader :: HeaderData -> HeaderOffsets -> L.Val -> GenM ()
writeHeader hdata hoff ptr = do
  -- TODO: Write object header if present
  write_tag (memTagInfo hdata) (memTagInfo hoff)
  where
    write_tag Nothing Nothing = return ()
    write_tag (Just tag_val) (Just (Off tag_off)) =
      primStoreOffConst (L.valType tag_val) ptr tag_off tag_val

-- | Read an object header's tag from memory
readHeaderTag :: HeaderType -> HeaderOffsets -> L.Val -> GenM (Maybe L.Val)
readHeaderTag htype hoff ptr =
  case (memTagInfo htype, varTagInfo htype, memTagInfo hoff)
  of (Nothing, Nothing, Nothing) ->
       return Nothing
     (Just mem_ty, Just val_ty, Just (Off off)) -> do
       loaded_tag <- primLoadOffConst mem_ty ptr off
       tag <- castTag mem_ty val_ty loaded_tag
       return $ Just tag

-- | Cast a tag value from one primitive type to another
castTag :: ValueType -> ValueType -> L.Val -> GenM L.Val
castTag from_ty to_ty val
  -- If types are the same, return the value
  | from_ty == to_ty =
      return val

  | PrimType (IntType {}) <- from_ty, PrimType (IntType {}) <- to_ty =
      primCastZ to_ty val
                      