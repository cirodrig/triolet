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
        algDataVarTagType,
        algDataMemTagType,
        algDataHeaderType,
        isEnumeration,
        disjunct,
        disjuncts,
        disjunctData,
        mapDisjuncts, mapMDisjuncts,
        checkDisjunct,
        algebraicData,
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
        writeEnumerationHeader,
        writeHeader,
        readHeaderValue,
        castTagToWord)
where

import Control.Monad
import Data.Maybe
import Debug.Trace

import Common.Error
import SystemF.Datatypes.DynamicTypeInfo
import SystemF.Datatypes.Structure
import SystemF.Datatypes.Util
import Type.Environment
import Type.Type
import LowLevel.Build
import LowLevel.CodeTypes
import qualified LowLevel.Syntax as L

-- | The type of a reference to a type object
typeObjectReferenceType :: ValueType
typeObjectReferenceType = PrimType OwnedType

-- | The type of an unboxed object tag held in a variable
variableTagType :: ValueType
variableTagType = PrimType nativeIntType

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
  type AlgTagInfo a

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

uniformTagPair x = TagPair x x

-- | Representation of an algebraic data type's header field.
--
--   For boxed data, the header is a type object reference.
--
--   For unboxed data, the header type depends on whether it is an
--   enumerative type, how many data constructors the type has,
--   and whether the header is in registers or in memory.
data HeaderType =
    BoxedHeaderType 
  | UnboxedHeaderType !Bool {-#UNPACK#-}!Int

isBoxedHeaderType BoxedHeaderType = True
isBoxedHeaderType (UnboxedHeaderType _ _) = False

instance HasAlgHeader HeaderType where
  type AlgTagInfo HeaderType = ValueType
  varTagInfo BoxedHeaderType             = Just typeObjectReferenceType
  varTagInfo (UnboxedHeaderType True  n) = Just $ PrimType $ unboxedEnumVarTagType n
  varTagInfo (UnboxedHeaderType False n) = fmap PrimType $ unboxedVarTagType n
  memTagInfo BoxedHeaderType             = Just typeObjectReferenceType
  memTagInfo (UnboxedHeaderType True n)  = Just $ PrimType $ unboxedEnumMemTagType n
  memTagInfo (UnboxedHeaderType False n) = fmap PrimType $ unboxedMemTagType n

-- | Data that identifies one disjunct of an algebraic data type.
data HeaderData =
    BoxedHeaderData
    { headerConIndex :: {-# UNPACK #-} !Int -- ^ Which data constructor
    , _headerValue   :: !L.Val              -- ^ The header tag value
    }
  | UnboxedHeaderData 
    { _headerType    :: !HeaderType
    , headerConIndex :: {-# UNPACK #-} !Int -- ^ Which data constructor
    }

instance HasAlgHeader HeaderData where
  type AlgTagInfo HeaderData = L.Val
  varTagInfo (BoxedHeaderData _ v) = Just v
  varTagInfo (UnboxedHeaderData ty n) = fmap (\t -> unboxedTagValue t n) $ varTagInfo ty
  memTagInfo (BoxedHeaderData _ v) = Just v
  memTagInfo (UnboxedHeaderData ty n) = fmap (\t -> unboxedTagValue t n) $ memTagInfo ty

headerType :: HeaderData -> HeaderType
headerType (BoxedHeaderData _ _) = BoxedHeaderType
headerType (UnboxedHeaderData ty _) = ty

-- | Field offsets for an algebraic data type's header.
--   The Boolean is True if there is a header, False if there is none.
--   The header is always at offset 0.
--   (This data structure is left over from when headers were more complex.)
data HeaderOffsets = HeaderOffsets Bool

headerOffsetPair :: Maybe Off -> Maybe (TagPair Off)
headerOffsetPair Nothing  = Nothing
headerOffsetPair (Just t) = Just (TagPair e t)
  where
    -- Local variables are not addressible, so there is no value for this field
    e = internalError "headerOffsetPair: No local variable offset"

instance HasAlgHeader HeaderOffsets where
  type AlgTagInfo HeaderOffsets = Bool

  -- This function should not be called.
  -- Local variables are not addressible.
  varTagInfo (HeaderOffsets _) =
    internalError "HeaderOffsets.varTagInfo: Unexpected use of this function"

  memTagInfo (HeaderOffsets b) = Just b

-- | One member of an algebraic data type.  Consists of a header
--   and possibly a list of fields.  A list of fields is not given for
--   enumerations, and is given for all other types.
data AlgDisjunct a = AlgDisjunct !HeaderData [a]

instance Functor AlgDisjunct where
  fmap f (AlgDisjunct header fs) = AlgDisjunct header (fmap f fs)

instance HasAlgHeader (AlgDisjunct a) where
  type AlgTagInfo (AlgDisjunct a) = AlgTagInfo HeaderData
  varTagInfo (AlgDisjunct header _) = varTagInfo header
  memTagInfo (AlgDisjunct header _) = memTagInfo header

algDisjunctConIndex :: AlgDisjunct a -> Int
algDisjunctConIndex d = headerConIndex $ algDisjunctHeader d

algDisjunctHeader (AlgDisjunct h _) = h

algDisjunctFields (AlgDisjunct _ fs) = fs

-- | Representation of an algebraic data type.
--
--   This has all the information needed to construct and deconstruct objects,
--   _except_ that it doesn't say how to create the header of a boxed object.
data AlgData a =
    -- | An enumeration
    TagD 
    { adBoxing    :: !Boxing 
    , adSize      :: !Int
    }
    -- | A product type
  | ProductD
    { adBoxing    :: !Boxing 
    , adFields    :: [a]
    }
    -- | A tagged sum type
  | SumD
    { adBoxing    :: !Boxing
    , adDisjuncts :: [[a]]
    }

instance Functor AlgData where
  fmap f (TagD b s)      = TagD b s
  fmap f (ProductD b fs) = ProductD b (map f fs)
  fmap f (SumD b ds)     = SumD b (map (map f) ds)

mapMAlgData :: Monad m => (a -> m b) -> AlgData a -> m (AlgData b)
mapMAlgData f (TagD b s)      = return $ TagD b s
mapMAlgData f (ProductD b fs) = ProductD b `liftM` mapM f fs
mapMAlgData f (SumD b ds)     = SumD b `liftM` mapM (mapM f) ds

-- | Number of data constructors of this algebraic data type
algDataNumConstructors :: AlgData a -> Int
algDataNumConstructors (TagD {adSize = n})       = n
algDataNumConstructors (ProductD {})             = 1
algDataNumConstructors (SumD {adDisjuncts = ds}) = length ds

-- | Number of fields in a disjunct of this algebraic data type
algDataNumFields :: AlgData a -> Int -> Int
algDataNumFields adt i
  | i < 0 || i >= algDataNumConstructors adt =
      internalError "algDataNumFields: Out of range"
  | otherwise =
      case adt
      of TagD {}                  -> 0
         ProductD {adFields = fs} -> length fs
         SumD {adDisjuncts = ds}  -> length $ ds !! i

algDataBoxing :: AlgData a -> Boxing
algDataBoxing d     = adBoxing d

-- | Get the tag types used to represent this data type.
--
--   When in a variable, unboxed types are always tagged with a word
--   and boxed types are always tagged with an owned pointer.
--   When in memory, boxed types are always tagged with an owned pointer.
--   Unboxed types in memory have an unsigned int tag, where the number of
--   disjuncts may vary.
algDataTagType :: AlgData a -> Maybe (TagPair ValueType)
algDataTagType ad = 
  case ad
  of TagD {} -> let t_var = unboxedEnumVarTagType nc
                    t_mem = unboxedEnumMemTagType nc
                in Just $ TagPair (PrimType t_var) (PrimType t_mem)
     ProductD {} -> Nothing
     SumD {} -> do t_var <- unboxedVarTagType nc
                   t_mem <- unboxedMemTagType nc
                   Just $ TagPair (PrimType t_var) (PrimType t_mem)
  where
    nc = algDataNumConstructors ad

algDataVarTagType :: AlgData a -> Maybe ValueType
algDataVarTagType ad = fmap varTag $ algDataTagType ad

algDataMemTagType :: AlgData a -> Maybe ValueType
algDataMemTagType ad = fmap memTag $ algDataTagType ad

algDataHeaderType :: AlgData a -> HeaderType
algDataHeaderType d = 
  case adBoxing d
  of IsBoxed  -> BoxedHeaderType
     NotBoxed -> UnboxedHeaderType (isEnumeration d) (algDataNumConstructors d)

isEnumeration :: AlgData a -> Bool
isEnumeration (TagD {}) = True
isEnumeration _         = False

disjunct :: Int -> Maybe L.Val -> AlgData a -> AlgDisjunct a
disjunct n m_tyob d
  | n < 0 || n >= algDataNumConstructors d =
      internalError "disjunct: Out of bounds"
  | otherwise =
      let fields = case d
                   of TagD {}                  -> []
                      ProductD {adFields = fs} -> fs
                      SumD {adDisjuncts = fss} -> fss !! n
          h_type = algDataHeaderType d
          header = case (adBoxing d, m_tyob)
                   of (IsBoxed, Just tyob) -> BoxedHeaderData n tyob
                      (NotBoxed, Nothing)  -> UnboxedHeaderData h_type n
      in AlgDisjunct header fields

disjuncts :: AlgData a -> [AlgDisjunct a]
disjuncts adt 
  | adBoxing adt == IsBoxed =
      internalError "disjuncts: Cannot construct disjuncts of boxed type"
  | otherwise =
      [disjunct i Nothing adt | i <- [0 .. algDataNumConstructors adt - 1]]

disjunctData :: Int -> [L.Val] -> AlgData a -> AlgDisjunct L.Val
disjunctData n fs d
  | adBoxing d == IsBoxed =
      internalError "disjunctData: Cannot create boxed disjunct"
  | otherwise =
      let header = UnboxedHeaderData (algDataHeaderType d) n
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
  | n_fields /= algDataNumFields adt i =
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
  | all null disjuncts = TagD boxing (length disjuncts)

  -- A product type
  | [fields] <- disjuncts = ProductD boxing fields

  -- General case, a sum of products type
  | otherwise = SumD boxing disjuncts

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
computeLayout type_info kind structure =
  case structure
  of PrimStruct pt            -> return $ PrimLayout pt
     ArrStruct t ts           -> arr_layout t ts
     DataStruct (Data tag fs) -> sum_layout tag fs
     ForallStruct fa          -> forall_layout fa
     VarStruct v              -> var_layout v
     UninhabitedStruct        -> internalError "computeLayout: Uninhabited"
  where
    -- Compute the layout of a component of the structure. 
    -- Look up dynamic type info first; if not found, proceed structurally.
    continue k component_type 
      | k == ValK  = dyn =<< lookupValTypeInfo type_info component_type
      | k == BareK = dyn =<< lookupBareTypeInfo type_info component_type
      | otherwise     = traceShow k $ internalError "computeLayout: Unexpected kind"
      where
        -- If dynamic size information is available, use that
        dyn (Just sa) = return $ BlockLayout sa
        dyn Nothing   = static

        -- Otherwise, compute the structure statically
        static = computeLayout type_info k =<< computeStructure component_type

    var_layout v
      | kind == ValK =
          BlockLayout `liftM` lookupValTypeInfo' type_info v
      | kind == BareK =
          BlockLayout `liftM` lookupBareTypeInfo' type_info v
      | otherwise =
          traceShow kind $ internalError "computeLayout: Unexpected kind"

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
      | otherwise = do l <- continue k t
                       return (k, l)

    forall_layout (Forall b t) =
      assumeBinder b $ continue kind t

    arr_layout size elem = do
      size_val <- lookupIntTypeInfo' type_info size
      -- Array elements are bare objects
      elem_size <- memorySize =<< continue BareK elem
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
headerLayout ht = do
  -- Object header
  (_, off) <-
    padOffMaybe emptyOffAlign $ fmap valueSizeAlign $ memTagInfo ht

  return (HeaderOffsets $ isBoxedHeaderType ht, off)

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

-- | Write an enumerative unboxed value to memory, given its tag value
writeEnumerationHeader :: L.Val -> AlgData a -> L.Val -> GenM ()
writeEnumerationHeader n d@(TagD NotBoxed _) ptr = do
  let h_type = algDataHeaderType d
  -- Coerce the tag type
  let Just mem_tag_type = memTagInfo h_type
  n' <- castTag (PrimType nativeWordType) mem_tag_type n

  -- Write to memory
  primStoreConst mem_tag_type ptr n'

-- | Write an object header to memory
writeHeader :: HeaderData       -- ^ Header of object to write
            -> HeaderOffsets
            -> L.Val            -- ^ Address of object to write
            -> GenM ()
writeHeader hdata hoff ptr = write_tag (memTagInfo hdata)
  where
    write_tag Nothing = return ()
    write_tag (Just tag_val) =
      primStoreConst (L.valType tag_val) ptr tag_val

-- | Read an object header from memory.
readHeaderValue :: HeaderType -> HeaderOffsets -> L.Val -> GenM (Maybe L.Val)
readHeaderValue htype hoff ptr =
  case (memTagInfo htype, varTagInfo htype)
  of (Nothing, Nothing)         -> return Nothing
     (Just mem_ty, Just val_ty) -> liftM Just $ primLoadConst mem_ty ptr

-- | Extract a constructor index from an object header value.  The result
--   is a word whose value is in the range from 0 up to
--   the number of constructors minus 1.
--   If no tag value is given, the index is zero.
castTagToWord :: HeaderType -> Maybe L.Val -> GenM L.Val
castTagToWord _ Nothing = return $ nativeWordV 0

castTagToWord BoxedHeaderType (Just t) =
  -- Read constructor index from the type object
  selectTypeObjectConIndex t

castTagToWord htype@(UnboxedHeaderType {}) (Just t) =
  -- Cast tag to a word
  let Just mem_ty = memTagInfo htype
  in castTag mem_ty (PrimType nativeWordType) t

-- | Cast a tag value from one primitive type to another
castTag :: ValueType -> ValueType -> L.Val -> GenM L.Val
castTag from_ty to_ty val
  -- If types are the same, return the value
  | from_ty == to_ty =
      return val

  | PrimType (IntType {}) <- from_ty, PrimType (IntType {}) <- to_ty =
      primExtendZ to_ty val
