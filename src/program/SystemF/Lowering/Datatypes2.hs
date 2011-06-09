{-| Lowering of data type operations.

Lowering tells us how to use low-level data types to represent values of a
given System F type, as well as how to construct and inspect System F types.
There are two levels of detail: 'Layout' is just enough information to put
some data in a variable or in a field of another object.  'AlgLayout' is
enough information to construct a new object or deconstruct using a
case statement.

Value types are represented as low-level values.  Boxed types are represented
as owned references.  Bare types are represented as pointers.

The lowering code is organized in two levels of abstraciton.  The lower level 
of abstraction deals with basic data structure manipulation such as
tagging, boxing, aggregating multiple pieces into a larger structure
(used for product types), and branching based on a tag value 
(used for sum types).  The upper level of abstraction translates data
types into compositions of lower-level operations.
-}

{-# LANGUAGE ViewPatterns #-}
module SystemF.Lowering.Datatypes2
       (-- * Translation to low-level data types 
        lowerType,
        lowerTypeList,
        lowerFunctionType,

        -- * Creating layouts
        LayoutCon(..),
        Layout(ValLayout, MemLayout),
        getLayout,
        AlgLayout,
        getAlgLayout,

        -- * Code generation
        algebraicIntro,
        algebraicElim)
where

import Prelude hiding(foldr, elem, any, all, sum)

import Control.Monad hiding(forM_)
import Control.Monad.Trans
import Data.List(partition)
import Data.Foldable
import qualified Data.Map as Map
import Data.Maybe
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import Common.Supply
import Builtins.Builtins
import LowLevel.Build
import qualified LowLevel.Syntax as LL
import qualified LowLevel.CodeTypes as LL
import LowLevel.CodeTypes((!!:))
import qualified LowLevel.Print as LL
import SystemF.Syntax
import SystemF.Lowering.LowerMonad
import Type.Environment
import Type.Eval
import Type.Type

-- | Generate code to compute the maximum of a nonempty list of values.
-- The values are unsigned native ints (this is not checked).
computeMaximum :: [LL.Val] -> GenLower LL.Val
computeMaximum [] = internalError "computeMaximum: empty list"
computeMaximum (v:vs) = foldM nativeMaxUZ v vs

-- | Construct a writer function.  The function takes a pointer parameter and
--   initializes the data it points to.
writerFunction :: (LL.Val -> GenLower LL.Stm) -> Lower LL.Val
writerFunction mk_body = do
  return_param <- LL.newAnonymousVar (LL.PrimType LL.PointerType)
  fun_body <- execBuild [] (mk_body (LL.VarV return_param))
  let fun = LL.closureFun [return_param] [] fun_body
  return $ LL.LamV fun

returnWriterFunction :: (LL.Val -> GenLower LL.Stm) -> Lower LL.Stm
returnWriterFunction f =
  fmap (\v -> LL.ReturnE $ LL.ValA [v]) $ writerFunction f

fieldTypeToRecord :: LL.DynamicFieldType -> LL.DynamicRecord
fieldTypeToRecord (LL.RecordField r) = r
fieldTypeToRecord ftype = singletonDynamicRecord LL.Mutable ftype

{-

* Layout objects

Layout objects describe how to introduce data
(corresponding to constructor application),
eliminate data (corresponding to case statements), and access data that is
stored inside other data.

TODO: Describe semantics of values in Mem and LowLevel.  Describe the idea of
wrappers/adapters.  Describe algebraic data types.
-}

-- | A data constructor used for selecting the correct layout for a member of 
--   a sum type.  Tuple types have only one constructor, so no further
--   information is required.  Other algebraic data types are annotated with
--   a constructor name.
data LayoutCon = VarCon !Var | TupleCon
               deriving(Eq)

-- | An algebraic sum type.
data AlgSum a =
    -- | A sum type.  Each member of the sum has a unique tag.  Given a value,
    --   there is a way to compute the tag.
    Sum [(LL.Lit, a)] !(LL.Val -> GenLower LL.Val)

    -- | A non-sum type
  | One a

-- | Pick an arbitrary member of the sum type.
anyMember :: AlgSum a -> a
anyMember (Sum ((_, x) : _) _) = x
anyMember (One x) = x
anyMember (Sum _ _) = internalError "anyMember: Type is uninhabited"

findMember :: (a -> Bool) -> AlgSum a -> Maybe a
findMember f (Sum members _) = find f $ map snd members
findMember f (One x) = if f x then Just x else Nothing

sumTagType :: AlgSum a -> LL.PrimType
sumTagType (Sum ((lit, _) : _) _) = LL.litType lit
sumTagType (One _) = internalError "sumTagType: Not a sum"

instance Functor AlgSum where
  fmap f s = 
    case s 
    of Sum xs get_tag ->
         Sum [(tag, f x) | (tag, x) <- xs] get_tag
       One x -> One (f x)

instance Foldable AlgSum where
  foldr f z (Sum xs _) = foldr f z (map snd xs)
  foldr f z (One a) = f a z

-- | The layout of an algebraic data type that is passed by value.  This
--   includes objects whose representation is 'Value' or 'Boxed'.
--   Even though a boxed object is stored in memory, the /pointer/ to the
--   object is passed by value.
--
--   An erased value behaves like a unit value, except when it appears as a
--   field of another object.
data AlgValLayout = AVLayout !(AlgSum ValProd) | AVErased

-- | An algebraic product type
data ValProd =
    ValProd
    { valConstructor :: !LayoutCon
      
      -- | The low-level type of this layout
    , valType        :: ValLayout

      -- | Fields of the product type
    , valFields      :: ![Layout]

      -- | Create a value, given the fields of the product type.
      --   All fields including erased fields are passed.
    , valWriter      :: !([Initializer] -> Producer)

      -- | Extract the fields of the product type.
      --   All fields including erased fields are returned.
    , valReader      :: !(LL.Val -> GenLower [LL.Val])
    }

-- | The layout of a value that's stored in a field of an object.
--   An erased value behaves like a unit value when stored in memory, put into
--   a field, or taken out of a field.  An erased value disappers when it is
--   a field of a value object.
data ValLayout = VLayout !LL.ValueType | VErased

instance LL.HasSize ValLayout where
  pointerlessness VErased = True 
  pointerlessness (VLayout t) = LL.pointerlessness t

valIsPointerless :: ValLayout -> Bool
valIsPointerless (VLayout t)   = LL.pointerlessness t
valIsPointerless VErased = True

type Producer = GenLower LL.Val
type Writer = LL.Val -> GenLower ()

-- | An initializer.  Either put a value in a field or write into memory.
data Initializer = ValInit Producer | WriteInit Writer

fromProducer (ValInit m) = m
fromProducer _ = internalError "Expected a value, got a writer"

fromWriter (WriteInit m) = m
fromWriter _ = internalError "Expected a writer, got a value"

asWriter :: Initializer -> Writer
asWriter (WriteInit m) = m
asWriter (ValInit m) = \dst -> do
  val <- m
  primStoreMutable (LL.valType val) dst val

-- | The layout of an algebraic data type that is passed by reference.
type AlgMemLayout = AlgSum MemProd

-- | An algebraic product type
data MemProd =
    MemProd
    { memConstructor :: !LayoutCon
      
      -- | The layout details of this product type
    , memLayout       :: MemLayout

      -- | Fields of the product type
    , memFields       :: ![Layout]

      -- | Write the fields of the product type, when constructing a value
      --   with this layout
    , memWriter       :: !(LL.DynamicRecord -> [Initializer] -> Writer)

      -- | Read the fields of the product type, when using a @case@ statement
      --   to inspect data with this layout
    , memReader       :: !(LL.DynamicRecord -> LL.Val -> GenLower [LL.Val])
    }

data MemLayout =
  MLayout
  { -- | The data type when used as a field of a record,
    --   and its pointerlessness.
    memFieldType :: GenLower (LL.DynamicFieldType, LL.Val)
    
    -- | The data type as a record, and its pointerlessness.
  , memType :: GenLower (LL.DynamicRecord, LL.Val)

    -- | Whether an object with this layout is stored via an indirection.
    --   If 'True', then the layout consists of a single pointer in memory
    --   that points to the real data; 'memFieldType' and 'memType' describe
    --   a pointer.  If 'False', then the layout consists of the real data.
  , memIsIndirect :: {-#UNPACK#-}!Bool
  }

data AlgLayout = AlgMemLayout !AlgMemLayout | AlgValLayout !AlgValLayout

data Layout = MemLayout !MemLayout | ValLayout !ValLayout

isErasedLayout :: Layout -> Bool
isErasedLayout (ValLayout VErased) = True
isErasedLayout _ = False

fromValLayout (ValLayout vl) = vl
fromValLayout _ = internalError "fromValLayout"

-- | Get the value type corresponding to a 'ValLayout'
valLayoutValueType :: ValLayout -> LL.ValueType
valLayoutValueType (VLayout t) = t
valLayoutValueType VErased     = LL.PrimType LL.UnitType

-- | Get the low-level type used to pass this data type as a
--   constructor parameter
algParamType :: Layout -> LL.ValueType
algParamType (ValLayout vl) = valLayoutValueType vl
algParamType (MemLayout _) = LL.PrimType LL.OwnedType

-- | Get the low-level type used to return this data from a case statement
algReturnType :: Layout -> LL.ValueType
algReturnType (ValLayout vl) = valLayoutValueType vl
algReturnType (MemLayout _) = LL.PrimType LL.PointerType

discardStructure :: AlgLayout -> Layout
discardStructure (AlgMemLayout ml) = MemLayout (discardMemStructure ml)
discardStructure (AlgValLayout vl) = ValLayout (discardValStructure vl)

-- | Read the contents of a structure field
readField :: Layout -> LL.DynamicField -> LL.Val -> GenLower LL.Val
readField (MemLayout mem_member) _ ptr =
  if memIsIndirect mem_member
  then primLoadMutable (LL.PrimType LL.PointerType) ptr
  else return ptr
-- memAccessor mem_member (LL.fieldType field) ptr
readField (ValLayout val_member) _ ptr =
  primLoadMutable (valLayoutValueType val_member) ptr

layoutFieldType :: Layout -> GenLower (LL.DynamicFieldType, LL.Val)
layoutFieldType (MemLayout ml) = memFieldType ml
layoutFieldType (ValLayout vl) =
  let field_type =
        case valLayoutValueType vl
        of LL.PrimType pt -> LL.PrimField pt
           LL.RecordType rt -> LL.RecordField (toDynamicRecord rt)
  in return (field_type, boolV $ LL.pointerlessness vl)

buildMemFieldType :: GenLower (LL.DynamicRecord, LL.Val)
                  -> GenLower (LL.DynamicFieldType, LL.Val)
buildMemFieldType m = do
  (recd, is_pointerless) <- m
  return (LL.RecordField recd, is_pointerless)

buildMemRecord :: GenLower (LL.DynamicFieldType, LL.Val)
               -> GenLower (LL.DynamicRecord, LL.Val)
buildMemRecord m = do
  (recd, is_pointerless) <- m
  return (singletonDynamicRecord LL.Mutable recd, is_pointerless)

-------------------------------------------------------------------------------
-- Operations on value layouts

-- | Discard the details of an algebraic value type
discardValStructure :: AlgValLayout -> ValLayout
discardValStructure (AVLayout layout) = valType $ anyMember layout
discardValStructure AVErased = VErased

-- | The layout of an enumerative type
enumValLayout :: [(Var, LL.Lit, [Layout])] -> AlgValLayout
enumValLayout members = AVLayout $ Sum (map make_layout members) return
  where
    tag_type = case members of (_, lit, _) : _ -> LL.litType lit

    make_layout (con, tag, fields) =
      (tag, ValProd (VarCon con) ty fields writer reader)
      where
        (writer, reader) = nullaryValueConCode (LL.LitV tag) fields
        ty = VLayout $ LL.PrimType tag_type

-- | The layout of an (enumerative + product) type.
--   One member has fields, the others do not.
enumProdLayout :: [(Var, LL.Lit, [Layout])]
               -> (Var, LL.Lit, ValProd)
               -> AlgValLayout
enumProdLayout e_members (p_con, p_tag, p_prod) =
  AVLayout $ Sum (p_layout : map make_layout e_members) get_tag
  where
    tag_type = LL.litType p_tag
    payload_type =
      case valType p_prod
      of VLayout vt -> vt
         VErased -> internalError "enumValLayout: Not a product type"
    
    -- The low-level type of this algebraic data type
    record_type = LL.constStaticRecord [LL.PrimField tag_type,
                                        LL.valueToFieldType payload_type]
    ty = VLayout $ LL.RecordType record_type

    -- A dummy value to put in the payload field of enum types
    dummy_payload_value = dummyValue payload_type

    get_tag x = do
      [tag, _] <- unpackRecord record_type x
      return (LL.VarV tag)

    -- Construct the layout for an enum member
    make_layout (con, tag, fields) =
      (tag, ValProd (VarCon con) ty fields writer reader)
      where
        value = LL.RecV record_type [LL.LitV tag, dummy_payload_value]
        (writer, reader) = nullaryValueConCode value fields
    
    -- The layout for the product member
    p_layout =
      (p_tag, ValProd (VarCon p_con) ty (valFields p_prod) writer reader)
      where
        writer inits = do
          -- Construct the product value
          val <- valWriter p_prod inits
          -- Add a tag
          return $ LL.RecV record_type [LL.LitV p_tag, val]
        
        reader x = do
          -- Get the payload
          [_, prod_value] <- unpackRecord record_type x
          valReader p_prod (LL.VarV prod_value)

dummyValue :: LL.ValueType -> LL.Val
dummyValue (LL.PrimType pt) =
  LL.LitV $ case pt
            of LL.UnitType       -> LL.UnitL
               LL.BoolType       -> LL.BoolL False
               LL.IntType sgn sz -> LL.IntL sgn sz 0
               LL.FloatType sz   -> LL.FloatL sz 0
               LL.PointerType    -> LL.NullL
               LL.OwnedType      -> LL.NullRefL

dummyValue (LL.RecordType rt) = dummyRecordValue rt

dummyRecordValue :: LL.StaticRecord -> LL.Val
dummyRecordValue record_type = LL.RecV record_type field_types
  where
    field_types = map (field_type . LL.fieldType) $ LL.recordFields record_type
    field_type (LL.PrimField pt) = dummyValue (LL.PrimType pt)
    field_type (LL.RecordField rt) = dummyValue (LL.RecordType rt)

-- | The layout of a product value type
productValLayout :: LayoutCon -> [ValLayout] -> ValProd
productValLayout con fields =
  ValProd con ltype (map ValLayout fields) writer reader
  where
    num_fields = length fields
    record_type =
      -- Create a record containing only non-erased fields
      LL.constStaticRecord [LL.valueToFieldType f | VLayout f <- fields]
    writer args
      | length args == num_fields = do
          -- Ignore the erased arguments
          let kept_args = [a | (a, VLayout _) <- zip args fields]
          vals <- mapM fromProducer kept_args
          return $ LL.RecV record_type vals
      | otherwise = internalError "productValLayout: Wrong number of fields"

    reader val = do
      real_values <- unpackRecord record_type val
      return $ make_erased_values fields real_values
      where
        -- For every non-erased value, take a value from the record
        -- For every erased value, produce a unit value
        make_erased_values (VLayout _ : fs) (v:vs) =
          LL.VarV v : make_erased_values fs vs

        make_erased_values (VErased : fs) vs =
          LL.LitV LL.UnitL : make_erased_values fs vs

        make_erased_values [] [] = []

    ltype = VLayout $ LL.RecordType record_type
    
-- | The layout of a type that's not a sum type.
nonSumValLayout :: ValProd -> AlgValLayout
nonSumValLayout = AVLayout . One

-- | The layout of a type isomorphic to the unit type.
--
--   The data type may have fields; the fields must all be erased.
unitValLayout :: LayoutCon -> [Layout] -> AlgValLayout
unitValLayout con fields =
  nonSumValLayout $ ValProd con unit_type fields writer reader
  where
    (writer, reader) = nullaryValueConCode (LL.LitV LL.UnitL) fields
    unit_type = VLayout (LL.PrimType LL.UnitType)

-- | Generate the code to construct or deconstruct a nullary value.
--
--   The nullary value may have erased fields.  The constructor takes 
--   field values as arguments and ignores them.  The destructor 
--   returns field values.
nullaryValueConCode :: LL.Val -> [Layout]
                    -> (([Initializer] -> Producer),
                        (LL.Val -> GenLower [LL.Val]))
nullaryValueConCode value fields
  | all isErasedLayout fields = num_fields `seq` (writer, reader)
  | otherwise = internalError "unitValueLayout: Data type has fields"
  where
    num_fields = length fields

    writer fs 
      | length fs == num_fields = return value
      | otherwise = internalError "unitValLayout: Wrong number of fields"

    reader _ = return (replicate num_fields (LL.LitV LL.UnitL))

boolLayout :: AlgValLayout
boolLayout = enumValLayout
             [ (pyonBuiltin the_False, LL.BoolL False, [])
             , (pyonBuiltin the_True, LL.BoolL True, [])]

-- | Create the layout of a boxed reference, given the layout of the referent.
--
--   The parameter layout should have an object header; this is not verified.
boxedLayout :: AlgMemLayout -> AlgValLayout
boxedLayout (Sum members get_tag) =
  AVLayout $ Sum [(tag, boxedLayout' l) | (tag, l) <- members] get_tag'
  where
    get_tag' owned_ptr = do
      -- Cast to a non-owned pointer before getting the tag
      ptr <- emitAtom1 (LL.PrimType LL.PointerType) $
             LL.PrimA LL.PrimCastFromOwned [owned_ptr]
      get_tag ptr

boxedLayout (One m) = AVLayout $ One (boxedLayout' m)

-- | Helper function for 'boxedLayout'.  Construct the layout of a boxed
--   sum type.
boxedLayout' :: MemProd -> ValProd
boxedLayout' (MemProd con layout fields writer reader) =
  ValProd { valConstructor = con
        , valType = VLayout (LL.PrimType LL.OwnedType)
        , valFields = fields
        , valWriter = new_writer
        , valReader = new_reader}
  where
    new_writer fld_inits = do
      (record_type, _) <- memType layout

      -- Allocate storage and initialize the contents.  Boxed objects
      -- always contain pointers in their header.
      ptr <- allocateHeapMemComposite (LL.recordSize record_type)
      writer record_type fld_inits ptr

      -- Return an owned pointer
      emitAtom1 (LL.PrimType LL.OwnedType) $ LL.PrimA LL.PrimCastToOwned [ptr]

    new_reader owned_ptr = do
      (record_type, _) <- memType layout

      -- Cast to a non-owned pointer before reading
      ptr <- emitAtom1 (LL.PrimType LL.PointerType) $
             LL.PrimA LL.PrimCastFromOwned [owned_ptr]
      reader record_type ptr

boxedObjectLayout :: AlgMemLayout -> AlgValLayout
boxedObjectLayout l = boxedLayout (objectLayout l)

-------------------------------------------------------------------------------
-- Operations on memory layouts

-- | Discard the details of an algebraic data type.  The resulting layout
--   consists of a block of memory with size and alignment sufficient to
--   satisfy all possible size and alignment constraints of the fields.
discardMemStructure :: AlgMemLayout -> MemLayout
discardMemStructure (Sum members _) =
  unionLayout $ map (memLayout . snd) members

discardMemStructure (One member) = memLayout member

-- | Create a field layout with the maximum size and alignment of all the 
--   given layouts.  The layout will have a 'BytesField' type.
unionLayout :: [MemLayout] -> MemLayout
unionLayout layouts =
  memBytesLayout $ do
    -- Compute the maximum size and alignment over all fields 
    (field_records, pointerlessnesses) <- mapAndUnzipM memType layouts
    max_size <- computeMaximum $ map LL.recordSize field_records
    max_align <- computeMaximum $ map LL.recordAlignment field_records
    is_pointerless <- foldM primAnd (boolV True) pointerlessnesses
    return (max_size, max_align, is_pointerless)

-- | Layout of an object that occupies a single field  
memValueLayout :: ValLayout -> MemLayout
memValueLayout value_type =
  MLayout
  (return (field_type, is_pointerless))
  (buildMemRecord $ return (field_type, is_pointerless))
  False
  where
    is_pointerless = boolV $ LL.pointerlessness value_type
    field_type = 
      case valLayoutValueType value_type
      of LL.PrimType pt -> LL.PrimField pt
         LL.RecordType rt -> LL.RecordField (toDynamicRecord rt)

-- | Layout of an object that consists of undifferentiated bytes
memBytesLayout :: GenLower (LL.Val, LL.Val, LL.Val)
                  -- ^ Computes size, alignment, and pointerlessness
               -> MemLayout     -- ^ Memory layout
memBytesLayout mk_size =
  MLayout mk_field_type (buildMemRecord mk_field_type) False
  where
    mk_field_type = do
      (size, alignment, is_pointerless) <- mk_size
      return (LL.BytesField size alignment, is_pointerless)

-- | Layout of an object that consists of a record
memRecordLayout :: GenLower (LL.DynamicRecord, LL.Val) -> MemLayout
memRecordLayout mk_record =
  MLayout
  { memFieldType = buildMemFieldType mk_record 
  , memType = mk_record 
  , memIsIndirect = False
  }

-- | The layout of an indirect reference.  The reference occupies one pointer
--   worth of memory.  It points to a dynamically allocated data structure
--   containing all its fields.  The data structure is big enough to hold 
--   any possible value of the referent type.
referenceLayout :: MemLayout -> MemProd
referenceLayout layout =
  MemProd (VarCon $ pyonBuiltin the_referenced) reference_layout [MemLayout layout]
  writer reader
  where
    writer _ [init] dst = do
      -- Allocate memory
      (referent_record, is_pointerless) <- memType layout
      let referent_size = LL.recordSize referent_record
      referent <- allocateHeapMem referent_size is_pointerless
      
      -- Initialize the allocated memory
      asWriter init referent
      
      -- Save the pointer
      primStoreMutable (LL.PrimType LL.PointerType) dst referent
    
    reader _ src = do
      -- Read the pointer to the referent
      referent <- primLoadMutable (LL.PrimType LL.PointerType) src

      -- Get the referent
      return [referent]

    reference_layout =
      -- Create the layout of a reference.  It's a pointer.
      MLayout (return (field_type, boolV False))
      (return (singletonDynamicRecord LL.Mutable field_type, boolV False))
      True
      where
        field_type = LL.PrimField LL.PointerType

-- | The layout of a polymorphic reference.  Its size and alignment are
--   computed at run time.
polymorphicLayout :: Type -> MemLayout
polymorphicLayout ty =
  memBytesLayout $ lookupReprDict ty $ \dict -> do
    size <- selectPassConvSize dict
    align <- selectPassConvAlignment dict
    is_pointerless <- selectPassConvIsPointerless dict
    return (size, align, is_pointerless)

arrayLayout :: LL.Val -> MemLayout -> MemLayout 
arrayLayout count element =
  memBytesLayout $ do
    (element_record, is_pointerless) <- memType element

    -- Array size = count * (pad (alignment element) (size element)
    let elt_size = LL.recordSize element_record
    let elt_align = LL.recordAlignment element_record
    int_size <- primCastZ (LL.PrimType LL.nativeIntType) elt_size
    padded_elt_size <- addRecordPadding int_size elt_align
    array_size <- nativeMulZ count padded_elt_size
    array_uint_size <- primCastZ (LL.PrimType LL.nativeWordType) array_size
    
    return (array_uint_size, elt_align, is_pointerless)

-- | The layout of a product type.
productMemLayout :: LayoutCon -> [Layout] -> MemProd
productMemLayout con fields =
  MemProd con layout fields writer reader
  where
    layout = memRecordLayout $ do
      (field_types, pointerlesss) <- mapAndUnzipM layoutFieldType fields
      pointerless <- foldM primAnd (boolV True) pointerlesss
      recd <- createMutableDynamicRecord field_types
      return (recd, pointerless)

    writer record_type initializers dst 
      | length initializers /= length fields = 
          internalError "productMemLayout: Wrong number of field initializers"
      | otherwise = do
          let record_fields = LL.recordFields record_type
          forM_ (zip record_fields initializers) $ \(fld, initializer) -> do
            field_ptr <- referenceField fld dst
            let layout = fieldTypeToRecord $ LL.fieldType fld
            asWriter initializer field_ptr

    reader record_type src = do
      let record_fields = LL.recordFields record_type
      forM (zip record_fields fields) $ \(fld, member) -> do
        field_ptr <- referenceField fld src
        readField member fld field_ptr

-- | The layout of a type that's not a sum type.
nonSumMemLayout :: MemProd -> AlgMemLayout
nonSumMemLayout = One

-- | The layout of a tagged sum type.
taggedSumMemLayout :: [(LL.Lit, MemProd)] -> AlgMemLayout
taggedSumMemLayout members = Sum tagged_members get_tag
  where
    -- We know the tag starts at offset 0 in memory
    get_tag ptr = primLoadMutable (LL.PrimType tag_type) ptr
      
    -- Get the layout of all member types, so we can determine their
    -- worst-case alignment
    payload_layout = unionLayout $ map (memLayout . snd) members
    
    payload_alignment :: GenLower LL.Val
    payload_alignment = do
      (recd, _) <- memType payload_layout
      return (LL.recordAlignment recd)
    
    tag_type = LL.litType $ fst $ head members
    
    -- Create a record type containing tag and payload.  The record type is
    -- given the same alignment in all cases
    tagged_type layout = do
      alignment <- payload_alignment
      (field_type, is_pointerless) <- memFieldType layout
      recd <- createMutableDynamicRecord
              [LL.AlignField alignment, LL.PrimField tag_type, field_type]
      return (recd, is_pointerless)

    tagged_members :: [(LL.Lit, MemProd)]
    tagged_members = [(tag, tagged_member tag l) | (tag, l) <- members]
      where
        tagged_member tag (MemProd cons layout fs writer reader) =
          MemProd cons (tagged_layout tag layout) fs tagged_writer tagged_reader
          where
            tagged_writer record_type initializers dst = do
              let [tag_field, payload_field] = LL.recordFields record_type
                  LL.RecordField payload_record = LL.fieldType payload_field

              -- Write the tag
              storeField tag_field dst (LL.LitV tag)

              -- Write the payload
              payload_ptr <- referenceField payload_field dst
              writer payload_record initializers payload_ptr
            
            tagged_reader record_type ptr = do
              let payload_field = record_type !!: 1
                  LL.RecordField payload_record = LL.fieldType payload_field

              -- Read the payload
              payload_ptr <- referenceField payload_field ptr
              reader payload_record payload_ptr              

        tagged_layout tag layout = memRecordLayout (tagged_type layout)

-- | The layout of a data type with an object header.  This is usually used
--   in combination with 'boxedLayout'.
objectLayout :: AlgMemLayout -> AlgMemLayout
objectLayout mem_layout =
  case mem_layout
  of Sum members get_tag ->
       let get_tag' ptr = do
             (payload, _) <- memFieldType $ discardMemStructure mem_layout
             object_record <- mk_object_record payload
             payload_ptr <- referenceField (object_record !!: 1) ptr
             get_tag payload_ptr
           members' = [(tag, member_layout l) | (tag, l) <- members]
       in Sum members' get_tag'
     One member -> One $ member_layout member
  where
    member_layout (MemProd cons layout fields writer reader) =
      MemProd cons (object_layout layout) fields obj_writer obj_reader
      where
        obj_writer recd initializers dst = do
          -- TODO: Write object header
          -- Write payload
          let payload_field = recd !!: 1
              LL.RecordField payload_record = LL.fieldType payload_field
          payload_ptr <- referenceField payload_field dst
          writer payload_record initializers payload_ptr
        
        obj_reader recd src = do
          let payload_field = recd !!: 1
              LL.RecordField payload_record = LL.fieldType payload_field
          payload_ptr <- referenceField payload_field src
          reader payload_record payload_ptr

    object_layout layout = memRecordLayout $ do
      (field_type, _) <- memFieldType layout

      -- The header has pointers that must be tracked,
      -- so pointerlessness is False
      recd <- mk_object_record field_type
      return (recd, boolV False)

    mk_object_record payload =
      createMutableDynamicRecord [LL.RecordField objectHeaderRecord', payload]
    
-------------------------------------------------------------------------------
-- Using layouts

-- | Get the type of a variable corresponding to the given high-level type
lowerType :: TypeEnv -> Type -> Lower (Maybe LL.ValueType)
lowerType tenv ty = 
  case toBaseKind $ typeKind tenv ty
  of ValK        -> do whnf_ty <- reduceToWhnf ty
                       vl <- getValLayout whnf_ty
                       return $ Just $ valLayoutValueType vl
     BoxK        -> return $ Just $ LL.PrimType LL.OwnedType
     BareK       -> return $ Just $ LL.PrimType LL.PointerType
     OutK        -> return $ Just $ LL.PrimType LL.PointerType
     SideEffectK -> return Nothing
     _           -> internalError "lowerReturnType: Invalid representation"

lowerTypeList :: TypeEnv -> [Type] -> Lower [LL.ValueType]
lowerTypeList tenv tys = liftM catMaybes $ mapM (lowerType tenv) tys

-- | Compute the low-level function type corresponding to a Mem function.
--   Uses the Mem type environment.
lowerFunctionType :: LowerEnv -> Type -> IO LL.FunctionType
lowerFunctionType env ty = runLowering env $ do
  -- Deconstruct the type
  let (ty_params, monotype) = fromForallType ty
      (params, ret) = fromFunType monotype
      local_tenv = foldr insert_type (typeEnvironment env) ty_params
        where insert_type (a ::: k) e = insertType a k e
  when (null params) $ internalError "lowerFunctionType: Not a function type"

  -- Create a function type
  param_types <- lowerTypeList local_tenv params
  ret_type <- fmap maybeToList $ lowerType local_tenv ret
  let ll_type = LL.closureFunctionType param_types ret_type
  return ll_type

-- | Generate the low-level translation of a data constructor.
--   If the data constructor takes parameters or
--   a return pointer, then a lambda function is generated.  Otherwise
--   code is generated to compute the constructor's value.
algebraicIntro :: AlgLayout -> Var -> GenLower LL.Val
algebraicIntro (AlgMemLayout ml) con = lift $ algMemIntro ml (VarCon con)
algebraicIntro (AlgValLayout (AVLayout vl)) con = algValIntro vl (VarCon con)

algMemIntro ml con =
  case findMember ((con ==) . memConstructor) ml
  of Just mb -> algMemIntro' mb
     Nothing -> internalError "algebraicIntro: Constructor not found"

algMemIntro' (MemProd { memLayout = layout
                    , memFields = fs
                    , memWriter = writer}) = do
  -- Create an initializer function. 
  -- The function takes the parameters (which may be initializer functions)
  -- and return pointer, and writes into the return pointer.
  let param_types = map algParamType fs
  params <- mapM LL.newAnonymousVar param_types
  ret_param <- LL.newAnonymousVar (LL.PrimType LL.PointerType)

  fun_body <- execBuild [] $ do
    -- Create record type
    (record_type, _) <- memType layout

    -- Write fields
    writer record_type (algInitializers params fs) (LL.VarV ret_param)
    return $ LL.ReturnE (LL.ValA [])
  let fun = LL.closureFun (params ++ [ret_param]) [] fun_body
  return $ LL.LamV fun

algValIntro vl con =
  case findMember ((con ==) . valConstructor) vl
  of Just mb -> algValIntro' mb
     Nothing -> internalError "algebraicIntro: Constructor not found"

algValIntro' (ValProd { valType = VLayout ty
                      , valFields = []
                      , valWriter = writer}) = do
  -- Since this constructor takes no parameters,
  -- we generate the code for it directly.
  writer []

algValIntro' (ValProd { valType = VLayout ty
                      , valFields = fs
                      , valWriter = writer}) = lift $ do
  -- Create an initializer function.
  -- The function takes the parameters (which may be initializer functions)
  -- and return pointer, and writes into the return pointer.
  let param_types = map algParamType fs
  params <- mapM LL.newAnonymousVar param_types
  
  fun_body <- execBuild [ty] $ do
    ret_val <- writer $ algInitializers params fs
    return $ LL.ReturnE (LL.ValA [ret_val])
  let fun = LL.closureFun params [ty] fun_body
  return $ LL.LamV fun

-- | Interpret the parameter variables as initializers.
--
--   If the parameter has a value layout, the parameter holds a value.
--   If the parameter has a memory layout, the parameter holds an initializer
--   function.  The function takes a single parameter, which is a pointer to 
--   the data to initialize.
algInitializers :: [LL.Var] -> [Layout] -> [Initializer]
algInitializers params fs = zipWith mk_init params fs  
  where
    mk_init param (MemLayout _) =
      WriteInit $ \p -> emitAtom0 $ LL.closureCallA (LL.VarV param) [p]
    mk_init param (ValLayout _) =
      ValInit (return $ LL.VarV param)

type Branch = (LayoutCon, [LL.Val] -> GenLower LL.Stm)
type Branches = [Branch]

-- | Generate the low-level translation of a case statement.
algebraicElim :: AlgLayout      -- ^ Scrutinee layout
              -> LL.Val         -- ^ Scrutinee
              -> Branches       -- ^ Case alternatives
              -> GenLower LL.Stm
algebraicElim (AlgValLayout (AVLayout layout)) scr branches =
  eliminateSum valConstructor algValElim layout scr branches
algebraicElim (AlgValLayout AVErased) _ _ =
  internalError "Lowering: Cannot generate case statement for an erased value"
algebraicElim (AlgMemLayout layout) scr branches =
  eliminateSum memConstructor algMemElim layout scr branches

eliminateSum get_ctors elim (Sum members get_tag) scr branches = do
  ret_types <- getReturnTypes
  alts <- lift $ forM branches $ \ (con, branch) -> do
    let (tag, layout) = find_member con
    branch_body <- execBuild ret_types $ elim layout scr branch
    return (tag, branch_body)
  tag <- get_tag scr
  return $ LL.SwitchE tag alts
  where
    find_member con =
      case find has_con members
      of Just mb -> mb
         Nothing -> internalError "algebraicElim: Constructor not found"
      where
        has_con (_, layout) = con == get_ctors layout

eliminateSum get_ctors elim (One member) scr [(con, branch)]
  | con == get_ctors member = elim member scr branch
  | otherwise = internalError "algebraicElim: Constructor not found"

eliminateSum _ _ _ _ _ =
  internalError "algebraicElim: Wrong number of case alternatives"

algValElim layout scr branch = valReader layout scr >>= branch

algMemElim layout scr branch = do
  (record_type, _) <- memType $ memLayout layout
  memReader layout record_type scr >>= branch

-------------------------------------------------------------------------------
-- Computing the layout of a data type

-- | Compute the low-level representation of an algebraic data type.
--   It's an error to call this on a non-algebraic data type.
getAlgLayout :: TypeEnv -> Type -> Lower AlgLayout
getAlgLayout tenv ty = do
  whnf_ty <- reduceToWhnf ty
  case toBaseKind $ typeKind tenv whnf_ty of
    ValK  -> fmap AlgValLayout $ getValAlgLayout whnf_ty
    BoxK  -> fmap AlgValLayout $ getValAlgLayout whnf_ty
    BareK -> ref_layout whnf_ty
    OutK  -> ref_layout whnf_ty
    _     -> internalError "getAlgLayout: Unexpected representation"
  where
    ref_layout whnf_ty = fmap AlgMemLayout $ getRefAlgLayout whnf_ty

-- | The type arguments and data constructors of a fully
--   instantiated data type.  All data constructors take
--   the same type arguments.
type InstantiatedDataType = (DataType, [Type], [DataConType])

-- | Look up the constructors of a data type.
lookupDataTypeForLayout :: TypeEnv -> Type -> Maybe InstantiatedDataType
lookupDataTypeForLayout tenv ty 
  | Just (tycon, ty_args) <- fromVarApp ty,
    Just data_type <- lookupDataType tycon tenv =
      case sequence [lookupDataCon c tenv
                    | c <- dataTypeDataConstructors data_type]
      of Just cons -> Just (data_type, ty_args, cons)
         Nothing -> internalError "lookupDataTypeForLayout"
  | otherwise = Nothing

lookupDataTypeForLayout' :: TypeEnv -> Type -> InstantiatedDataType
lookupDataTypeForLayout' tenv ty =
  case lookupDataTypeForLayout tenv ty
  of Just x -> x
     Nothing -> internalError $
                "getLayout: Unknown data type: " ++ show (pprType ty)

-- | Get the algebraic data type layout of a boxed or value type.
--   The type must be in WHNF.
getValAlgLayout :: Type -> Lower AlgValLayout
getValAlgLayout ty =
  case getLevel ty
  of TypeLevel ->
       case fromTypeApp ty
       of (VarT op, args)
            | op `isPyonBuiltin` the_bool  -> return boolLayout
            | op `isPyonBuiltin` the_int   -> not_algebraic
            | op `isPyonBuiltin` the_float -> not_algebraic
            | op `isPyonBuiltin` the_Pf    -> return AVErased
            | otherwise -> do
                tenv <- getTypeEnv
                case lookupDataTypeForLayout tenv ty of
                  Just inst_type -> getValDataTypeLayout inst_type
                  Nothing -> not_algebraic
          (UTupleT kinds, args) -> do
            arg_layouts <- mapM getLayout args
            return $ nonSumValLayout $
              productValLayout TupleCon (map fromValLayout arg_layouts)
          _ -> case ty 
               of FunT {} -> not_algebraic
                  _ -> internalError "getAlgLayout: Head is not a type application"
     _ -> not_algebraic
  where
    not_algebraic =
      internalError $
      "getAlgLayout: Not an algebraic type:\n" ++ show (nest 4 $ pprType ty)

-- | Compute the layout of a value data type based on the types of its
--   data constructors.
getValDataTypeLayout :: InstantiatedDataType -> Lower AlgValLayout
getValDataTypeLayout (tycon, ty_args, datacons)  
  | null datacons =
      -- Uninhabited type
      internalError "getAlgLayout: Type is uninhabited"
  | ValK <- dataTypeKind tycon =
      getValueDataTypeLayout ty_args datacons
  | BoxK <- dataTypeKind tycon =
      getBoxedDataTypeLayout ty_args datacons
  | otherwise =
      internalError "getValDataTypeLayout"

getValueDataTypeLayout ty_args datacons = do
  ctor_fields <- mapM (instantiateDataCon ty_args) datacons
  case partition (nullaryValueCon . fst) (zip ctor_fields datacons) of
    ([(fields, c)], []) ->
      -- Unit type
      return $ unitValLayout (VarCon $ dataConCon c) fields

    ([], [(fields, c)]) ->
      -- Product type
      -- Fields must not be reference objects
      let fields' = map from_val fields
            where
              from_val (ValLayout vl) = vl
              from_val (MemLayout _) =
                internalError "getAlgLayout: Invalid field type"

      in return $ nonSumValLayout $
         productValLayout (VarCon $ dataConCon c) fields'

    (nullary_cons, [(fields, c)]) ->
      -- Enum + product type
      let fields' = map from_val fields
            where
              from_val (ValLayout vl) = vl
              from_val (MemLayout _) =
                internalError "getAlgLayout: Invalid field type"

          fields_layout = productValLayout (VarCon $ dataConCon c) fields'
          
          -- Tags
          (_, tags) = dataTags datacons
          tag_table = [(dataConCon c1, t) | (c1, t) <- zip datacons tags]
          
          -- Product member
          p_con = dataConCon c
          Just p_tag = lookup p_con tag_table

          -- Enum members
          disjuncts = [let con = dataConCon n_c
                           Just tag = lookup con tag_table
                       in (con, tag, n_fields)
                      | (n_fields, n_c) <- nullary_cons]

      in return $ enumProdLayout disjuncts (p_con, p_tag, fields_layout)

    (nullary_cons, []) ->
      -- Enumerative type
      let (_, tags) = dataTags datacons
          disjuncts = [(dataConCon c, tag, fields)
                      | ((fields, c), tag) <- zip nullary_cons tags]
      in return $ enumValLayout disjuncts
    
    _ ->
      internalError "getAlgLayout: Cannot construct values of this type"

getBoxedDataTypeLayout ty_args datacons = do
  members <- forM datacons $ \datacon -> do
    fields <- instantiateDataCon ty_args datacon
    return $ productMemLayout (VarCon $ dataConCon datacon) fields
  
  let (_, tags) = dataTags datacons
      mem_layout =
        case members
        of [member] -> nonSumMemLayout member -- Product type
           _        -> taggedSumMemLayout $ zip tags members -- SOP type
  return $ boxedObjectLayout mem_layout

-- | Get the algebraic layout of a bare type.
--   The type must be in WHNF.
getRefAlgLayout :: Type -> Lower AlgMemLayout
getRefAlgLayout ty =
  case fromVarApp ty
  of Just (op, [arg])
       | op `isPyonBuiltin` the_Referenced -> do
           arg_layout <- getRefLayout =<< reduceToWhnf arg
           return $ nonSumMemLayout $ referenceLayout arg_layout
     _ -> do
       tenv <- getTypeEnv
       case lookupDataTypeForLayout tenv ty of
         Nothing ->
           case ty
           of AnyT {} -> internalError "getAlgLayout: Not implemented for Any"
              _ -> internalError "getAlgLayout: Invalid type"
         Just inst_type@(data_type, _, _) ->
           case dataTypeKind data_type
           of BareK -> getRefDataTypeLayout inst_type
              _ -> internalError "getAlgLayout: Invalid representation"

-- | Get the algebraic layout of a bare data type, based on an algebraic
--   data type definition.
getRefDataTypeLayout :: InstantiatedDataType -> Lower AlgMemLayout
getRefDataTypeLayout (_, ty_args, datacons)
  | null datacons =
      -- Uninhabited type
      internalError "refDataTypeLayout: Type is uninhabited"

  | [datacon] <- datacons = do
      -- Singleton object.  It's a product with no tag.
      fields <- instantiateDataCon ty_args datacon
      return $ nonSumMemLayout $ productMemLayout (VarCon $ dataConCon datacon) fields

  | otherwise = do
      -- Sum of products type
      members <- forM datacons $ \datacon -> do
        fields <- instantiateDataCon ty_args datacon
        return $ productMemLayout (VarCon $ dataConCon datacon) fields
      
      let (_, tags) = dataTags datacons
      return $ taggedSumMemLayout $ zip tags members

-- | Compute the low-level representation of a data type
getLayout :: Type -> Lower Layout
getLayout ty = do
  whnf_ty <- reduceToWhnf ty
  kind <- askTypeEnv (\tenv -> toBaseKind $ typeKind tenv whnf_ty)
  case kind of
    ValK  -> fmap ValLayout $ getValLayout whnf_ty
    BoxK  -> fmap ValLayout $ getValLayout whnf_ty
    BareK -> ref_layout whnf_ty
    OutK  -> ref_layout whnf_ty
    _     -> internalError "getLayout: Unexpected representation"
  where
    ref_layout whnf_ty = fmap MemLayout $ getRefLayout whnf_ty

-- | Get the layout of a value or boxed type.  The type should be in WHNF.
getValLayout :: Type -> Lower ValLayout
getValLayout ty
  | TypeLevel <- getLevel ty =
      case fromTypeApp ty
      of (VarT op, args)
           | op `isPyonBuiltin` the_bool  -> prim_layout LL.BoolType
           | op `isPyonBuiltin` the_int   -> prim_layout LL.pyonIntType
           | op `isPyonBuiltin` the_float -> prim_layout LL.pyonFloatType
           | op `isPyonBuiltin` the_Pf    -> return VErased
           | otherwise -> do
               tenv <- getTypeEnv
               case lookupDataTypeForLayout tenv ty of
                 Just inst_type@(tycon, _, _) ->
                   case dataTypeKind tycon
                   of BoxK -> prim_layout LL.OwnedType
                      ValK -> do
                        -- Use the algebraic data type layout
                        alg_layout <- getValDataTypeLayout inst_type
                        return $ discardValStructure alg_layout
                      _ -> internalError "getValLayout"
                 Nothing -> internalError "getValLayout: Unexpected type"
         (UTupleT kinds, args) -> do
           -- Create a record containing a field for each argument.
           -- Since arguments always have value or boxed kind, they always 
           -- have a value layout.
           arg_layouts <- mapM getLayout args
           return $ VLayout $ LL.RecordType $ LL.constStaticRecord $
             map (LL.valueToFieldType . valLayoutValueType . fromValLayout)
             arg_layouts
         (FunT {}, []) ->
           prim_layout LL.OwnedType
         _ -> internalError "getLayout: Head is not a type application"
  | otherwise = internalError "getValLayout"
  where
    prim_layout t = return $ VLayout $ LL.PrimType t

-- | Get the layout of a bare type.  The type should be in WHNF.
getRefLayout :: Type -> Lower MemLayout
getRefLayout ty =
  case fromVarApp ty
  of Just (op, [arg])
       | op `isPyonBuiltin` the_Referenced ->
           return $ memValueLayout $ VLayout (LL.PrimType LL.PointerType)
     Just (op, [arg1, arg2])
       | op `isPyonBuiltin` the_array -> do
           field_layout <- getRefLayout =<< reduceToWhnf arg2
           size <- lookupIndexedInt arg1
           return $ arrayLayout size field_layout
     _ -> do
       tenv <- getTypeEnv
       case lookupDataTypeForLayout tenv ty of
         Nothing ->
           case ty
           of AnyT {} -> internalError "getLayout: Not implemented for Any"
              _ -> -- Type variable or type variable application
                return $ polymorphicLayout ty
              _ -> internalError "getRefLayout: Unexpected type"
         Just inst_type@(data_type, _, _) ->
           case dataTypeKind data_type
           of BareK -> do
                alg_layout <- getRefDataTypeLayout inst_type
                return $ discardMemStructure alg_layout
              _ -> internalError "getAlgLayout: Invalid representation"

-- | Instantiate a data constructor.  Get the layouts of its members.
instantiateDataCon :: [Type] -> DataConType -> Lower [Layout]
instantiateDataCon ty_args data_con = do
  -- Create existential variables and get the field types
  (ex_vars, field_reprs, _) <-
    instantiateDataConTypeWithFreshVariables data_con ty_args

  -- Add existential variables to the environment
  assumeBinders ex_vars $
    -- Get layouts of fields
    mapM getLayout field_reprs

-- | Given the layouts of a value data constructor's fields, decide
--   whether the data constructor is a nullary data constructor.
--
--   We can only do this for value data constructors.  Value data constructors 
--   must be instantiated with non-variable type arguments, so we're guaranteed
--   to compute consistent results.
--
--   Other types may result in inconsistent results depending on how type
--   variables are instantiated.
nullaryValueCon :: [Layout] -> Bool
nullaryValueCon = all is_erased
  where
    is_erased (ValLayout VErased) = True
    is_erased _ = False

nullaryBoxedCon :: DataConType -> Bool
nullaryBoxedCon c = null $ dataConPatternArgs c

-- | Given a list of data constructors, create a list of tags. 
--   The tag data type is chosen based on how many data constructors there are.
--
--   We don't tag types with a single constructor.
--   This function isn't used for \'bool\', since we use a special tag type.
dataTags :: [DataConType] -> (LL.PrimType, [LL.Lit])
dataTags data_cons =
  let tag_size = if length data_cons <= 256 then LL.S8 else LL.S16
  in (LL.IntType LL.Unsigned tag_size,
      map (LL.IntL LL.Unsigned tag_size) [0..])
