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
        layoutCon,
        Layout(ValLayout, MemLayout),
        getLayout,
        AlgLayout,
        getAlgLayout,
        pprAlgLayout,

        -- * Code generation
        layoutSize,
        staticObject,
        algebraicIntro,
        algebraicElim)
where

import Prelude hiding(foldr, elem, any, all, or, sum)

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
import Common.Label
import Common.Supply
import Builtins.Builtins
import LowLevel.Build
import qualified LowLevel.Syntax as LL
import qualified LowLevel.CodeTypes as LL
import LowLevel.CodeTypes((!!:), Mutability)
import qualified LowLevel.Print as LL
import LowLevel.Records
import SystemF.Syntax
import SystemF.Lowering.LowerMonad
import Type.Environment
import Type.Eval
import Type.Type
import qualified Type.Substitute as Substitute 

-- | Generate code to compute the maximum of a nonempty list of values.
-- The values are unsigned native ints (this is not checked).
computeMaximum :: [LL.Val] -> GenLower LL.Val
computeMaximum [] = internalError "computeMaximum: empty list"
computeMaximum (v:vs) = foldM nativeMaxUZ v vs

fieldTypeToRecord :: LL.DynamicFieldType -> LL.DynamicRecord
fieldTypeToRecord (LL.RecordField r) = r
fieldTypeToRecord ftype = singletonDynamicRecord LL.Mutable ftype

-- | A Code generator of a computation that produces a value
type Producer = GenLower LL.Val

-- | A code generator of a computation that writes a value into memory
type Writer = LL.Val -> GenLower ()

-- | A code generator of an initializer.
--
--   An initializer either puts a value into a field or
--   writes an object into memory, depending on the data kind that the
--   initializer was created from.
data Initializer = ValInit Producer | WriteInit Writer

fromProducer (ValInit m) = m
fromProducer _ = internalError "Expected a value, got a writer"

fromWriter (WriteInit m) = m
fromWriter _ = internalError "Expected a writer, got a value"

-- | Convert an initializer to a writer.
--
--   If a value producer was provided, its value is written to memory.
asWriter :: Initializer -> Writer
asWriter (WriteInit m) = m
asWriter (ValInit m) = \dst -> do
  val <- m
  primStoreMutable (LL.valType val) dst val

-------------------------------------------------------------------------------
{-

* Layout objects

Data types are described in two levels of detail.  A 'Layout' describes how
to store a value as a field of another value, including how to read and write
that field.  An 'AlgLayout' describes, in addition to what 'Layout' describes,
how to introduce values (the low-level translation of constructor application)
and how to eliminate values (the low-level translation of a case statement).

Types are lowered to /value/ or /memory/ data, depending  
on their kind.  A lowered value variable /contains/ its data, while a lowered
memory variable /points to/ its data.  A lowered field of an object
contains its data in both cases.  Because of this distinction, field access
works differently depending on the types involved.
In addition, some data types have pointer indirection or extra fields.  Those
details are inserted by the code in this file.

Data of kind \'val\' become values.  The exact data type used to represent a
\'val\' value is selected by inspecting its data type.  The compiler ensures
that a \'val\' value will always have a constant type (not a type variable).
Data of kind \'box\' also become values--more precisely, owned pointer values.
Data of kinds \'bare\' and \'out\' become memory data.

Algebraic layouts describe sum-of-product data types.  The sum component
of the type is described by an 'AlgSum'.  The 'AlgSum' describes how to
identify which component of a SOP data type a given instance belongs to.
The product component is described by a 'ValProd' or 'MemProd'.  It includes
a constructor, layout, field layouts, and methods for constructing or reading
that product type.
-}

-- | A data constructor used for selecting a member of a sum type.
--   Tuple types have only one constructor, so no further
--   information is required.  Other algebraic data types are annotated with
--   a constructor name.
data LayoutCon = VarTag !Var | TupleTag
               deriving(Eq, Show)

layoutCon :: ConInstSummary -> LayoutCon
layoutCon (Just v) = VarTag v
layoutCon Nothing = TupleTag

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
--   An erased value behaves like a unit value when it's in a variable.
--   Erased values are not stored in an object.
data AlgValLayout = AVLayout !(AlgSum ValProd) | AVErased

-- | An algebraic product type.  A product type consists of a constructor
--   and fields.  The field values are stored in the object according to
--   the writer and reader methods.
data ValProd =
    ValProd
    { valConstructor :: !LayoutCon
      
      -- | The low-level type of this layout
    , valType        :: ValLayout

      -- | Fields of the product type
    , valFields      :: ![Layout]

      -- | Create a static value
    , valBuilder      :: !(Maybe Label -> [LL.Val] -> Lower (LL.Val, [LL.GlobalDef]))

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

fromValLayout (ValLayout vl) = vl
fromValLayout _ = internalError "fromValLayout"

-- | Get the value type corresponding to a 'ValLayout'
valLayoutValueType :: ValLayout -> LL.ValueType
valLayoutValueType (VLayout t) = t
valLayoutValueType VErased     = LL.PrimType LL.UnitType

-- | Get the data type corresponding to a 'ValLayout' that's stored as a field
--   of another object.
--   Erased values have no data type.
valLayoutFieldType :: ValLayout -> Maybe LL.StaticFieldType
valLayoutFieldType (VLayout t) = Just $ LL.valueToFieldType t
valLayoutFieldType VErased     = Nothing

-- | The layout of an algebraic data type that is passed by reference.
type AlgMemLayout = AlgSum MemProd

-- | An algebraic product type.
--
--   A product type is or contains a record containing its fields.
data MemProd =
    MemProd
    { memConstructor :: !LayoutCon
      
      -- | The layout details of this product type
    , memLayout       :: MemLayout

      -- | Fields of the product type
    , memFields       :: ![Layout]

      -- | Create a static value
    , memBuilder      :: !(Maybe Label -> [LL.Val] -> Lower (LL.Val, [LL.GlobalDef]))

      -- | Initialize the product type, given the initializers for all its
      --   fields
    , memWriter       :: !([Initializer] -> Writer)

      -- | Read the fields of the product type, when using a @case@ statement
      --   to inspect data with this layout
    , memReader       :: !(LL.Val -> GenLower [LL.Val])
    }

-- | The layout of a memory object.
data MemLayout =
    -- | An object with statically known layout
    StaticMemLayout !LL.ValueType
    -- | A pointer to a pass-by-reference object
  | IndirectMemLayout
    -- | A pass-by-reference object with dynamically determined layout
    --   * size (unsigned word) 
    --   * alignment (unsigned word)
    --   * pointerless (bool)
  | DynamicMemLayout (GenLower (LL.Val, LL.Val, LL.Val))
    -- | An erased object; only occurs as a field of another object.
    --   The erased object is read and written as a unit value.
  | ErasedMemLayout

data AlgLayout = AlgMemLayout !AlgMemLayout | AlgValLayout !AlgValLayout

data Layout = MemLayout !MemLayout | ValLayout !ValLayout

isErasedLayout :: Layout -> Bool
isErasedLayout (ValLayout VErased) = True
isErasedLayout _ = False

-- | Compute the size and alignment of the given layout.
--   Returns native word values.
layoutSize :: Layout -> GenLower (LL.Val, LL.Val)
layoutSize (MemLayout ml) = do
  (size, alignment, _) <- memDynamicObjectType ml
  return (size, alignment)

layoutSize (ValLayout vl) =
  return (nativeWordV $ LL.sizeOf vl, nativeWordV $ LL.alignOf vl)

discardStructure :: AlgLayout -> Layout
discardStructure (AlgMemLayout ml) = MemLayout (discardMemStructure ml)
discardStructure (AlgValLayout vl) = ValLayout (discardValStructure vl)

-- | Read the contents of a structure field
readField :: Mutability -> Layout -> LL.Val -> GenLower LL.Val
readField _ (MemLayout mem_member) ptr = return ptr

readField m (ValLayout val_member) ptr =
  primLoad m (valLayoutValueType val_member) ptr

memStaticObjectType :: MemLayout -> LL.ValueType
memStaticObjectType (StaticMemLayout vt) = vt

memStaticObjectType IndirectMemLayout = LL.PrimType LL.PointerType

memStaticObjectType (DynamicMemLayout _) =
  internalError "memStaticObjectType: Not a valid static type"

memStaticObjectType ErasedMemLayout =
  internalError "memStaticObjectType: Not a valid static type"

-- | Get the storage properties of an object having the given layout
memDynamicObjectType :: MemLayout -> GenLower (LL.Val, LL.Val, LL.Val)
memDynamicObjectType (StaticMemLayout vt) =
  return (nativeWordV $ LL.sizeOf vt,
          nativeWordV $ LL.alignOf vt,
          boolV $ LL.pointerlessness vt)

memDynamicObjectType IndirectMemLayout =
  return (nativeWordV $ LL.sizeOf LL.PointerType,
          nativeWordV $ LL.alignOf LL.PointerType,
          boolV False)

memDynamicObjectType (DynamicMemLayout l) = l

memDynamicObjectType ErasedMemLayout =
  internalError "memDynamicObjectType: Not an object"

memStaticFieldType :: MemLayout -> Maybe (LL.StaticFieldType, Bool)
memStaticFieldType (StaticMemLayout vt) =
  Just (LL.valueToFieldType vt, LL.pointerlessness vt)
memStaticFieldType IndirectMemLayout =
  Just (LL.PrimField LL.PointerType, False)
memStaticFieldType ErasedMemLayout = Nothing
memStaticFieldType _ = internalError "memStaticFieldType: Invalid type"

memDynamicFieldType :: MemLayout
                    -> Maybe (GenLower (LL.DynamicFieldType, LL.Val))
memDynamicFieldType (StaticMemLayout vt) = Just $ do
  return (toDynamicFieldType $ LL.valueToFieldType vt,
          boolV $ LL.pointerlessness vt)

memDynamicFieldType IndirectMemLayout = Just $ do
  return (LL.PrimField LL.PointerType, boolV False)

memDynamicFieldType (DynamicMemLayout l) = Just $ do
  (size, alignment, pointerless) <- l
  return (LL.BytesField size alignment, pointerless)

memDynamicFieldType ErasedMemLayout = Nothing

dynamicFieldType :: Layout -> Maybe (GenLower (LL.DynamicFieldType, LL.Val))
dynamicFieldType (MemLayout ml) = memDynamicFieldType ml
dynamicFieldType (ValLayout VErased) = Nothing
dynamicFieldType (ValLayout (VLayout t)) =
  Just $ return (toDynamicFieldType $ LL.valueToFieldType t,
                 boolV $ LL.pointerlessness t)

staticFieldType :: Layout -> Maybe (LL.StaticFieldType, Bool)
staticFieldType (MemLayout ml) = memStaticFieldType ml
staticFieldType (ValLayout VErased) = Nothing
staticFieldType (ValLayout (VLayout t)) =
  Just (LL.valueToFieldType t, LL.pointerlessness t)

-- | Compute the layout of a record type consisting of the specified fields 
dynamicRecordLayout :: Mutability
                    -> [Layout]
                    -> GenLower (LL.DynamicRecord, LL.Val)
dynamicRecordLayout mutable layouts
  | any is_dynamic layouts = do
      -- Cannot create a static record layout.  Compute dynamic layout
      -- for each field.
      field_info <- sequence $ mapMaybe dynamicFieldType layouts
      let (fields, pointerlesss) = unzip field_info
      recd <- case mutable
              of LL.Mutable -> createMutableDynamicRecord fields
                 LL.Constant -> createConstDynamicRecord fields
      pointerless <- foldM primAnd (boolV True) pointerlesss
      return (recd, pointerless)
  | otherwise =
      -- Create a static record layout
      let (field_types, pointerlesss) =
            unzip $ mapMaybe staticFieldType layouts
          record_type = case mutable
                        of LL.Mutable -> LL.mutableStaticRecord field_types
                           LL.Constant -> LL.constStaticRecord field_types
      in return (toDynamicRecord record_type, boolV $ or pointerlesss)
  where
    is_dynamic (MemLayout (DynamicMemLayout _)) = True
    is_dynamic _ = False

-------------------------------------------------------------------------------
-- Printing

pprAlgSum ppr_member (Sum xs _) = braces $ vcat (map member xs)
  where
    member (l, x) = LL.pprLit l <+> text "=>" <+> ppr_member x

pprAlgSum ppr_member (One x) = ppr_member x

pprLayoutCon (VarTag v) = pprVar v
pprLayoutCon TupleTag   = text "tuple"

pprValProd p = parens $ sep (intro : ty : fields)
  where
    intro = pprLayoutCon (valConstructor p) <> colon
    ty = pprValLayout (valType p)
    fields = map pprLayout $ valFields p

pprMemProd p = parens $ sep (intro : ty : fields)
  where
    intro = pprLayoutCon (memConstructor p) <> colon
    ty = pprMemLayout (memLayout p)
    fields = map pprLayout $ memFields p

pprLayout (MemLayout ml) = parens $ text "M" <+> pprMemLayout ml
pprLayout (ValLayout vl) = parens $ text "V" <+> pprValLayout vl

pprValLayout (VLayout t) = LL.pprValueType t
pprValLayout VErased = text "()"

pprMemLayout (StaticMemLayout t)  = LL.pprValueType t
pprMemLayout IndirectMemLayout    = text "indirect"
pprMemLayout (DynamicMemLayout _) = text "dynamic"
pprMemLayout ErasedMemLayout      = text "()"

pprAlgLayout (AlgMemLayout ml) = pprAlgMemLayout ml
pprAlgLayout (AlgValLayout vl) = pprAlgValLayout vl

pprAlgMemLayout = pprAlgSum pprMemProd
pprAlgValLayout (AVLayout x) = pprAlgSum pprValProd x
pprAlgValLayout AVErased = text "()"

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
      (tag, ValProd (VarTag con) ty fields builder writer reader)
      where
        (builder, writer, reader) = nullaryValueConCode (LL.LitV tag) fields
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
      (tag, ValProd (VarTag con) ty fields builder writer reader)
      where
        value = LL.RecV record_type [LL.LitV tag, dummy_payload_value]
        (builder, writer, reader) = nullaryValueConCode value fields
    
    -- The layout for the product member
    p_layout =
      (p_tag, ValProd (VarTag p_con) ty (valFields p_prod) builder writer reader)
      where
        builder m_name inits = do
          (val, defs) <- valBuilder p_prod m_name inits
          return (LL.RecV record_type [LL.LitV p_tag, val], defs)

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
  ValProd con ltype (map ValLayout fields) builder writer reader
  where
    num_fields = length fields
    record_type =
      -- Create a record containing only non-erased fields
      LL.constStaticRecord [LL.valueToFieldType f | VLayout f <- fields]

    builder m_name args
      | length args == num_fields = do
          -- Ignore the erased arguments
          let kept_args = [a | (a, VLayout _) <- zip args fields]
          return (LL.RecV record_type kept_args, [])
      | otherwise = internalError "productValLayout: Wrong number of fields"

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
  nonSumValLayout $ ValProd con unit_type fields builder writer reader
  where
    (builder, writer, reader) = nullaryValueConCode (LL.LitV LL.UnitL) fields
    unit_type = VLayout (LL.PrimType LL.UnitType)

-- | Generate the code to construct or deconstruct a nullary value.
--
--   The nullary value may have erased fields.  The constructor takes 
--   field values as arguments and ignores them.  The destructor 
--   returns field values.
nullaryValueConCode :: LL.Val -> [Layout]
                    -> ((Maybe Label -> [LL.Val] -> Lower (LL.Val, [LL.GlobalDef])),
                        ([Initializer] -> Producer),
                        (LL.Val -> GenLower [LL.Val]))
nullaryValueConCode value fields
  | all isErasedLayout fields = num_fields `seq` (builder, writer, reader)
  | otherwise = internalError "unitValueLayout: Data type has fields"
  where
    num_fields = length fields

    builder _ fs
      | length fs == num_fields = return (value, [])
      | otherwise = internalError "unitValLayout: Wrong number of fields"

    writer fs 
      | length fs == num_fields = return value
      | otherwise = internalError "unitValLayout: Wrong number of fields"

    reader _ = return (replicate num_fields (LL.LitV LL.UnitL))

boolLayout :: AlgValLayout
boolLayout = enumValLayout
             [ (coreBuiltin The_False, LL.BoolL False, [])
             , (coreBuiltin The_True, LL.BoolL True, [])]

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
boxedLayout' (MemProd con layout fields builder writer reader) =
  ValProd { valConstructor = con
          , valType = VLayout (LL.PrimType LL.OwnedType)
          , valFields = fields
          , valBuilder = new_builder
          , valWriter = new_writer
          , valReader = new_reader}
  where
    new_builder m_name fields = do
      -- Construct the object
      (val, defs) <- builder Nothing fields

      -- Bind it to a global definition
      tmp_var <- LL.newVar m_name (LL.PrimType LL.OwnedType)
      let object_def = LL.GlobalDataDef (LL.Def tmp_var (LL.StaticData val))
      return (LL.VarV tmp_var, object_def : defs)

    new_writer initializers = do
      (obj_size, _, _) <- memDynamicObjectType layout

      -- Allocate storage and initialize the contents.  Boxed objects
      -- always contain pointers in their header.
      ptr <- allocateHeapMemComposite obj_size
      writer initializers ptr

      -- Return an owned pointer
      emitAtom1 (LL.PrimType LL.OwnedType) $ LL.PrimA LL.PrimCastToOwned [ptr]

    new_reader owned_ptr = do
      -- Cast to a non-owned pointer before reading
      ptr <- emitAtom1 (LL.PrimType LL.PointerType) $
             LL.PrimA LL.PrimCastFromOwned [owned_ptr]
      reader ptr

-- | Given the layout of a boxed object's data payload
--   (basically a bare object), construct the boxed layout.
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
    (unzip3 -> (sizes, alignments, pointerlessnesses)) <-
      mapM memDynamicObjectType layouts
    max_size <- computeMaximum sizes
    max_align <- computeMaximum alignments
    is_pointerless <- foldM primAnd (boolV True) pointerlessnesses
    return (max_size, max_align, is_pointerless)

-- | Layout of an object that consists of undifferentiated bytes
memBytesLayout :: GenLower (LL.Val, LL.Val, LL.Val)
                  -- ^ Computes size, alignment, and pointerlessness
               -> MemLayout     -- ^ Memory layout
memBytesLayout mk_size = DynamicMemLayout mk_size

-- | Layout of an object that consists of a record
memRecordLayout :: GenLower (LL.DynamicRecord, LL.Val) -> MemLayout
memRecordLayout mk_record = DynamicMemLayout $ do
  (recd, is_pointerless) <- mk_record
  return (LL.recordSize recd, LL.recordAlignment recd, is_pointerless)

{-
-- | The layout of an indirect reference.  The reference occupies one pointer
--   worth of memory.  It points to a dynamically allocated data structure
--   containing all its fields.  The data structure is big enough to hold 
--   any possible value of the referent type.
referenceLayout :: MemLayout -> MemProd
referenceLayout layout =
  MemProd (VarTag $ coreBuiltin The_referenced) IndirectMemLayout
  [MemLayout layout] builder writer reader
  where
    builder m_name [obj_value] = do
      -- Create a global data definition with this value 
      tmp_var <- LL.newVar m_name (LL.PrimType LL.PointerType)
      let obj_def = LL.GlobalDataDef $ LL.Def tmp_var (LL.StaticData obj_value)
      return (LL.VarV tmp_var, [obj_def])
          
    writer [init] dst = do
      -- Allocate memory
      (size, align, is_pointerless) <- memDynamicObjectType layout
      referent <- allocateHeapMem size is_pointerless

      -- Initialize the allocated memory
      asWriter init referent

      -- Save the pointer
      primStoreMutable (LL.PrimType LL.PointerType) dst referent
    
    reader src = do
      -- Read the pointer to the referent
      referent <- primLoadMutable (LL.PrimType LL.PointerType) src

      -- Get the referent
      return [referent] -}

-- | The layout of a polymorphic reference.  Its size and alignment are
--   computed at run time.
polymorphicLayout :: Type -> MemLayout
polymorphicLayout ty =
  memBytesLayout $ lookupReprDict ty $ \dict -> do
    sa <- selectPassConvSizeAlign dict
    [size, align] <- unpackRecord sizeAlignRecord sa
    is_pointerless <- selectPassConvIsPointerless dict
    return (LL.VarV size, LL.VarV align, is_pointerless)

-- | Get an array layout, given the array size and element layout.
--   The array size generates code to get the number of elements, in the
--   form of a finite indexed int (a record containing an int).
arrayLayout :: GenLower LL.Val -> MemLayout -> MemLayout 
arrayLayout get_count element =
  memBytesLayout $ do
    count <- get_count
    [size_var] <- unpackRecord finIndexedIntRecord count

    (elt_size, elt_align, elt_pointerless) <- memDynamicObjectType element

    -- Array size = count * (pad (alignment element) (size element)
    int_size <- primCastZ (LL.PrimType LL.nativeIntType) elt_size
    padded_elt_size <- addRecordPadding int_size elt_align
    array_size <- nativeMulZ (LL.VarV size_var) padded_elt_size
    array_uint_size <- primCastZ (LL.PrimType LL.nativeWordType) array_size
    
    return (array_uint_size, elt_align, elt_pointerless)

-- | The layout of a product type.
productMemLayout :: LayoutCon -> [Layout] -> MemProd
productMemLayout con fields =
  MemProd con layout fields builder writer reader
  where
    -- This is somewhat of a hack.  For some data types, we generate
    -- 'const' memory operations to help out the low-level optimizer.
    -- The low-level optimizer assumes 'const' stores are never overwritten.
    is_const_con = case con 
                   of VarTag c -> c `isCoreBuiltin` The_repr
                      TupleTag -> False
    mutable = if is_const_con then LL.Constant else LL.Mutable

    layout = memRecordLayout $ dynamicRecordLayout mutable fields

    builder _ args
      | length args /= length fields = 
          internalError "productMemLayout: Wrong number of field initializers"
      | otherwise = do
          let arg_types = map (LL.valueToFieldType . LL.valType) args
              record_type =
                if is_const_con
                then LL.constStaticRecord arg_types
                else LL.mutableStaticRecord arg_types
          return (LL.RecV record_type args, [])

    writer initializers dst 
      | length initializers /= length fields = 
          internalError "productMemLayout: Wrong number of field initializers"
      | otherwise = do
          (recd, _) <- dynamicRecordLayout mutable fields
          let record_fields = LL.recordFields recd
          forM_ (zip record_fields initializers) $ \(fld, initializer) -> do
            field_ptr <- referenceField fld dst
            let layout = fieldTypeToRecord $ LL.fieldType fld
            asWriter initializer field_ptr

    reader src = do
      (record_type, _) <- dynamicRecordLayout mutable fields
      let record_fields = LL.recordFields record_type
      forM (zip record_fields fields) $ \(fld, member) -> do
        readField (LL.fieldMutable fld) member =<< referenceField fld src

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
      (_, alignment, _) <- memDynamicObjectType payload_layout
      return alignment

    -- If static records of this data type can be built, this is the
    -- size and alignment of the payload
    static_payload_alignment :: (Int, Int)
    static_payload_alignment =
      foldl' (\(a, b) (c, d) -> (max a c, max b d)) (0, 1)
      [(LL.sizeOf field, LL.alignOf field)
      | (_, p) <- members,
        let Just (field, _) = memStaticFieldType $ memLayout p]

    -- Data type used for the tag
    tag_type = LL.litType $ fst $ head members

    -- Create a record type containing tag and payload.  The record type is
    -- given the same alignment in all cases
    tagged_type layout = do
      alignment <- payload_alignment
      (field_type, is_pointerless) <-
        case memDynamicFieldType layout of Just m -> m
      recd <- createMutableDynamicRecord
              [LL.AlignField alignment, LL.PrimField tag_type, field_type]
      return (recd, is_pointerless)

    static_tagged_type layout =
      let Just (field_type, is_pointerless) = memStaticFieldType layout
          (_, alignment) = static_payload_alignment
          recd = LL.mutableStaticRecord
                 [LL.AlignField alignment, LL.PrimField tag_type, field_type]
      in (recd, is_pointerless)

    tagged_members :: [(LL.Lit, MemProd)]
    tagged_members = [(tag, tagged_member tag l) | (tag, l) <- members]
      where
        tagged_member tag (MemProd cons layout fs builder writer reader) =
          MemProd cons (tagged_layout tag layout) fs
          tagged_builder tagged_writer tagged_reader
          where
            tagged_builder m_name values = do
              let (record_type, _) = static_tagged_type layout
              (payload, defs) <- builder m_name values
              let val = LL.RecV record_type [LL.LitV tag, payload]
              return (val, defs)

            tagged_writer initializers dst = do
              (record_type, _) <- tagged_type layout
              let [tag_field, payload_field] = LL.recordFields record_type

              -- Write the tag
              storeField tag_field dst (LL.LitV tag)

              -- Write the payload
              writer initializers =<< referenceField payload_field dst
            
            tagged_reader ptr = do
              (record_type, _) <- tagged_type layout
              let payload_field = record_type !!: 1

              -- Read the payload
              reader =<< referenceField payload_field ptr

        tagged_layout tag layout = memRecordLayout (tagged_type layout)

-- | The layout of a data type with an object header.  This is usually used
--   in combination with 'boxedLayout'.
objectLayout :: AlgMemLayout -> AlgMemLayout
objectLayout mem_layout =
  case mem_layout
  of Sum members get_tag ->
       let get_tag' ptr = do
             -- Compute offset of payload
             object_record <- mk_object_record (discardMemStructure mem_layout)

             -- Get the tag from the payload
             get_tag =<< referenceField (object_record !!: 1) ptr
           members' = [(tag, member_layout l) | (tag, l) <- members]
       in Sum members' get_tag'
     One member -> One $ member_layout member
  where
    member_layout (MemProd cons layout fields builder writer reader) =
      MemProd cons (object_layout layout) fields obj_builder obj_writer obj_reader
      where
        obj_builder m_name values = do
          let Just (field_type, is_pointerless) = memStaticFieldType layout
          (payload, defs) <- builder m_name values
          let record_type =
                LL.mutableStaticRecord [LL.RecordField objectHeaderRecord,
                                     LL.valueToFieldType $ LL.valType payload]

              -- TODO: Initialize object header
              recd = LL.RecV record_type [dummyRecordValue objectHeaderRecord,
                                          payload]
          return (recd, defs)

        obj_writer initializers dst = do
          -- TODO: Write object header
          -- Write payload
          recd <- mk_object_record (discardMemStructure mem_layout)
          let payload_field = recd !!: 1
          writer initializers =<< referenceField payload_field dst
        
        obj_reader src = do
          recd <- mk_object_record (discardMemStructure mem_layout)
          let payload_field = recd !!: 1
          reader =<< referenceField payload_field src

    object_layout layout = memRecordLayout $ do
      recd <- mk_object_record layout
      -- The header has pointers that must be tracked,
      -- so pointerlessness is False
      return (recd, boolV False)

    mk_object_record layout = do
      (payload, _) <- case memDynamicFieldType layout of Just m -> m
      -- The header is never modified.  The payload may or may not change.
      createConstDynamicRecord [LL.RecordField objectHeaderRecord', payload]
    
-------------------------------------------------------------------------------
-- Using layouts

-- | Get the type of a variable corresponding to the given high-level type
lowerType :: Type -> Lower (Maybe LL.ValueType)
lowerType ty = do
  k <- typeBaseKind ty
  case k of
    ValK        -> do whnf_ty <- reduceToWhnf ty
                      vl <- getValLayout whnf_ty
                      return $ Just $ valLayoutValueType vl
    BoxK        -> return $ Just $ LL.PrimType LL.OwnedType
    BareK       -> return $ Just $ LL.PrimType LL.PointerType
    OutK        -> return $ Just $ LL.PrimType LL.PointerType
    _           -> internalError "lowerReturnType: Invalid representation"

lowerTypeList :: [Type] -> Lower [LL.ValueType]
lowerTypeList tys = liftM catMaybes $ mapM lowerType tys

-- | Compute the low-level function type corresponding to a Mem function.
--   Uses the Mem type environment.
lowerFunctionType :: LowerEnv -> Type -> IO LL.FunctionType
lowerFunctionType env ty = runLowering env $ do
  (ty_params, params, ret) <- liftTypeEvalM $ deconForallFunType ty
  when (null params) $ internalError "lowerFunctionType: Not a function type"

  -- Add type parameters to type environment.  Type parameters must not
  -- affect memory layout.
  assumeBinders ty_params $ do
    -- Create a function type
    param_types <- lowerTypeList params
    ret_type <- fmap maybeToList $ lowerType ret
    let ll_type = LL.closureFunctionType param_types ret_type
    return ll_type

-- | Generate a static data definition from a data constructor application.
--   Return the lowered value, auxiliary global definitions, and a flag
--   indicating whether it's a pass-by-value value.
staticObject :: Maybe Label -> AlgLayout -> LayoutCon -> [LL.Val]
             -> Lower (LL.Val, [LL.GlobalDef], Bool)
staticObject m_name (AlgMemLayout ml) con fields =
  staticMemObject m_name ml con fields
staticObject m_name (AlgValLayout (AVLayout vl)) con fields =
  staticValObject m_name vl con fields

staticMemObject m_name ml con fields =
  case findMember ((con ==) . memConstructor) ml
  of Just mb -> do (val, defs) <- memBuilder mb m_name fields
                   return (val, defs, False)
     Nothing -> internalError "staticObject: Constructor not found"

staticValObject m_name vl con fields =
  case findMember ((con ==) . valConstructor) vl
  of Just mb -> do (val, defs) <- valBuilder mb m_name fields
                   return (val, defs, True)
     Nothing -> internalError "staticObject: Constructor not found"

-- | Generate the low-level translation of a data constructor.  If the
--   data constructor takes a return pointer, then a lambda function
--   is generated.  Otherwise code is generated to compute the
--   constructor's value.
--
--   The arguments should be initializer functions (for bare objects) or
--   values (for boxed or value objects).
algebraicIntro :: AlgLayout -> LayoutCon -> [LL.Val] -> GenLower LL.Val
algebraicIntro (AlgMemLayout ml) con fields =
  algMemIntro ml con fields
algebraicIntro (AlgValLayout (AVLayout vl)) con fields =
  algValIntro vl con fields

algMemIntro ml con fields =
  case findMember ((con ==) . memConstructor) ml
  of Just mb -> algMemIntro' mb fields
     Nothing -> let x = case ml
                        of One x -> show (memConstructor x)
                           Sum xs _ -> show $ map (memConstructor . snd) xs
                in trace (show con ++ "\n" ++ x) $ internalError "algebraicIntro: Constructor not found"

algMemIntro' (MemProd { memLayout = layout
                      , memFields = fs
                      , memWriter = writer}) fields = do
  -- Create an initializer function. 
  -- The function takes a return pointer, and writes its results into the
  -- referenced memory.
  ret_param <- lift $ LL.newAnonymousVar (LL.PrimType LL.PointerType)

  genLambda [LL.PrimType LL.PointerType] [LL.PrimType LL.UnitType] $ \[ret_param] -> do
    -- Write fields
    writer (algInitializers fields fs) ret_param
    return [LL.LitV LL.UnitL]

algValIntro vl con =
  case findMember ((con ==) . valConstructor) vl
  of Just mb -> algValIntro' mb
     Nothing -> internalError "algebraicIntro: Constructor not found"

algValIntro' (ValProd { valType = VLayout ty
                      , valFields = fs
                      , valWriter = writer}) fields = do
  writer $ algInitializers fields fs

-- | Interpret the parameter variables as initializers.
--
--   If the parameter has a value layout, the parameter holds a value.
--   If the parameter has a memory layout, the parameter holds an initializer
--   function.  The function takes a single parameter, which is a pointer to 
--   the data to initialize.
algInitializers :: [LL.Val] -> [Layout] -> [Initializer]
algInitializers params fs
  | length params /= length fs =
      internalError "algInitializers"
  | otherwise =
      zipWith mk_init params fs  
  where
    mk_init param (MemLayout _) =
      WriteInit $ \p -> do
        emitAtom1 (LL.PrimType LL.UnitType) $ LL.closureCallA param [p]
        return ()
    mk_init param (ValLayout _) =
      ValInit (return param)

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

eliminateSum :: (a -> LayoutCon)
             -> (a -> LL.Val -> ([LL.Val] -> GenLower LL.Stm) -> GenLower LL.Stm)
             -> AlgSum a
             -> LL.Val
             -> Branches
             -> GenLower LL.Stm
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

algValElim :: ValProd -> LL.Val -> ([LL.Val] -> GenLower LL.Stm)
           -> GenLower LL.Stm
algValElim layout scr branch = valReader layout scr >>= branch

algMemElim :: MemProd -> LL.Val -> ([LL.Val] -> GenLower LL.Stm)
           -> GenLower LL.Stm
algMemElim layout scr branch = memReader layout scr >>= branch

-------------------------------------------------------------------------------
-- Computing the layout of a data type

-- | Compute the low-level representation of an algebraic data type.
--   It's an error to call this on a non-algebraic data type.
getAlgLayout :: Type -> Lower AlgLayout
getAlgLayout ty = do
  whnf_ty <- reduceToWhnf ty
  kind <- typeBaseKind whnf_ty
  case kind of
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
lookupDataTypeForLayout :: Type -> UnboxedTypeEvalM (Maybe InstantiatedDataType)
lookupDataTypeForLayout ty =
  case fromVarApp ty
  of Just (tycon, ty_args) -> do
       m_data_type <- lookupDataType tycon
       case m_data_type of
         Just data_type -> do cons <- lookup_data_constructors data_type
                              return $ Just (data_type, ty_args, cons)
         Nothing        -> return Nothing
     Nothing -> return Nothing
  where
    -- Get all the data constructors
    lookup_data_constructors data_type = do
      data_constructors <-
        sequence [lookupDataCon c
                 | c <- dataTypeDataConstructors data_type]
      case sequence data_constructors of
        Just cons -> return cons
        Nothing -> internalError "lookupDataTypeForLayout"

lookupDataTypeForLayout' :: Type -> UnboxedTypeEvalM InstantiatedDataType
lookupDataTypeForLayout' ty = do
  m_type <- lookupDataTypeForLayout ty
  case m_type of
    Just x -> return x
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
            | op `isCoreBuiltin` The_bool -> return boolLayout
            | op == intV                  -> not_algebraic
            | op == uintV                 -> not_algebraic
            | op == floatV                -> not_algebraic
            | otherwise -> do
                m_inst_type <- liftTypeEvalM $ lookupDataTypeForLayout ty
                case m_inst_type of
                  Just inst_type -> getValDataTypeLayout inst_type
                  Nothing -> not_algebraic
          (UTupleT kinds, args) -> do
            arg_layouts <- mapM getLayout args
            return $ nonSumValLayout $
              productValLayout TupleTag (map fromValLayout arg_layouts)
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
      internalError $
      "getAlgLayout: Type is uninhabited: " ++ show (dataTypeCon tycon)
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
      return $ unitValLayout (VarTag $ dataConCon c) fields

    ([], [(fields, c)]) ->
      -- Product type
      -- Fields must not be reference objects
      let fields' = map from_val fields
            where
              from_val (ValLayout vl) = vl
              from_val (MemLayout _) =
                internalError "getAlgLayout: Invalid field type"

      in return $ nonSumValLayout $
         productValLayout (VarTag $ dataConCon c) fields'

    (nullary_cons, [(fields, c)]) ->
      -- Enum + product type
      let fields' = map from_val fields
            where
              from_val (ValLayout vl) = vl
              from_val (MemLayout _) =
                internalError "getAlgLayout: Invalid field type"

          fields_layout = productValLayout (VarTag $ dataConCon c) fields'
          
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
    return $ productMemLayout (VarTag $ dataConCon datacon) fields
  
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
  of {-Just (op, [arg])
        | op `isCoreBuiltin` The_Referenced -> do
           arg_layout <- getRefLayout =<< reduceToWhnf arg
           return $ nonSumMemLayout $ referenceLayout arg_layout-}
     _ -> do
       m_inst_type <- liftTypeEvalM $ lookupDataTypeForLayout ty
       case m_inst_type of
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
getRefDataTypeLayout (data_type, ty_args, datacons)
  | null datacons =
      -- Uninhabited type
      internalError $ "refDataTypeLayout: Data type is uninhabited: " ++
      show (dataTypeCon data_type)

  | [datacon] <- datacons = do
      -- Singleton object.  It's a product with no tag.
      fields <- instantiateDataCon ty_args datacon
      return $ nonSumMemLayout $ productMemLayout (VarTag $ dataConCon datacon) fields

  | otherwise = do
      -- Sum of products type
      members <- forM datacons $ \datacon -> do
        fields <- instantiateDataCon ty_args datacon
        return $ productMemLayout (VarTag $ dataConCon datacon) fields
      
      let (_, tags) = dataTags datacons
      return $ taggedSumMemLayout $ zip tags members

-- | Compute the low-level representation of a data type
getLayout :: Type -> Lower Layout
getLayout ty = do
  whnf_ty <- reduceToWhnf ty
  kind <- typeBaseKind whnf_ty
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
  | getLevel ty /= TypeLevel = internalError "getValLayout"
  | otherwise = do
      ty' <- Substitute.freshen ty
      case fromTypeApp ty' of
         (VarT op, args)
           | op `isCoreBuiltin` The_bool -> prim_layout LL.BoolType
           | op == intV                  -> prim_layout LL.trioletIntType
           | op == uintV                 -> prim_layout LL.trioletUintType
           | op == floatV                -> prim_layout LL.trioletFloatType
           | op == storeV                -> prim_layout LL.UnitType
           | otherwise -> do
               kind <- typeBaseKind ty'
               case kind of
                 BoxK ->
                   -- All boxed types have the same layout
                   prim_layout LL.OwnedType
                 ValK -> do
                   -- Layout of a value type depends on the data constructor, 
                   -- which must be known (i.e. not a variable or function)
                   m_layout <- liftTypeEvalM $ lookupDataTypeForLayout ty'
                   case m_layout of
                     Just inst_type@(tycon, _, _) -> do
                        -- Use the algebraic data type layout
                        alg_layout <- getValDataTypeLayout inst_type
                        return $ discardValStructure alg_layout
                     _ -> internalError "getValLayout"
                 _ ->
                   internalError "getValLayout: Unexpected kind"
         (UTupleT kinds, args) -> do
           -- Create a record containing a field for each argument.
           -- Since arguments always have value or boxed kind, they always 
           -- have a value layout.
           arg_layouts <- mapM getLayout args
           return $ VLayout $ LL.RecordType $ LL.constStaticRecord $
             mapMaybe (valLayoutFieldType . fromValLayout) arg_layouts
         (FunT {}, []) ->
           prim_layout LL.OwnedType
         (AllT (v ::: k) ty'', []) ->
           -- Look through the 'forall' type
           assume v k $ getValLayout ty''
         (CoT {}, [_, _]) ->
           -- Coercions are erased
           -- TODO: Convert coercions to unit values, instead
           error "Coercion"

         _ -> internalError "getLayout: Head is not a type application"
  where
    prim_layout t = return $ VLayout $ LL.PrimType t

-- | Get the layout of a bare type.  The type should be in WHNF.
getRefLayout :: Type -> Lower MemLayout
getRefLayout ty = do
  ty' <- Substitute.freshen ty
  case fromTypeApp ty' of
     {-(VarT op, [arg])
       | op `isCoreBuiltin` The_Referenced -> do
           return IndirectMemLayout-}
     (VarT op, [arg1, arg2])
       | op == arrV -> do
           field_layout <- getRefLayout =<< reduceToWhnf arg2
           return $ arrayLayout (lookupIndexedInt arg1) field_layout
     (AllT (v ::: k) rng, []) ->
       -- Look through the 'forall' type
       assume v k $ getRefLayout rng
     _ -> do
       m_inst_type <- liftTypeEvalM $ lookupDataTypeForLayout ty'
       case m_inst_type of
         Nothing ->
           case ty'
           of AnyT {} -> internalError "getLayout: Not implemented for Any"
              _ -> -- Type variable or type variable application
                return $ polymorphicLayout ty'
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
nullaryBoxedCon c = null $ dataConTyParams c

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
