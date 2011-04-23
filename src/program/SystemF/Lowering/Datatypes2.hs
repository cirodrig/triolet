{-| Lowering of data type operations.

For each System F data type, lowering produces a corresponding low-level value
type (for data represented as values), record field type (for fields of
another data type) or record type (for boxed objects and data represented by
reference).  This module deals with translating data types and with generating
code to construct and eliminate values.  For our purposes, store and load
operations are a special case of constructor and eliminator.

Each high-level variable is translated to a low-level variable.  The
meaning of the low-level variable's value depends on the high-level variable's
representation:

* A /value/ term becomes a low-level value.  The low-level value contains
  the value variable's data.

* A /boxed/ term becomes a low-level owned reference.  The reference
  points to the boxed value.

* A /writable/ term becomes a single-parameter function.  The parameter is
  a pointer to the memory area that the function will initialize.

* A /readable/ term becomes a low-level pointer, pointing to the readable
  object.

The lowering code is organized in two levels of abstraciton.  The lower level 
of abstraction deals with basic data structure manipulation such as
tagging, boxing, aggregating multiple pieces into a larger structure
(used for product types), and branching based on a tag value 
(used for sum types).  The upper level of abstraction translates data
types into compositions of lower-level operations.
-}

module SystemF.Lowering.Datatypes2
       (-- * Translation to low-level data types 
        lowerParamType,
        lowerReturnType,
        lowerReturnTypeList,
        lowerFunctionType,

        -- * Creating layouts
        Layout(ValLayout, MemLayout),
        getLayout,
        AlgLayout,
        getAlgLayout,

        -- * Code generation
        algebraicIntro,
        algebraicElim,
        loadValue,
        storeValue)
where

import Prelude hiding(foldr, elem, any, all, sum)

import Control.Monad hiding(forM_)
import Control.Monad.Trans
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
type AlgValLayout = AlgSum ValProd

-- | An algebraic product type
data ValProd =
    ValProd
    { valConstructors :: [Var]
      
      -- | The low-level type of this layout
    , valType        :: ValLayout

      -- | Fields of the product type
    , valFields      :: ![Layout]

      -- | Create a value, given the fields of the product type
    , valWriter      :: !([Initializer] -> Producer)

      -- | Extract the fields of the product type
    , valReader      :: !(LL.Val -> GenLower [LL.Val])
    }

type ValLayout = LL.ValueType

valIsPointerless :: ValLayout -> Bool
valIsPointerless t = LL.pointerlessness t

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
    { memConstructors :: [Var]
      
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

-- | Get the low-level type used to pass this data type as a
--   constructor parameter
algParamType :: Layout -> LL.ValueType
algParamType (ValLayout val_type) = val_type
algParamType (MemLayout _) = LL.PrimType LL.OwnedType

-- | Get the low-level type used to return this data from a case statement
algReturnType :: Layout -> LL.ValueType
algReturnType (ValLayout val_type) = val_type
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
  primLoadMutable val_member ptr

layoutFieldType :: Layout -> GenLower (LL.DynamicFieldType, LL.Val)
layoutFieldType (MemLayout ml) = memFieldType ml
layoutFieldType (ValLayout vl) =
  let field_type =
        case vl
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
discardValStructure :: AlgValLayout -> LL.ValueType
discardValStructure layout = valType $ anyMember layout

-- | The layout of an enumerative type
enumValLayout :: [(Var, LL.Lit)] -> AlgValLayout
enumValLayout members = Sum (map make_layout members) return
  where
    tag_type = LL.litType $ snd $ head members
    make_layout (con, tag) = (tag, ValProd [con] ty [] writer reader)
      where
        writer [] = return (LL.LitV tag)
        reader _ = return []
        ty = LL.PrimType tag_type

-- | The layout of a product value type
productValLayout :: Var -> [ValLayout] -> AlgValLayout
productValLayout con fields =
  One $ ValProd [con] ltype (map ValLayout fields) writer reader
  where
    num_fields = length fields
    record_type =
      LL.constStaticRecord $ map LL.valueToFieldType fields
    writer args
      | length args == num_fields = do
          vals <- mapM fromProducer args
          return $ LL.RecV record_type vals
      | otherwise = internalError "productValLayout: Wrong number of fields"

    reader val = fmap (map LL.VarV) $ unpackRecord record_type val
    
    ltype = LL.RecordType record_type
    
-- | The layout of a type isomorphic to the unit type
unitValLayout :: Var -> AlgValLayout
unitValLayout con = One $ ValProd [con] unit_type [] writer reader
  where
    writer [] = return (LL.LitV LL.UnitL)
    reader _ = return []
    unit_type = LL.PrimType LL.UnitType

boolLayout :: AlgValLayout
boolLayout = enumValLayout
             [ (pyonBuiltin the_False, LL.BoolL False)
             , (pyonBuiltin the_True, LL.BoolL True)]

-- | Create the layout of a boxed reference, given the layout of the referent.
--
--   The parameter layout should have an object header; this is not verified.
boxedLayout :: AlgMemLayout -> AlgValLayout
boxedLayout (Sum members get_tag) =
  Sum [(tag, boxedLayout' l) | (tag, l) <- members] get_tag'
  where
    get_tag' owned_ptr = do
      -- Cast to a non-owned pointer before getting the tag
      ptr <- emitAtom1 (LL.PrimType LL.PointerType) $
             LL.PrimA LL.PrimCastFromOwned [owned_ptr]
      get_tag ptr

boxedLayout (One m) = One (boxedLayout' m)

-- | Helper function for 'boxedLayout'.  Construct the layout of a boxed
--   sum type.
boxedLayout' :: MemProd -> ValProd
boxedLayout' (MemProd cons layout fields writer reader) =
  ValProd { valConstructors = cons
        , valType = LL.PrimType LL.OwnedType
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
      case value_type
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
  MemProd [pyonBuiltin the_referenced] reference_layout [MemLayout layout]
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
productMemLayout :: Var -> [Layout] -> MemProd
productMemLayout con fields =
  MemProd [con] layout fields writer reader
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
lowerReturnType :: ReturnType -> Lower (Maybe LL.ValueType)
lowerReturnType rt = 
  case rt
  of ValRT ::: ty -> fmap Just $ getValLayout ty
     BoxRT ::: _ -> return $ Just $ LL.PrimType LL.OwnedType
     ReadRT ::: _ -> return $ Just $ LL.PrimType LL.PointerType
     OutRT ::: _ -> return $ Just $ LL.PrimType LL.PointerType
     WriteRT ::: _ -> internalError "lowerReturnType: Invalid representation"
     SideEffectRT ::: _ -> return Nothing

lowerReturnTypeList :: ReturnType -> Lower [LL.ValueType]
lowerReturnTypeList rt = fmap maybeToList $ lowerReturnType rt

lowerParamType :: ParamType -> Lower (Maybe LL.ValueType)
lowerParamType (prepr ::: ptype) =
  lowerReturnType (paramReprToReturnRepr prepr ::: ptype)

lowerFunctionType :: IdentSupply LL.Var -> IdentSupply Var -> TypeEnv -> Type
                  -> IO LL.FunctionType
lowerFunctionType ll_var_supply var_supply tenv ty = do
  -- FIXME: Don't recompute this every time the function is called!
  env <- initializeLowerEnv var_supply ll_var_supply tenv Map.empty
  runLowering env $ do
    let (params, ret) = fromFunType ty
    m_param_types <- mapM lowerParamType params
    let param_types = catMaybes m_param_types
    ret_type <- lowerReturnTypeList ret
    return $ LL.closureFunctionType param_types ret_type

-- | Generate the low-level translation of a data constructor.
--   If the data constructor takes parameters or
--   a return pointer, then a lambda function is generated.
algebraicIntro :: AlgLayout -> Var -> Lower LL.Val
algebraicIntro (AlgMemLayout ml) con = algMemIntro ml con
algebraicIntro (AlgValLayout vl) con = algValIntro vl con

algMemIntro ml con =
  case findMember ((con `elem`) . memConstructors) ml
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
  case findMember ((con `elem`) . valConstructors) vl
  of Just mb -> algValIntro' mb
     Nothing -> internalError "algebraicIntro: Constructor not found"

algValIntro' (ValProd { valType = ty
                    , valFields = fs
                    , valWriter = writer}) = do
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

type Branch = (Var, [LL.Val] -> GenLower LL.Stm)
type Branches = [Branch]

-- | Generate the low-level translation of a case statement.
algebraicElim :: AlgLayout -> LL.Val -> Branches -> GenLower LL.Stm
algebraicElim (AlgValLayout layout) scr branches =
  eliminateSum valConstructors algValElim layout scr branches
algebraicElim (AlgMemLayout layout) scr branches =
  eliminateSum memConstructors algMemElim layout scr branches

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
        has_con (_, layout) = con `elem` get_ctors layout

eliminateSum get_ctors elim (One member) scr [(con, branch)]
  | con `elem` get_ctors member = elim member scr branch
  | otherwise = internalError "algebraicElim: Constructor not found"

eliminateSum _ _ _ _ _ =
  internalError "algebraicElim: Wrong number of case alternatives"

algValElim layout scr branch = valReader layout scr >>= branch

algMemElim layout scr branch = do
  (record_type, _) <- memType $ memLayout layout
  memReader layout record_type scr >>= branch

loadValue :: Layout -> LL.Val -> GenLower LL.Val
loadValue (ValLayout ty) ptr = primLoadMutable ty ptr 
loadValue (MemLayout _) _ = internalError "loadValue: Not a value"

storeValue :: Layout -> LL.Val -> LL.Val -> GenLower ()
storeValue (ValLayout ty) val ptr = primStoreMutable ty ptr val 
storeValue (MemLayout _) _ _ = internalError "storeValue: Not a value"

-------------------------------------------------------------------------------
-- Computing the layout of a data type

-- | Compute the low-level representation of an algebraic data type.
--   It's an error to call this on a non-algebraic data type.
getAlgLayout :: ReturnType -> Lower AlgLayout
getAlgLayout (repr ::: ty) =
  case repr
  of ValRT -> fmap AlgValLayout $ getValAlgLayout ty
     BoxRT -> fmap AlgValLayout $ getValAlgLayout ty
     ReadRT -> ref_layout
     OutRT -> ref_layout
     _ -> internalError "getAlgLayout: Unexpected representation"
  where
    ref_layout = fmap AlgMemLayout $ getRefAlgLayout ty

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

getValAlgLayout :: Type -> Lower AlgValLayout
getValAlgLayout ty =
  case getLevel ty
  of TypeLevel ->
       case fromVarApp ty
       of Just (op, args)
            | op `isPyonBuiltin` the_bool  -> return boolLayout
            | op `isPyonBuiltin` the_int   -> not_algebraic
            | op `isPyonBuiltin` the_float -> not_algebraic
            | otherwise -> do
                tenv <- getTypeEnv
                case lookupDataTypeForLayout tenv ty of
                  Just inst_type -> getValDataTypeLayout inst_type
                  Nothing -> not_algebraic
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
      internalError "valDataTypeLayout: Type is uninhabited"

  | is_unboxed, all_nullary_constructors, [datacon] <- datacons =
      -- Unit type
      return $ unitValLayout (dataConCon datacon)

  | is_unboxed, all_nullary_constructors =
      -- Enumerative type
      let (_, tags) = dataTags datacons
          cons = map dataConCon datacons
          disjuncts = zip cons tags
      in return $ enumValLayout disjuncts

  | is_unboxed, [datacon] <- datacons = do
      -- Product type
      fields <- instantiateDataCon ty_args datacon
        
      -- Fields must not be reference objects
      let fields' = map from_val fields
            where
              from_val (ValLayout vl) = vl
              from_val (MemLayout _) =
                internalError "getAlgLayout: Invalid field type"

      return $ productValLayout (dataConCon datacon) fields'

  | is_unboxed =
      internalError "valDataTypeLayout: Cannot construct values of this type"
      
  | not is_unboxed, [datacon] <- datacons = do
      -- Boxed product type
      fields <- instantiateDataCon ty_args datacon
      return $ boxedObjectLayout $ nonSumMemLayout $
        productMemLayout (dataConCon datacon) fields
      
  | not is_unboxed = do
      -- Boxed SOP type
      members <- forM datacons $ \datacon -> do
        fields <- instantiateDataCon ty_args datacon
        return $ productMemLayout (dataConCon datacon) fields
      
      let (_, tags) = dataTags datacons
      return $ boxedObjectLayout $ taggedSumMemLayout $ zip tags members
  where
    -- True if this type is represented as a value; False if boxed
    is_unboxed = case dataTypeRepresentation tycon
                 of Value -> True
                    Boxed -> False
                    _ -> internalError "getValDataTypeLayout"

    -- True if no constructors have fields
    all_nullary_constructors = all (null . dataConPatternArgs) datacons

getRefAlgLayout :: Type -> Lower AlgMemLayout
getRefAlgLayout ty =
  case fromVarApp ty
  of Just (op, [arg])
       | op `isPyonBuiltin` the_Referenced -> do
           arg_layout <- getRefLayout arg
           return $ nonSumMemLayout $ referenceLayout arg_layout
     _ -> do
       tenv <- getTypeEnv
       case lookupDataTypeForLayout tenv ty of
         Nothing ->
           case ty
           of AnyT {} -> internalError "getAlgLayout: Not implemented for Any"
              _ -> internalError "getAlgLayout: Invalid type"
         Just inst_type@(data_type, _, _) ->
           case dataTypeRepresentation data_type
           of Referenced -> getRefDataTypeLayout inst_type
              _ -> internalError "getAlgLayout: Invalid representation"

getRefDataTypeLayout :: InstantiatedDataType -> Lower AlgMemLayout
getRefDataTypeLayout (_, ty_args, datacons)
  | null datacons =
      -- Uninhabited type
      internalError "refDataTypeLayout: Type is uninhabited"

  | [datacon] <- datacons = do
      -- Singleton object.  It's a product with no tag.
      fields <- instantiateDataCon ty_args datacon
      return $ nonSumMemLayout $ productMemLayout (dataConCon datacon) fields

  | otherwise = do
      -- Sum of products type
      members <- forM datacons $ \datacon -> do
        fields <- instantiateDataCon ty_args datacon
        return $ productMemLayout (dataConCon datacon) fields
      
      let (_, tags) = dataTags datacons
      return $ taggedSumMemLayout $ zip tags members

-- | Compute the low-level representation of a data type
getLayout :: ReturnType -> Lower Layout
getLayout (repr ::: ty) =
  case repr
  of ValRT -> fmap ValLayout $ getValLayout ty
     BoxRT -> return $ ValLayout (LL.PrimType LL.OwnedType)
     ReadRT -> ref_layout
     OutRT -> ref_layout
     _ -> internalError "getLayout: Unexpected representation"
  where
    ref_layout = fmap MemLayout $ getRefLayout ty

getValLayout :: Type -> Lower ValLayout
getValLayout ty =
  case getLevel ty
  of TypeLevel ->
       case fromVarApp ty
       of Just (op, args)
            | op `isPyonBuiltin` the_bool ->
                return (LL.PrimType LL.BoolType)
            | op `isPyonBuiltin` the_int ->
                return (LL.PrimType LL.pyonIntType)
            | op `isPyonBuiltin` the_float -> 
                return (LL.PrimType LL.pyonFloatType)
            | otherwise -> do
                tenv <- getTypeEnv
                case lookupDataTypeForLayout tenv ty of
                  Just inst_type@(tycon, _, _) ->
                    case dataTypeRepresentation tycon
                    of Boxed -> return (LL.PrimType LL.OwnedType)
                       Value -> do
                         -- Use the algebraic data type layout
                         alg_layout <- getValDataTypeLayout inst_type
                         return $ discardValStructure alg_layout
                       _ -> internalError "getValLayout"
                  Nothing -> internalError "getValLayout: Unexpected type"
          _ -> internalError "getLayout: Head is not a type application"
     KindLevel -> return (LL.PrimType LL.UnitType)

getRefLayout :: Type -> Lower MemLayout
getRefLayout ty =
  case fromVarApp ty
  of Just (op, [arg])
       | op `isPyonBuiltin` the_Referenced ->
           return $ memValueLayout (LL.PrimType LL.PointerType)
     Just (op, [arg1, arg2])
       | op `isPyonBuiltin` the_array -> do
           field_layout <- getRefLayout arg2
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
           case dataTypeRepresentation data_type
           of Value -> fmap memValueLayout $ getValLayout ty
              Boxed -> return $ memValueLayout (LL.PrimType LL.OwnedType)
              Referenced -> do
                alg_layout <- getRefDataTypeLayout inst_type
                return $ discardMemStructure alg_layout
              _ -> internalError "getAlgLayout: Invalid representation"

-- | Instantiate a data constructor.  Get the layouts of its members.
instantiateDataCon :: [Type] -> DataConType -> Lower [Layout]
instantiateDataCon ty_args data_con = do
  -- Create existential variables and get the field types
  (ex_vars, field_reprs, _) <-
    liftFreshVarM $ instantiateDataConTypeWithFreshVariables data_con ty_args

  -- Add existential variables to the environment
  insert_ex_vars ex_vars $
    -- Get layouts of fields
    mapM getLayout field_reprs
  where
    insert_ex_vars params m = foldr ins m params
    ins (ValPT (Just v) ::: ty) m = assumeType v ty m

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
