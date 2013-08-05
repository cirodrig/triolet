{-| Type object generation.

There are several, similar pieces of code here for computing type
information.  Some code computes type objects, some code computes sizes. 
Out of the code that computes type objects, some computes bare objects
and some computes value objects.

This code creates a global type object for each algebraic data type definition.
In many ways, type objects hold 

For type object constructor @S@ and type constructor @T@,
the global type object is a function or constant of type
@forall tys. size_parameters -> S (T tys)@.
-}

module SystemF.Datatypes.TypeObject
       (definePrimitiveValInfo,
        valInfoDefinition,
        bareInfoDefinition,
        boxInfoDefinitions)
where

import Prelude hiding(catch)

import Control.Exception
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Writer
import qualified Data.IntMap as IntMap
import Data.List
import Data.Maybe
import Data.Monoid
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import Common.MonadLogic
import Common.Supply
import qualified LowLevel.CodeTypes as LL
import qualified LowLevel.Syntax as LL
import SystemF.Build
import SystemF.Syntax
import SystemF.MemoryIR
import SystemF.PrintMemoryIR
import SystemF.Datatypes.DynamicTypeInfo
import SystemF.Datatypes.Structure
import SystemF.Datatypes.Util(unboxedMemTagType, runGenMWithoutOutput)
import SystemF.Datatypes.Layout
import qualified SystemF.Datatypes.Size
import SystemF.Datatypes.InfoCall
import SystemF.Datatypes.Code
import Type.Type
import Type.Environment
import Type.Eval

-------------------------------------------------------------------------------

readBufferT = cursorT `AppT` byteT

data StaticValInfo =
  StaticValInfo
  { staticValSize        :: !Int
  , staticValAlignment   :: !Int
  , staticValPointerless :: !Bool
    -- | Serialize or deserialize a value.
    --   Has type @a -> OpaqueRef -> Store -> Store@.
  , staticValSerializer  :: !SerDes
  }

-- | A pair of a serializer and deserializer for a particular type. 
--   The serializer has type @t -> OpaqueRef -> Store -> Store@.
--   The deserializer has type @cursor (Stored byte) -> (cursor (Stored byte), t)@.
data SerDes = SerDes {serializer, deserializer :: ExpM}

-- | Compute the representation of a type that has kind @val@.
--   The representation must be known statically.
staticValInfo :: IdentSupply LL.Var -> Type -> UnboxedTypeEvalM StaticValInfo
staticValInfo var_supply ty = {-# SCC "staticValInfo" #-} do
  s <- computeStructure ty
  case s of
    PrimStruct pt  -> staticPrimTypeInfo ty pt
    DataStruct dat -> staticSumInfo var_supply ty dat

staticPrimTypeInfo ty pt = do
  serdes <- staticPrimTypeSerializer ty pt
  return $ StaticValInfo (LL.sizeOf pt) (LL.alignOf pt) (LL.pointerlessness pt) serdes

staticSumInfo var_supply ty d = do
  -- Compute the type's memory layout, which must be known
  l <- runGenMWithoutOutput var_supply $ computeLayout emptyTypeInfo ValK (DataStruct d)
  let value_type  = SystemF.Datatypes.Size.layoutValueType False l
      size        = LL.sizeOf value_type
      alignment   = LL.alignOf value_type
      pointerless = LL.pointerlessness value_type

  serdes <- staticAlgValueSerializer ty d

  return $ StaticValInfo size alignment pointerless serdes

-- | Create serializers for values of the given type.
--   Deconstruct the value, write the tag, and write the fields.
staticValueSerializer :: Type -> UnboxedTypeEvalM SerDes
staticValueSerializer ty = staticValueSerializer' ty =<< computeStructure ty

staticValueSerializer' ty (PrimStruct pt) =
  staticPrimTypeSerializer ty pt
    
staticValueSerializer' ty (DataStruct adt) =
  staticAlgValueSerializer ty adt

staticPrimTypeSerializer ty _ = do
  ty' <- reduceToWhnf ty
  return $! case fromVarApp ty'
            of Just (op, [])
                 | op == intV   -> serdes putIntV getIntV
                 | op == uintV  -> serdes putUintV getUintV
                 | op == floatV -> serdes putFloatV getFloatV
               _ -> internalError $ "staticPrimTypeSerializer: Unexpected type " ++ show (pprType ty')
  where
    serdes s d = SerDes (varE' s) (varE' d)

-- | Create serializers for algebraic data of the given type.
--   The serializer deconstructs the value, writes the tag,
--   and writes the fields.
--   The deserializer reads the tag, reads the fields, and
--   constructs the value.
staticAlgValueSerializer :: Type
                         -> Data
                         -> UnboxedTypeEvalM SerDes
staticAlgValueSerializer ty (Data NotBoxed alts) = do
  -- Create serializers for all fields
  let field_tag_type = fromMaybe LL.UnitType $ unboxedMemTagType (length alts)
  field_serializers <-
    sequence 
    [ assumeBinders (deConExTypes decon) $ mapM fieldSerializer field_types
    | Alternative decon field_types <- alts]
  deserializer_indices <- mapM get_constructor_index alts

  -- Get the type constructor information
  Just (dtype_con, _) <- deconVarAppType ty
  Just data_type <- lookupDataType dtype_con

  -- Create a function that deconstructs its argument and serializes the
  -- constructor term that it finds
  serializer <-
    lamE $ mkFun [] (\ [] -> return ([ty, opaqueRefT, storeT], storeT))
    (\ [] [value, buffer, state] ->
        mkCase ty (varE' value) []
        [ (con, dj_deconstructor field_tag_type con_index buffer state (map fst serializers))
        | (serializers, alt) <- zip field_serializers alts
        , let Alternative (VarDeCon con _ _) _ = alt
        , let con_index = dataTypeConIndex data_type con])

  -- Create a function that reads an object from a buffer
  deserializer <-
    lamE $
    mkFun [] (\ [] -> return ([readBufferT], deserialized_type))
    (\ [] [buffer] -> do
        -- Read the constructor index and dispatch
        let g = getConIndex field_tag_type deserialized_type
                [ (ix, dj_constructor alt (map snd serializers))
                | (ix, alt, serializers) <-
                     zip3 deserializer_indices alts field_serializers]
        createGetCode g buffer (retupleExp' deserialized_type))

  return $ SerDes serializer deserializer
  where
    -- Return type of deserializer
    deserialized_type =
      UTupleT [ValK, ValK] `typeApp` [readBufferT, ty]

    get_constructor_index (Alternative (VarDeCon con _ _) _) = do
      Just dcon_type <- lookupDataCon con
      return $ dataConIndex dcon_type

    -- Write an object by writing its constructor index, followed by its fields
    dj_deconstructor
      field_tag_type con_index buffer state serializers _ field_values =
      let put = mconcat (putConIndex field_tag_type con_index :
                         zipWith putField serializers field_values)
      in createPutCode put buffer state

    -- Read a constructor by reading its fields and constructing the object
    -- TODO: What about existential types?
    dj_constructor (Alternative (VarDeCon con ty_args []) _) serializers = do
      xs <- sequence serializers
      return $ valConE' (VarCon con ty_args []) xs

fieldSerializer :: (BaseKind, Type)
                -> UnboxedTypeEvalM (ExpM -> Put, Get ExpM ExpM)
fieldSerializer (BoxK, ty) = return (put_boxed_object, get_boxed_object)
  where
    get_boxed_object =
      getAndUntuple ty (\b -> varAppE' getBoxedObjectV [ty] [varE' b])
    put_boxed_object x = Put $ \buffer state ->
      return $ varAppE' putBoxedObjectV [ty] [x, varE' buffer, varE' state]

fieldSerializer (ValK, ty) = do
  serdes <- staticValueSerializer ty
  let p = mk_putter $ serializer serdes 
  let g = mk_getter $ deserializer serdes
  return (p, g)
  where
    mk_putter ser val = Put $ \buffer state ->
      return $ appE' ser [] [val, varE' buffer, varE' state]

    mk_getter des =
      getAndUntuple ty (\b -> appE' des [] [varE' b])

-- | A code generator that takes an output buffer handle and a state
--   variable, and produces code to write output.
--   An example generated expression is
--
-- > putInt x o s
--
--   where @o@ is the output buffer handle and @s@ is the state variable.
newtype Put = Put {createPutCode :: Var -> Var -> UnboxedTypeEvalM ExpM}

instance Monoid Put where
  -- Put nothing
  mempty = Put $ \_ state -> return $ varE' state

  -- Put x, then put y
  x `mappend` y = Put $ \buffer state -> do
    state2 <- newClonedVar state
    e <- createPutCode x buffer state
    f <- createPutCode y buffer state2
    return $ letE (patM (state2 ::: storeT)) e f

-- | Write a constructor index, in the same format as the object's 
--   in-memory tag value.
putConIndex :: LL.PrimType -> Int -> Put
putConIndex tag_type index = Put $ \buffer state ->
  let index_lit = uintL index
      put op = return $ varAppE' op [] [index_lit, varE' buffer, varE' state]
  in case tag_type
     of LL.UnitType -> return $ varE' state -- Do not write anything
        LL.IntType LL.Unsigned LL.S8 -> put putUintAsUint8V
        LL.IntType LL.Unsigned LL.S16 -> put putUintAsUint16V
        _ | tag_type == LL.trioletUintType -> put putUintV

-- | Write a list of fields, given their serializers and values
putFields :: [(ExpM -> Put, ExpM)] -> Put
putFields fs = mconcat [putField s e | (s, e) <- fs]

putField put value = put value

-- | A code generator that reads a value from an input buffer and uses that
--   value.
newtype Get r a =
  Get {createGetCode :: Var -> (a -> Var -> UnboxedTypeEvalM r) -> UnboxedTypeEvalM r}

instance Monad (Get r) where
  return x = Get $ \b k -> k x b
  m >>= f = Get $ \b k -> createGetCode m b $ \x b' -> createGetCode (f x) b' k

liftGet :: UnboxedTypeEvalM a -> Get r a
liftGet m = Get $ \b k -> do x <- m
                             k x b

-- | Untuple the result of a single read operation.
--
--   The argument of type @Var -> ExpM@ takes a buffer variable and 
--   returns a buffer-reading expression.  From this, a 'Get' value is
--   produced that extracts the newly read value from the expression.
getAndUntuple :: Type -> (Var -> ExpM) -> Get ExpM ExpM
getAndUntuple ty mk_read = Get $ \buffer cont -> do
  buffer' <- newClonedVar buffer
  read_value <- newAnonymousVar ObjectLevel
  body <- cont (varE' read_value) buffer'
  return $ untupleExp ty (mk_read buffer) buffer' read_value body

untupleExp value_type scrutinee buffer_var value_var body =
  ExpM $ CaseE defaultExpInfo scrutinee []
  [AltM $ Alt (TupleDeCon [readBufferT, value_type]) Nothing
   [patM (buffer_var ::: readBufferT), patM (value_var ::: value_type)] body]

retupleExp value_type value_exp buffer_var =
  valConE' (TupleCon [readBufferT, value_type]) [varE' buffer_var, value_exp]

retupleExp' value_type value_exp buffer_var =
  return $ retupleExp value_type value_exp buffer_var

-- | Get the current buffer value
getCurrentBuffer :: Get a Var
getCurrentBuffer = Get $ \buffer k -> k buffer buffer

-- | Read and dispatch on a constructor index, whichis  in the same format
--   as the object's in-memory tag value.  The arguments are pairs of
--   (constructor-index, handler); all constructors should be represented.
--   The arguments should each return an object of type @result_type@.
getConIndex :: LL.PrimType -> Type -> [(Int, Get ExpM ExpM)] -> Get ExpM ExpM
getConIndex tag_type result_type handlers =
  getAndUntuple uintT get_tag >>= dispatch
  where
    get_tag b =
      case tag_type
      of LL.UnitType -> retupleExp uintT (uintL 0) b
         LL.IntType LL.Unsigned LL.S8 -> get_uint getUint8AsUintV
         LL.IntType LL.Unsigned LL.S16 -> get_uint getUint16AsUintV
         _ | tag_type == LL.trioletUintType -> get_uint getUintV
      where
        get_uint op = varAppE' op [] [varE' b]
    -- Generate nested 'if' expressions.
    -- Pass the buffer around properly.
    dispatch index_value = Get $ \buffer cont -> do

      -- Generate nested if expressions. 
      -- Each branch expression returns a result of type 
      -- @(cursor (Stored byte), result_type)@.
      let generate_handler [(_, h)] =
            createGetCode h buffer $ retupleExp' result_type
          generate_handler ((i, h):hs) = do
            let test = varAppE' eqUV [] [index_value, uintL i]
            first_case <- createGetCode h buffer $ retupleExp' result_type
            other_cases <- generate_handler hs
            return $ ifE' test first_case other_cases

      dispatch_code <- generate_handler handlers

      -- Use the result
      buffer' <- newClonedVar buffer
      read_value <- newAnonymousVar ObjectLevel
      body <- cont (varE' read_value) buffer'

      -- Untuple the result so that it can be used
      return $ untupleExp result_type dispatch_code buffer' read_value body

-- | Create the representation of a @Stored t@, for a given value type @t@.
--   The type argument must be known statically.
storedRepr :: IdentSupply LL.Var -> Type -> UnboxedTypeEvalM BareInfo
storedRepr var_supply ty = do
  internalError $ "Not implemented: storedRepr for " ++ show (pprType ty)
{-  val_info <- staticValInfo var_supply ty
  let size = SizeAlign (uintL $ staticValSize val_info) (uintL $ staticValAlignment val_info)
             (if staticValPointerless val_info then isPointerFree else notPointerFree)
  is_ref <- liftTypeEvalM $ createNonRefEvidence (storedT `AppT` ty)
  return $ BareInfo size is_ref (internalError "storedRepr") (internalError "storedRepr")-}

-------------------------------------------------------------------------------

-- | Compute the size and alignment of an object header.
--   Size and alignment depend on whether the object is boxed and how many
--   constructors it has.
--
--   The results of this function must agree with
--   'SystemF.Datatypes.Layout.headerLayout'.
headerSize :: Boxing -> Int -> SizeAlign
headerSize boxing n_constructors = primSize header_type
  where
    -- Type of the object header
    header_type =
      case boxing
      of IsBoxed  -> LL.OwnedType
         NotBoxed -> fromMaybe LL.UnitType $ unboxedMemTagType n_constructors

-- | Compute the size and alignment of a type of kind 'val'
computeValInfo :: CoreDynTypeInfo
               -> Type
               -> Structure
               -> Gen ValInfo
computeValInfo type_info ty layout =
  case layout
  of PrimStruct pt            -> lift $ liftTypeEvalM $ primValInfo ty pt
     DataStruct (Data tag fs) -> sumValInfo type_info ty tag fs
     ForallStruct fa          -> forall_layout fa
     VarStruct v              -> var_layout v
     UninhabitedStruct        -> internalError "computeLayout: Uninhabited"
  where
    var_layout v = lift $ lookupValTypeInfo' type_info v

    forall_layout (Forall b t) = assumeBinder b $ do
      s <- lift $ computeStructure t
      computeValInfo type_info t s

sumValInfo :: CoreDynTypeInfo -> Type -> Boxing -> Alternatives
           -> Gen ValInfo
sumValInfo _ _ _ [] =
  internalError "computeValInfo: Uninhabited type"

sumValInfo type_info ty tag alts = do
  let header_layout = headerSize tag (length alts)
  disjunct_info <- mapM (alt_layout header_layout) alts

  -- Combine disjuncts
  size <- overlays disjunct_info

  -- Instantiate serializer and deserializer
  Just (ty_op, ty_args) <- lift $ liftTypeEvalM $ deconVarAppType ty
  Just data_type <- lookupDataType ty_op
  let serializer = varAppE' (dataTypeUnboxedSerializerVar data_type) ty_args []
  let deserializer = varAppE' (dataTypeUnboxedDeserializerVar data_type) ty_args []  
  
  return $ ValInfo size serializer deserializer

  where
    -- Layouts of fields of a case alternative
    alt_layout header_layout (Alternative decon fs) = do
      field_info <- assumeBinders (deConExTypes decon) $ mapM field_layout fs

      size <- structSize $
              header_layout : map (fieldDetailsSize . fiDetails) field_info

      return size

    field_layout (k, t) = fieldInfo type_info (k, t)

primValInfo :: Type -> LL.PrimType -> UnboxedTypeEvalM ValInfo
primValInfo ty pt = do
  -- Instantiate the serializer and deserializer for this type.
  -- They may take type parameters, but no run-time type info.
  ty' <- reduceToWhnf ty
  cond (fromTypeApp ty')
    [ -- Algebric data type 
      do (VarT ty_op, ty_args) <- it
         lift $ do
           Just data_type <- lookupDataType ty_op
           let serializer = varAppE' (dataTypeUnboxedSerializerVar data_type) ty_args []
           let deserializer = varAppE' (dataTypeUnboxedDeserializerVar data_type) ty_args []
           return $ ValInfo (primSize pt) serializer deserializer

      -- Coercion type
    , do (CoT k, [s, t]) <- it
         k' <- lift $ reduceToWhnf k
         let (serializer, deserializer) =
               case k' of
                 VarT v | v == bareV -> (varAppE' putBareCoercionV [s, t] [],
                                         varAppE' getBareCoercionV [s, t] [])
                        | v == boxV  -> (varAppE' putBoxCoercionV [s, t] [],
                                         varAppE' getBoxCoercionV [s, t] [])
         return $ ValInfo (primSize pt) serializer deserializer
    ]

primSize pt = SizeAlign size alignment pointer_free
  where
    size = uintL $ LL.sizeOf pt 
    alignment = uintL $ LL.alignOf pt
    pointer_free = if LL.pointerlessness pt
                   then isPointerFree
                   else notPointerFree

-- | Information about how a field of an object is represented
data FieldInfo = FieldInfo Type !FieldDetails

fiDetails (FieldInfo _ d) = d

-- | Kind-specific information about how a field of an object is represented
data FieldDetails =
    ValDetails ValInfo
  | BareDetails BareInfo
  | BoxDetails

fieldDetailsSize :: FieldDetails -> SizeAlign
fieldDetailsSize BoxDetails      = primSize LL.OwnedType
fieldDetailsSize (ValDetails i)  = val_info_size i
fieldDetailsSize (BareDetails i) = bare_info_size i

-- | Get the pointerlessness of this field.  The result is a boolean.
{-fieldDetailsPointerFree :: FieldDetails -> PointerFree
fieldDetailsPointerFree BoxDetails      = notPointerFree
fieldDetailsPointerFree (ValDetails i)  = val_info_pointers i
fieldDetailsPointerFree (BareDetails i) = bare_info_pointers i-}

-- | Get information about a field's representation
fieldInfo :: CoreDynTypeInfo -> (BaseKind, Type) -> Gen FieldInfo
fieldInfo type_info (k, t) = do
  d <- fieldDetails type_info k t
  return $ FieldInfo t d

fieldDetails :: CoreDynTypeInfo -> BaseKind -> Type -> Gen FieldDetails
fieldDetails type_info k t =
  case k
  of BoxK  -> return BoxDetails
     _    -> condM (lift $ deconVarAppType t)
             [ -- Algebraic data type: call the info function
               do aguard False  -- Disabled; doesn't work properly with existential types
                  Just (op, args) <- it
                  Just data_type <- lift $ lookupDataType op
                  lift $ do e <- callKnownUnboxedInfoFunction type_info data_type args
                            unpack_info e
               -- Otherwise, call 'structureRepr'
             , lift $ do s <- lift $ computeStructure t
                         structure_info s
             ]
  where
    -- Unpack an info value
    unpack_info e
      | k == BareK = fmap BareDetails $ unpackRepr t e
      | k == ValK  = fmap ValDetails $ unpackReprVal t e

    -- Compute info from a structure
    structure_info s
      | k == BareK = fmap BareDetails $ structureRepr type_info t s
      | k == ValK  = fmap ValDetails $ computeValInfo type_info t s

-- | Information about the size of a field of an object.
--   A 'FieldSize' contains size information about an unboxed field.
--   For a boxed field, it contains 'Nothing'.
data FieldSize = FieldSize Type !(Maybe SizeAlign)

fsSize (FieldSize _ d) = d

-- | Get the size of a field.  If boxed, it's the size of a pointer.
fsSize' (FieldSize _ Nothing)  = primSize LL.OwnedType
fsSize' (FieldSize _ (Just s)) = s

-- | Get information about a field's representation
fieldSize :: CoreDynSizeInfo -> (BaseKind, Type) -> Gen FieldSize
fieldSize type_info (k, t) = do
  d <- case k
       of BoxK  -> return Nothing
          BareK -> liftM Just field_details
          ValK  -> liftM Just field_details
  return $ FieldSize t d
  where
    field_details = do s <- lift $ computeStructure t
                       structureSize type_info k t s

-------------------------------------------------------------------------------

-- | Dynamic size info
type CoreDynSizeInfo = DynTypeInfo SizeAlign SizeAlign Length

-- | Compute dynamic size information of an unboxed data structure
structureSize :: CoreDynSizeInfo -> BaseKind -> Type -> Structure -> Gen SizeAlign
structureSize type_info kind ty layout =
  case layout
  of DataStruct (Data tag fs) -> sumSize type_info ty tag fs
     ForallStruct fa          -> forall_layout fa
     VarStruct v              -> var_layout v
     ArrStruct t ts           -> arrSize type_info ty t ts
     PrimStruct pt            -> return $ primSize pt
     StoredStruct t           -> stored_layout t
     UninhabitedStruct        -> internalError "structureSize: Uninhabited"
  where
    continue k t l = structureSize type_info k t l

    var_layout v = 
      case kind
      of ValK  -> lift $ lookupValTypeInfo' type_info v
         BareK -> lift $ lookupBareTypeInfo' type_info v

    forall_layout (Forall b t) = assumeBinder b $ do
      continue kind t =<< lift (computeStructure t)

    stored_layout t = continue ValK t =<< lift (computeStructure t)

sumSize type_info ty tag alts = do
  let header_layout = headerSize tag (length alts)

  -- Compute size of all data constructors
  constructor_sizes <-
    forM alts $ \(Alternative decon fs) ->
    assumeBinders (deConExTypes decon) $ do
      -- Compute field sizes
      sizes <- mapM (return . fsSize' <=< fieldSize type_info) fs

      -- Compute size of this disjunct
      structSize (header_layout : sizes)

  -- Combine isizes
  overlays constructor_sizes

arrSize type_info ty size elem = do
  size_val <- lift $ lookupIntTypeInfo' type_info size
  elem_size <- structureSize type_info BareK ty =<< lift (computeStructure elem)
  arraySize size_val elem_size

-- | Compute sizes of all unboxed fields of one disjunct of a data type.
--   Return a list with one value per field.  Boxed fields are represented
--   by 'Nothing'.
disjunctSizes :: CoreDynSizeInfo -> Type -> Data -> Var
              -> Gen [Maybe SizeAlign]
disjunctSizes type_info ty (Data tag djs) con =
  let Alternative decon fs = findAlternative con djs
  in assumeBinders (deConExTypes decon) $ do

    -- Compute size of each unboxed field
    forM fs $ \f -> do
      field_info <- fieldSize type_info f
      return $! fsSize field_info

-------------------------------------------------------------------------------
-- Representations

-- | Compute dynamic type information of a bare data structure
structureRepr :: CoreDynTypeInfo
              -> Type
              -> Structure
              -> Gen BareInfo
structureRepr type_info ty layout =
  case layout
  of DataStruct (Data tag fs) -> sumRepr type_info ty tag fs
     StoredStruct ty          -> do ll_supply <- getLLVarIdentSupply 
                                    lift $ storedRepr ll_supply ty
     ForallStruct fa          -> forall_layout fa
     VarStruct v              -> var_layout v
     ArrStruct t ts           -> arrRepr type_info t ts
     PrimStruct pt            -> internalError "structureRepr: Unexpected type"
     UninhabitedStruct        -> internalError "structureRepr: Uninhabited"
  where
    continue t l = structureRepr type_info t l

    var_layout v = lift $ lookupBareTypeInfo' type_info v

    forall_layout (Forall b t) =
      assumeBinder b $ continue t =<< lift (computeStructure t)

sumRepr type_info ty tag alts = do
  let header_layout = headerSize tag (length alts)

  -- Compute representation info for all data constructors
  field_info <-
    forM alts $ \(Alternative decon fs) ->
    assumeBinders (deConExTypes decon) $
    mapM (fieldInfo type_info) fs
    
  -- Compute properties of data constructors
  constructor_info <- zipWithM (alt_repr header_layout) field_info alts

  (serializer, deserializer) <- serializer_code

  -- Combine info
  sum_size <- overlays constructor_info
  is_ref <- lift $ createNonRefEvidence ty
  return $ BareInfo sum_size is_ref serializer deserializer
  where
    -- Compute repr information for one constructor.
    -- The returned tuple contains values for the size, copy, and pointerless 
    -- fields of 'BareInfo'.
    alt_repr :: SizeAlign -> [FieldInfo] -> Alternative -> Gen SizeAlign
    alt_repr header_layout field_info (Alternative decon fs) =
      assumeBinders (deConExTypes decon) $ do
        size <- let sizes = [fieldDetailsSize d | FieldInfo _ d <- field_info]
                in structSize (header_layout : sizes)
        return size
        
    -- Create calls to the serializer and deserializer variables
    serializer_code = do
      Just (dtype_con, dtype_args) <- lift $ deconVarAppType ty
      Just dtype <- lookupDataType dtype_con

      -- Look up size parameters
      size_param_types <- lift $ instantiateSizeParams dtype dtype_args
      size_params <- mapM get_dyn_info size_param_types

      let serializer_var =
            -- Override the default serialization for some data types
            -- TODO: Implement a more flexible override mechanism
            case ()
            of () | dataTypeCon dtype == listSectionV ->
                      putListSection_optimizedV
               _ -> dataTypeUnboxedSerializerVar dtype
          serializer_call = varAppE' serializer_var dtype_args size_params
      let deserializer_var = dataTypeUnboxedDeserializerVar dtype
          deserializer_call = varAppE' deserializer_var dtype_args size_params
      return (serializer_call, deserializer_call)

    -- Get dynamic type info.  This function must not fail to find type info.
    get_dyn_info kt = do
      Just e <- constructInfo type_info kt
      return e

-- | Create evidence that the given type is not 'Ref'
createNonRefEvidence :: Type -> UnboxedTypeEvalM IsRef
createNonRefEvidence ty = do
  Just (op, args) <- deconVarAppType ty
  when (op == refV) $ internalError "createNonRefEvidence"

  -- Create an expression:
  -- > notAReference @ty (unsafeMakeCoercion @(AsBox ty) @(Boxed ty))
  let co = varAppE' idCoercionV [asBoxT `AppT` ty] []
  return $ IsRef $ conE' (VarCon notAReferenceV [ty] []) [] Nothing [co]

{-
sumCopyFunction :: CoreDynTypeInfo
                -> Type
                -> [([FieldInfo], Alternative)]
                -> Gen ExpM
sumCopyFunction type_info ty disjuncts = do
  -- Create size parameters
  let Just (con, ty_args) = fromVarApp ty
  Just data_type <- lookupDataType con
  size_param_types <- lift $ instantiateSizeParams data_type ty_args
  size_params <- mapM (constructKnownSizeParameter type_info) size_param_types

  -- Create variables
  copy_src <- lift $ newAnonymousVar ObjectLevel
  copy_dst <- lift $ newAnonymousVar ObjectLevel

  -- Create an expression that copies from src to dst
  copy_exp <-
    lift $ assume copy_src ty $ assume copy_dst (AppT outPtrT ty) $
    mkCase ty (varE' copy_src) size_params
    (reconstructors ty_args size_params copy_dst)

  -- Create function
  let copy_fun = FunM $ Fun { funInfo = defaultExpInfo
                            , funTyParams = []
                            , funParams = [patM (copy_src ::: ty),
                                           patM (copy_dst ::: AppT outPtrT ty)]
                            , funReturn = storeT
                            , funBody = copy_exp}

  return $ ExpM $ LamE defaultExpInfo copy_fun
  where
    reconstructors ty_args size_params copy_dst =
      [(con, reconstruct ty_args size_params copy_dst field_info alt)
      | (field_info, alt@(Alternative (VarDeCon con _ _) _)) <- disjuncts]

    -- Reconstruct one case alternative from the given
    -- 'ex_types' and 'field_vals'
    reconstruct ty_args size_params copy_dst field_info
      (Alternative decon field_types) ex_types field_vals =

      assumeBinders (deConExTypes decon) $ do
        let VarDeCon con _ _ = decon

        -- Create a data constructor expression
        let copy = copyConstructor type_info con ty_args size_params ex_types
                   (zip field_info field_vals)

        -- Apply to the return value
        return $ appE' copy [] [varE' copy_dst]

-- | Construct a bare object from the given fields.  Convert bare fields to
--   initializers.
copyConstructor :: CoreDynTypeInfo -> [Type] -> Var -> [Type] -> [ExpM]
                -> [Type] -> [(FieldInfo, ExpM)] -> ExpM
copyConstructor type_info data_type con ty_args size_params ex_types fields =
  unboxedConE' (VarCon con ty_args ex_types) size_params (map field_expr fields)
  where
    field_expr (FieldInfo ty details, e) =
      case details
      of ValDetails _  -> e
         BoxDetails    -> e
         BareDetails d -> varAppE' blockcopyV [data_type]
                          [packSizeAlign $ bare_info_size d, e]
-}

arrRepr :: CoreDynTypeInfo -> Type -> Type -> Gen BareInfo
arrRepr type_info size elem = do
  let array_type = varApp arrV [size, elem]
  size_val <- lift $ lookupIntTypeInfo' type_info size
  elem_repr <- structureRepr type_info elem =<< lift (computeStructure elem)

  -- Call 'repr_arr' to compute the array's representation
  let expr = varAppE' bareInfo_arrV [size, elem]
             [packLength size size_val, packRepr elem elem_repr]
  unpackRepr array_type expr

-------------------------------------------------------------------------------

-- | Construct dynamic type information from a set of bindings.
makeDynTypeInfo :: [(Var, KindedType)] -> Gen CoreDynTypeInfo
makeDynTypeInfo bs = do
  updates <- mapM mk_update bs
  return $ foldr ($) emptyTypeInfo updates
  where
    -- Extract untyped size information from the data structure
    mk_update (v, KindedType ValK t) = do 
      sa <- unpackReprVal t (varE' v)
      return $ insertValTypeInfo t sa

    mk_update (v, KindedType BareK t) = do 
      rep <- unpackRepr t (varE' v)
      return $ insertBareTypeInfo t rep

    mk_update (v, KindedType IntIndexK t) = do
      l <- unpackLength t (varE' v)
      return $ insertIntTypeInfo t l

-- | Construct dynamic type information from a set of bindings.
makeDynSizeInfo :: [(Var, KindedType)] -> Gen CoreDynSizeInfo
makeDynSizeInfo bs = do
  updates <- mapM mk_update bs
  return $ foldr ($) emptyTypeInfo updates
  where
    -- Extract untyped size information from the data structure
    mk_update (v, KindedType ValK t) = do
      sa <- unpackSizeAlignVal t (varE' v)
      return $ insertValTypeInfo t sa

    mk_update (v, KindedType BareK t) = do 
      sa <- unpackSizeAlign t (varE' v)
      return $ insertBareTypeInfo t sa

    mk_update (v, KindedType IntIndexK t) = do
      l <- unpackLength t (varE' v)
      return $ insertIntTypeInfo t l

-- | Create a parameteric global definition.  If it takes any parameters, it
--   will be a global function; otherwise, it will be a global constant.
parametricDefinition :: [Binder] -- ^ Type parameters
                     -> [Type]   -- ^ Parameter types
                     -> Type     -- ^ Type of body's result
                     -> ([Var] -> UnboxedTypeEvalM ExpM) -- ^ Compute body
                     -> UnboxedTypeEvalM (Ent Mem)
parametricDefinition ty_params param_tys return_ty mk_body = do
  param_vars <- replicateM (length param_tys) $ newAnonymousVar ObjectLevel

  -- Compute the body
  body <- assumeBinders ty_params $
    assumeBinders (zipWith (:::) param_vars param_tys) $
    mk_body param_vars

  -- Create a function or constant
  let entity =
        if null ty_params && null param_tys
        then DataEnt $ Constant defaultExpInfo return_ty body
        else FunEnt $ FunM $
             Fun { funInfo = defaultExpInfo 
                 , funTyParams = map TyPat ty_params
                 , funParams = [patM (v ::: t) | (v, t) <- zip param_vars param_tys]
                 , funReturn = return_ty
                 , funBody = body
                 }
  return entity

-- | Create a function definition for a data type's info variable.
--
--   This function creates function parameters and returns, and sets up
--   the lookup table of dynamic type information
typeInfoDefinition :: IdentSupply LL.Var
                   -> DataType
                   -> ([ExpM] -> CoreDynTypeInfo -> Gen ExpM)
                   -> UnboxedTypeEvalM (Ent Mem)
typeInfoDefinition var_supply dtype construct_info =
  parametricDefinition ty_params param_size_types return_type make_body
  where
    -- Type parameters come directly from the data type definition
    ty_params = dataTypeParams dtype

    -- Parameters are based on size parameters and static types
    param_types =
      let l = dataTypeLayout' dtype
      in layoutSizeParamTypes l ++ layoutStaticTypes l

    param_size_types = map infoType param_types

    -- Return type is @Info (Con type_arguments)@
    return_type = infoTycon (dataTypeKind dtype) `varApp`
                  [dataTypeCon dtype `varApp`
                   [VarT v | v ::: _ <- dataTypeParams dtype]]

    -- Set up dynamic type information and construct an info term
    make_body parameters = runGen var_supply $ do
      dyn_info <- makeDynTypeInfo (zip parameters param_types)
      construct_info (map varE' parameters) dyn_info

-- | Compute the size types of a data constructor fields.
--   The returned list contains one value per field.  The value is 'Nothing'
--   for boxed fields, or the type of the field's run-time size information
--   otherwise.
sizeInfoFieldTypes :: DataConType -> [Maybe Type]
sizeInfoFieldTypes dcon_type = let 
    dtype = dataConType dcon_type

    -- Type parameters come directly from the data type definition
    ty_params = dataTypeParams dtype
    ex_types = dataConExTypes dcon_type

    -- Compute field sizes
    field_size (_, BoxK)  = Nothing
    field_size (t, ValK)  = Just $ sizeAlignValT `AppT` t
    field_size (t, BareK) = Just $ sizeAlignT `AppT` t

    in map field_size $ dataConFields dcon_type

-- | Create a function definition for computing a data constructor's
--   fields' sizes.
--
--   This function creates function parameters and returns, and sets up
--   the lookup table of dynamic type information.
--
--   The function definition is parameterized over both the data type's
--   parameters and the data constructor's existential type parameters.
--   Existential types don't affect the result's value, but they may
--   affect its type.
sizeInfoDefinition :: IdentSupply LL.Var
                   -> DataConType -> UnboxedTypeEvalM (Ent Mem)
sizeInfoDefinition var_supply dcon_type =
  parametricDefinition (ty_params ++ ex_types)
  param_size_types return_type make_body
  where
    dtype = dataConType dcon_type

    -- Type parameters come directly from the data type definition
    ty_params = dataTypeParams dtype
    ex_types = dataConExTypes dcon_type

    -- Parameters are based on size parameters and static types
    param_types =
      let l = dataTypeLayout' dtype
      in layoutSizeParamTypes l ++ layoutStaticTypes l

    param_size_types = map sizeParamType param_types

    -- Type of size information for each field
    field_size_types = sizeInfoFieldTypes dcon_type

    -- The returned tuple contains all size informations
    return_field_types = catMaybes field_size_types
    return_type =
      let field_kinds = [ValK | _ <- return_field_types]
      in UTupleT field_kinds `typeApp` return_field_types

    -- Construct a data structure for the size of a field,
    -- given its type and unlifted value
    pack_fields :: [Maybe SizeAlign] -> ExpM
    pack_fields field_values =
      let packed_values =
            catMaybes $
            zipWith pack_field (dataConFields dcon_type) field_values
          tuple_con = TupleCon return_field_types
      in valConE' tuple_con packed_values
      where
        pack_field (ty, ValK)  (Just sa) = Just $ packSizeAlignVal ty sa 
        pack_field (ty, BareK) (Just sa) = Just $ packSizeAlign ty sa 
        pack_field (ty, BoxK)  Nothing   = Nothing

    -- Set up dynamic type information and compute sizes of disjuncts
    make_body parameters = runGen var_supply $ do
      dyn_info <- makeDynSizeInfo (zip parameters param_types)
      let ty = dataTypeCon dtype `varApp` [VarT v | v ::: _ <- ty_params]

      -- Compute sizes
      DataStruct dat <- lift $ computeStructure ty
      field_sizes <- disjunctSizes dyn_info ty dat (dataConCon dcon_type)

      -- Create a tuple
      return $ pack_fields field_sizes

sizeInfoDefinitions var_supply dtype =
  forM (dataTypeDataConstructors dtype) $ \c -> do
    Just dcon_type <- lookupDataCon c
    ent <- sizeInfoDefinition var_supply dcon_type
    return $ mkDef (dataTypeFieldSizeVar dtype c) ent

-------------------------------------------------------------------------------
-- Entry points

-- | Define an info variable for a primitive value type.
--   Primitive types have no data constructors, so there are no size info 
--   variables.
definePrimitiveValInfo :: IdentSupply LL.Var
                       -> DataType -> UnboxedTypeEvalM [GDef Mem]
definePrimitiveValInfo var_supply dtype
  | dataTypeIsAbstract dtype && not (dataTypeIsAlgebraic dtype) &&
    null (dataTypeDataConstructors dtype) =
      valInfoDefinition var_supply dtype
  | otherwise =
      internalError "definePrimitiveValInfo"

-- | Create definitions of layout information for the data type.
--   One definition is created for unboxed types, or one per data constructor
--   for boxed types.
valInfoDefinition :: IdentSupply LL.Var
                  -> DataType -> UnboxedTypeEvalM [GDef Mem]
valInfoDefinition var_supply dtype = do
  ent <- typeInfoDefinition var_supply dtype build_info
  let info_def = addExportedAttribute $ addInlineAttribute $ mkDef info_var ent
  return [info_def]
  --size_defs <- sizeInfoDefinitions var_supply dtype

{-
  -- DEBUG: create and print storedRepr.  The result is not used.
  let l = dataTypeLayout' dtype
  when (null (layoutSizeParamTypes l) && null (layoutStaticTypes l)) $ do
    typeInfoDefinition var_supply dtype $ \_ -> do
      lift $ storedRepr var_supply ty
      return $ uintL 0
    return ()
-}
  
  --return (info_def : size_defs)
  where
    ty_args = [VarT v | v ::: _ <- dataTypeParams dtype] 
    ty = dataTypeCon dtype `varApp` ty_args
    info_var = dataTypeUnboxedInfoVar dtype

    -- Create the info object for this data type constructor
    build_info _ dyn_info = do
      sa <- computeValInfo dyn_info ty =<< lift (computeStructure ty)
      return $ packReprVal ty sa

bareInfoDefinition :: IdentSupply LL.Var
                   -> DataType -> UnboxedTypeEvalM [GDef Mem]
bareInfoDefinition var_supply dtype = do
  ent <- typeInfoDefinition var_supply dtype build_info
  let info_def = addExportedAttribute $ addInlineAttribute $ mkDef info_var ent
  return [info_def]
  --size_defs <- sizeInfoDefinitions var_supply dtype
  --return (info_def : size_defs)
  where
    ty_args = [VarT v | v ::: _ <- dataTypeParams dtype] 
    ty = dataTypeCon dtype `varApp` ty_args
    info_var = dataTypeUnboxedInfoVar dtype

    -- Create the info object for this data type constructor
    build_info _ dyn_info = do
      -- Create a recursive call to the info object for this type constructor
      rep <- structureRepr dyn_info ty =<< lift (computeStructure ty)
      return $ packRepr ty rep

-- Add an \"inline-final\" attribute to functions.
-- We inline unboxed info.  It's a good idea because it gets rid
-- of type objects.
addInlineAttribute d =
  modifyDefAnnotation make_inlined d
  where
    make_inlined d = d { defAnnInlineRequest = InlAggressively
                       , defAnnInlinePhase = InlFinal
                       }

addExportedAttribute d =
  modifyDefAnnotation (\a -> a {defAnnExported = True}) d

boxInfoDefinitions :: IdentSupply LL.Var
                   -> DataType -> UnboxedTypeEvalM [GDef Mem]
boxInfoDefinitions var_supply dtype = do
  info_defs <- forM (dataTypeDataConstructors dtype) $ \c -> do
    Just dcon_type <- lookupDataCon c
    ent <- typeInfoDefinition var_supply dtype $ build_info dcon_type
    return $ add_attributes $ mkDef (dataTypeBoxedInfoVar dtype c) ent
  return info_defs
  --size_defs <- sizeInfoDefinitions var_supply dtype
  --return (info_defs ++ size_defs)
  where
    ty_args = [VarT v | v ::: _ <- dataTypeParams dtype] 
    ty = dataTypeCon dtype `varApp` ty_args

    -- Create the info object for this data type constructor
    build_info dcon_type info_params dyn_type_info = do
      let ix = dataConIndex dcon_type
          ser = dataTypeBoxedSerializerVar dtype (dataConCon dcon_type)
          des = dataTypeBoxedDeserializerVar dtype (dataConCon dcon_type)
      let ser_exp = varAppE' ser ty_args info_params
      let des_exp = varAppE' des ty_args info_params
      let rep = BoxInfo (uintL ix) ser_exp des_exp
      return $ packTypeObject ty rep

    -- Type object constructors 
    -- with no value parameters are marked "inline_never".
    -- These objects may be recursive, and the simplifier doesn't terminate
    -- correctly for this form of recursion. 
    -- Besides, they're not very useful to inline because we don't
    -- deconstruct them very often.
    add_attributes def
      | FunEnt (FunM f) <- definiens def, null $ funParams f =
          modifyDefAnnotation (\d -> d {defAnnInlineRequest = InlNever,
                                        defAnnExported = True}) def
      | otherwise =
          modifyDefAnnotation (\d -> d {defAnnExported = True}) def
