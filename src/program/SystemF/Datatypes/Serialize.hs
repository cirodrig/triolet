{-| Serializer and deserializer code generation.

Serializing a boxed reference will, if possible, create a reference to a 
preexisting object so as to avoid creating duplicate objects.
The reference may be to a global variable or a previously serialized object 
in the same buffer.  Previously serialized objects are given by their index.
Globals are given by their section and offset from the beginning of the
section.

Unboxed objects that do not contain pointers are serialized in their
native representation so that they can be block-copied to and from a buffer.

To keep the representations correct, we do conversions on values of primitive
types as they are moved in and out of local varibables.
-}

{-# OPTIONS_GHC -auto-all #-}
module SystemF.Datatypes.Serialize
       (createAllSerializers, getAllSerializers)
where

import Prelude hiding(catch)

import Control.Exception
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Writer
import qualified Data.IntMap as IntMap
import Data.List
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import Common.MonadLogic
import Common.Supply
import LowLevel.Build
import LowLevel.CodeTypes
import LowLevel.Print
import LowLevel.Records
import qualified LowLevel.Builtins as L
import qualified LowLevel.Syntax as L
import SystemF.Datatypes.DynamicTypeInfo
import SystemF.Datatypes.Structure
import SystemF.Datatypes.Util
import SystemF.Datatypes.Layout
import SystemF.Datatypes.Size
import Type.Type
import Type.Environment
import Type.Eval

data ValInfo =
  ValInfo
  { val_info_size :: !SizeAlign
  }

-- | These are the useful fields of a @Repr@ type
data BareInfo =
  BareInfo
  { bare_info_size :: !SizeAlign
  , bare_info_serialize :: !L.Val
  , bare_info_deserialize :: !L.Val
  }

unpackReprVal :: L.Val -> GenM ValInfo
unpackReprVal ptr = do
  -- Compute layout of a 'ReprVal a'; the type 'a' is unimportant
  let repr_type = valInfoT `AppT` intT
  DataLayout adt <-
    computeLayout emptyTypeInfo BoxK =<< computeStructure repr_type
  mem_adt <- memoryLayout adt

  -- Read its contents
  let pack_fields (Just _) [size] = do
        size' <- unpackSizeAlign size
        return $ ValInfo size'

  memoryElimAtConstructor mem_adt 0 pack_fields ptr

unpackRepr :: L.Val -> GenM BareInfo
unpackRepr ptr = do
  -- Compute layout of a 'Repr a'; the type 'a' is unimportant
  let repr_type = bareInfoT `AppT` (storedT `AppT` intT)
  DataLayout adt <-
    computeLayout emptyTypeInfo BoxK =<< computeStructure repr_type
  mem_adt <- memoryLayout adt

  -- Read its contents
  let pack_fields (Just _) [size, _, ser, des] = do
        size' <- unpackSizeAlign size
        return $ BareInfo size' ser des

  memoryElimAtConstructor mem_adt 0 pack_fields ptr

unpackFIInt :: L.Val -> GenM L.Val
unpackFIInt x = do
  [y] <- unpackRecord2 finIndexedIntRecord x
  return y

-- | Dynamic type information used for serialization
--   consists of unpacked fields of info objects
type SerDynTypeInfo = DynTypeInfo ValInfo BareInfo L.Val

-- | Given run-time type info, construct a 'SerDynTypeInfo'
setupSerializationInfo :: DataType -> [Type] -> [L.Val]
                       -> GenM SerDynTypeInfo
setupSerializationInfo dtype ty_args size_params = do
  sp_types <- instantiateSizeParams dtype ty_args
  when (length sp_types /= length size_params) $
    internalError "setupDynTypeInfo: Wrong number of size parameters"

  foldM insert emptyTypeInfo $ zip sp_types size_params
  where
    insert (!type_info) (KindedType k t, e) = 
      case k
      of ValK      -> do x <- unpackReprVal e
                         return $ insertValTypeInfo t x type_info
         BareK     -> do x <- unpackRepr e
                         return $ insertBareTypeInfo t x type_info
         IntIndexK -> do x <- unpackFIInt e
                         return $ insertIntTypeInfo t e type_info

-- | The type of @Store@ after lowering
storeType = PrimType UnitType

storeValue = L.LitV L.UnitL

-- | The type of a readable buffer
readBufferType = PrimType CursorType

-- | The type returned from reading a readable buffer
readResultRecord t =
  constStaticRecord [PrimField CursorType, valueToFieldType t]

readResultType t = RecordType $ readResultRecord t

-- | The result of deserializing something is a value or initializer and
--   a new buffer reference
data DesResult = DesResult {desBuffer, desValue :: L.Val}

unpackDesResult :: ValueType -> L.Val -> GenM DesResult
unpackDesResult ty x = do [b, v] <- unpackRecord2 (readResultRecord ty) x
                          return $ DesResult b v

packDesResult :: DesResult -> GenM L.Val
packDesResult (DesResult buffer val) =
  packRecord (readResultRecord $ L.valType val) [buffer, val]

-- | A pair of a serializer and deserializer for a particular type.
data SerDes =
  SerDes
  { -- | Given a value and a write-buffer reference, serialize the value
    serialize   :: L.Val -> L.Val -> GenM ()

    -- | Given a buffer-info reference and a read-buffer reference, deserialize a value
  , deserialize :: L.Val -> L.Val -> GenM DesResult
  }

-- | Create a serializer and deserializer from a pair of functions
fromFunctions :: ValueType -> L.Val -> L.Val -> SerDes
fromFunctions deserialized_type ser des =
  SerDes (callSerializerFun ser) (callDeserializerFun deserialized_type des)

-- | Call a function to serialize a value
callSerializerFun :: L.Val -> L.Val -> L.Val -> GenM ()
callSerializerFun s value buffer =
  void $ emitAtom1 storeType $ L.closureCallA s [value, buffer, storeValue]

callDeserializerFun :: ValueType -> L.Val -> L.Val -> L.Val -> GenM DesResult
callDeserializerFun value_type s des_info buffer = do
  let result_type = readResultType value_type
  x <- emitAtom1 result_type $ L.closureCallA s [des_info, buffer]
  unpackDesResult value_type x

boxedFieldSerializer =
  fromFunctions (PrimType OwnedType)
  (L.VarV $ L.llBuiltin L.the_fun_putBoxedObject)
  (L.VarV $ L.llBuiltin L.the_fun_getBoxedObject)

unboxedLayoutSerDes :: SerDynTypeInfo -> BaseKind -> Type -> Layout
                    -> GenM SerDes
unboxedLayoutSerDes type_info ValK ty layout =
  case layout
  of PrimLayout pt  -> primTypeSerDes pt
     DataLayout adt -> algLayoutSerDes type_info ValK ty adt

unboxedLayoutSerDes type_info BareK ty layout = do
  -- First, look up the type info
  m_dyn_info <- lookupBareTypeInfo type_info ty
  case m_dyn_info of
    Just (BareInfo sa ser des) -> do
      -- TODO: If pointerless, use block copy
      return $ fromFunctions (PrimType OwnedType) ser des
    Nothing ->
      -- If not available, consult the layout
      case layout
      of DataLayout adt -> algLayoutSerDes type_info BareK ty adt

-- | Create a serializer for a primitive type
primTypeSerDes :: PrimType -> GenM SerDes
primTypeSerDes pt
  | pt == trioletIntType   = builtin L.the_fun_putInt L.the_fun_getInt
  | pt == trioletUintType  = builtin L.the_fun_putUint L.the_fun_getUint
  | pt == trioletFloatType = builtin L.the_fun_putFloat L.the_fun_getFloat
  | pt == UnitType         = builtin L.the_fun_putUnit L.the_fun_getUnit
  | pt == CursorType       = builtin L.the_fun_putCursor L.the_fun_getCursor
  | otherwise = internalError $ "primTypeSerDes: " ++ show pt
  where
    builtin s d =
      return $ fromFunctions (PrimType pt) (L.VarV $ L.llBuiltin s) (L.VarV $ L.llBuiltin d)

-- | Create a serializer for an algebraic unboxed type
algLayoutSerDes :: SerDynTypeInfo
                -> BaseKind
                -> Type
                -> AlgData LayoutField
                -> GenM SerDes
algLayoutSerDes type_info kind ty layout = do
  -- Compute types of the fields
  structure_alts <- do
    s <- computeStructure ty
    return $! case s
              of DataStruct (Data _ structure_alts) -> structure_alts
                 StoredStruct value_ty ->
                   [Alternative (VarDeCon stored_conV [value_ty] [])
                    [(ValK, value_ty)]]
                 _ -> traceShow (pprType ty) $ internalError "algLayoutSerDes"

  -- Create serializers for all fields
  field_ss <- sequence
              [ fieldSerializers type_info alt (algDisjunctFields dj)  
              | (alt, dj) <- zip structure_alts $ disjuncts layout]

  let !(make_ser, make_des) =
        case kind of
          ValK  -> (algValueLayoutSerializer, algValueLayoutDeserializer)
          BareK -> (algBareLayoutSerializer, algBareLayoutDeserializer)

  return $ SerDes (make_ser field_ss layout) (make_des field_ss layout)

algValueLayoutSerializer :: [[SerDes]] -> AlgData LayoutField
                         -> L.Val -> L.Val -> GenM ()
algValueLayoutSerializer field_ss adt scrutinee buffer = do
  valueElim alg_value_type storeType (dj_handler buffer) scrutinee
  return ()
  where
    alg_value_type = valueLayout adt
    value_type = algDataValueType True adt

    dj_handler buffer con_index Nothing field_values = do
      -- If a sum type, write the tag
      serializeUnboxedTag adt buffer con_index

      -- Write the fields
      serializeFields buffer $ zip (field_ss !! con_index) field_values
      return storeValue

algBareLayoutSerializer field_ss adt scrutinee buffer = do
  mem_adt <- memoryLayout adt
  memoryElim mem_adt storeType (dj_handler buffer) scrutinee
  return ()
  where
    dj_handler buffer con_index Nothing field_values = do
      -- If a sum type, write the tag
      serializeUnboxedTag adt buffer con_index

      -- Write the fields
      serializeFields buffer $ zip (field_ss !! con_index) field_values
      return storeValue

algValueLayoutDeserializer :: [[SerDes]] -> AlgData LayoutField
                           -> L.Val -> L.Val -> GenM DesResult
algValueLayoutDeserializer field_ss adt des_info buffer =
  case n_constructors of
    -- No tag
    1 -> do x <- deserialize_disjunct buffer 0
            unpackDesResult value_type x

    -- Read the tag, then deserialize one of the disjuncts
    _ -> do DesResult buffer' tag <- deserializeUnboxedTag adt des_info buffer
            x <- tagDispatch2 (PrimType tag_type) n_constructors tag [result_type] $
                 deserialize_disjunct buffer'
            unpackDesResult value_type x
  where
    alg_value_type = valueLayout adt
    value_type = algDataValueType True adt
    result_type = readResultType value_type

    n_constructors = algDataNumConstructors adt
    Just tag_type = unboxedMemTagType $ algDataNumConstructors adt

    deserialize_disjunct buffer con_index = do
      -- Read fields      
      let field_types = map (fieldValueType' False) $
                        algDisjunctFields $ disjunct con_index Nothing adt
          field_serializers = field_ss !! con_index
      (buffer', field_values) <-
        deserializeFields des_info buffer (zip field_serializers field_types)

      -- Construct value
      new_value <- valueIntro alg_value_type con_index field_values

      -- Pack into a record with the new buffer
      packDesResult $ DesResult buffer' new_value
      
algBareLayoutDeserializer :: [[SerDes]] -> AlgData LayoutField
                          -> L.Val -> L.Val -> GenM DesResult
algBareLayoutDeserializer field_ss adt des_info buffer = do
  mem_adt <- memoryLayout adt
  case n_constructors of
    -- No tag
    1 -> do x <- deserialize_disjunct mem_adt buffer 0
            unpackDesResult (PrimType OwnedType) x

    -- Read the tag, then deserialize one of the disjuncts
    _ -> do DesResult buffer' tag <- deserializeUnboxedTag adt des_info buffer
            x <- tagDispatch2 (PrimType tag_type) n_constructors tag [result_type] $
                 deserialize_disjunct mem_adt buffer'
            unpackDesResult (PrimType OwnedType) x
  where
    -- Result includes an initializer function
    result_type = readResultType (PrimType OwnedType)

    n_constructors = algDataNumConstructors adt
    Just tag_type = unboxedMemTagType $ algDataNumConstructors adt

    deserialize_disjunct mem_adt buffer con_index = do
      -- Read fields      
      let field_types = map (fieldValueType' False) $
                        algDisjunctFields $ disjunct con_index Nothing adt
          field_serializers = field_ss !! con_index
      (buffer', field_values) <-
        deserializeFields des_info buffer (zip field_serializers field_types)

      -- Construct value
      new_value <- memoryIntro mem_adt con_index Nothing field_values

      -- Pack into a record with the new buffer
      packDesResult $ DesResult buffer' new_value

-- | A pair of a serializer and deserializer for a boxed type.
--
--   The desserializer takes an extra parameter, the type object.
data BoxedSerDes =
  BoxedSerDes
  { -- | Given a value and a write-buffer reference, serialize the value
    boxedSerialize   :: L.Val -> L.Val -> GenM ()

    -- | Given a read-buffer reference, deserialize a value.
    --
    --   Parameters are the type object (boxed),
    --   the deserialization info (boxed),
    --   and the buffer (cursor).
  , boxedDeserialize :: L.Val -> L.Val -> L.Val -> GenM DesResult
  }

-- | Create a serializer for a disjunct of an algebraic boxed type.
--   Serializers and deserializers take care of the boxed object's fields.
--   The type object gets moved before the serializer or deserializer is
--   called.
--
--   The serializer serializes the fields.
--   The deserializer takes the type object as a parameter, deserializes
--   the fields, and constructs an object.
boxedLayoutSerDes :: SerDynTypeInfo -> AlgData LayoutField -> Type -> Int
                  -> GenM BoxedSerDes
boxedLayoutSerDes type_info adt ty con_index 
  | algDataBoxing adt /= IsBoxed = internalError "boxedLayoutSerDes: Not boxed"
  | otherwise = do
    -- Compute types of the fields
    DataStruct (Data _ structure_alts) <- computeStructure ty

    -- Create serializers for all fields
    field_s <- fieldSerializers type_info (structure_alts !! con_index) 
               (disjunctFields con_index adt)

    return $ BoxedSerDes (boxedLayoutSerializer field_s adt con_index)
                         (boxedLayoutDeserializer field_s adt con_index)

boxedLayoutSerializer field_s adt con_index scrutinee buffer = do
  mem_adt <- memoryLayout adt
  memoryElimAtConstructor mem_adt con_index
    (serialize_fields buffer) scrutinee
  where
    serialize_fields buffer (Just _) fields = do
      -- The type object has been serialized already
      serializeFields buffer $ zip field_s fields

    serialize_fields _ Nothing _ =
      -- Boxed types always contain a type object
      internalError "boxedLayoutSerializer"

-- | A boxed object deserializer takes a the object's type object 
--   as an extra type parameter.  The type object has already been
--   deserialized.
boxedLayoutDeserializer field_s adt con_index tyob des_info buffer = do
  mem_adt <- memoryLayout adt

  let dj = disjunct con_index (Just tyob) adt
  let field_types = map fieldInitializerType $ algDisjunctFields dj

  let read_fields = do
        (buffer', field_values) <-
          deserializeFields des_info buffer $ zip field_s field_types
        return (field_values, buffer')

  -- Construct the new object and read its fields
  (new_object, buffer') <-
    memoryIntroDeserialized mem_adt con_index des_info (Just tyob) read_fields

  -- Return the results
  return $ DesResult buffer' new_object
  

-- | Serialize a sequence of fields
serializeFields :: L.Val -> [(SerDes, L.Val)] -> GenM ()
serializeFields buffer fields = mapM_ serialize_field fields
  where
    serialize_field (serdes, value) = serialize serdes value buffer

-- | Deserialize a sequence of fields.  Return the new buffer and the field
--   values or initializers.
deserializeFields :: L.Val -> L.Val -> [(SerDes, ValueType)]
                  -> GenM (L.Val, [L.Val])
deserializeFields des_info buffer fields = go id buffer fields
  where
    go hd buf ((s, ty):fs) = do
      -- Deserialize one field
      DesResult buf' y <- deserialize s des_info buf
      go (hd . (y:)) buf' fs

    go hd buf [] = return (buf, hd [])

-- | Write an unboxed data type's tag to the buffer
serializeUnboxedTag :: AlgData a -> L.Val -> Int -> GenM ()
serializeUnboxedTag adt buffer con_index =
  case unboxedMemTagType $ algDataNumConstructors adt
  of Nothing                      -> return ()       -- There is no tag
     Just (IntType Unsigned S8)   -> use (L.llBuiltin L.the_fun_putUintAsUint8)
     Just (IntType Unsigned S16)  -> use (L.llBuiltin L.the_fun_putUintAsUint16)
     Just t | t == nativeWordType -> use (L.llBuiltin L.the_fun_putUint)
  where
    use serialize_function =
      void $ emitAtom1 storeType $ L.closureCallA (L.VarV serialize_function)
      [nativeWordV con_index, buffer, storeValue]

deserializeUnboxedTag :: AlgData a -> L.Val -> L.Val -> GenM DesResult
deserializeUnboxedTag adt des_info buffer =
  case unboxedMemTagType $ algDataNumConstructors adt
  of Nothing -> return $ DesResult buffer invalid
     Just pt ->
       case pt 
       of IntType Unsigned S8     -> use pt (L.llBuiltin L.the_fun_getUint8AsUint)
          IntType Unsigned S16    -> use pt (L.llBuiltin L.the_fun_getUint16AsUint)
          t | t == nativeWordType -> use pt (L.llBuiltin L.the_fun_getUint)
  where
    invalid = internalError "deserializeUnboxedTag: No tag"
    use tag_type deserialize_function = do
      x <- emitAtom1 (readResultType $ PrimType nativeWordType) $
           L.closureCallA (L.VarV deserialize_function) [des_info, buffer]
      unpackDesResult (PrimType tag_type) x

fieldSerializers :: SerDynTypeInfo -> Alternative -> [LayoutField]
                 -> GenM [SerDes]
fieldSerializers type_info (Alternative decon field_kind_types) field_layouts =
  assumeBinders (deConExTypes decon) $ do
    let field_types = map snd field_kind_types
    zipWithM (fieldSerializer type_info) field_types field_layouts
                      
fieldSerializer _         _  (BoxK,  _) = return boxedFieldSerializer
fieldSerializer type_info ty (ValK,  l) = unboxedLayoutSerDes type_info ValK ty l
fieldSerializer type_info ty (BareK, l) = unboxedLayoutSerDes type_info BareK ty l

{-
valueLayoutSerializer (DataLayout adt) = do
  
  -- Create serializers for all fields
  field_serializers <- mapM fieldSerializers alts

  -- Get the type constructor information
  Just (dtype_con, _) <- deconVarAppType ty
  Just data_type <- lookupDataType dtype_con

  -- Get the data constructor index for each alternative
  let constructors = [con | Alternative (VarDeCon con _ _) _ <- alts] 
      constructor_indices = map (dataTypeConIndex data_type) constructors

  -- Get the data type's layout
  
  -- Create a serializer for this type
  serializer <- mapM algValueSerializer $ zip3 constructors constructor_indices 

    lamE $ mkFun [] (\ [] -> return ([ty, opaqueRefT, storeT], storeT))
    (\ [] [value, buffer, state] ->
        mkCase ty (varE' value) []
        [ (con, dj_deconstructor con_index buffer state (map fst serializers))
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
    -- Type of the tag value for an object stored in memory
    tag_type :: Maybe PrimType
    tag_type = unboxedMemTagType (length alts)

    -- Return type of deserializer
    deserialized_type =
      UTupleT [ValK, ValK] `typeApp` [readBufferT, ty]

    get_constructor_index (Alternative (VarDeCon con _ _) _) = do
      Just dcon_type <- lookupDataCon con
      return $ dataConIndex dcon_type

    -- Write an object by writing its constructor index, followed by its fields
    dj_deconstructor con_index buffer state serializers _ field_values =
      let put = mconcat (putConIndex tag_type con_index :
                         zipWith putField serializers field_values)
      in createPutCode put buffer state

    -- Read a constructor by reading its fields and constructing the object
    -- TODO: What about existential types?
    dj_constructor (Alternative (VarDeCon con ty_args []) _) serializers = do
      xs <- sequence serializers
      return $ valConE' (VarCon con ty_args []) xs

algValueSerializer 

-- | Create a serializer for each field of the alternative
fieldSerializers :: Alternative -> [SerDes]
fieldSerializers (Alternative decon field_types) =
  assumeBinders (deConExTypes decon) $ mapM fieldSerializer field_types
-}

-- | Create a parameteric global function definition.
--
--   Although a low-level function is being generated, we pretend that 
--   the function takes type parameters and we add those type parameters 
--   to the type environment so that data types can be lowered.
parametricDefinition :: L.Var       -- ^ Function name
                     -> [Binder]    -- ^ Type parameters
                     -> [ValueType] -- ^ Run-time size information
                     -> [ValueType] -- ^ Other parameters
                     -> [ValueType] -- ^ Return types
                     -> ([L.Var] -> [L.Var] -> GenM [L.Val])
                     -> SizeComputing L.Fun
parametricDefinition fname typarams size_types other_types return_types mk_body = do
  size_param_vars <- mapM L.newAnonymousVar size_types
  other_param_vars <- mapM L.newAnonymousVar other_types

  genClosureFun fname (size_param_vars ++ other_param_vars) return_types $ do
    retvals <- assumeBinders typarams $
               mk_body size_param_vars other_param_vars
    return $ L.ReturnE $ L.ValA retvals

-- | Get the lowered types of the run-time type information to pass 
--   to serializer functions.
--   We pass run-time type objects, so these appear as owned pointers.
infoParameterTypes :: DataType -> [ValueType]
infoParameterTypes data_type =
  map sp_type $ layoutSizeParamTypes $ dataTypeLayout' data_type
  where
    sp_type (KindedType ValK _)      = PrimType OwnedType
    sp_type (KindedType BareK _)     = PrimType OwnedType
    sp_type (KindedType IntIndexK _) = RecordType finIndexedIntRecord

-- | Given a piece of run-time type info, extract the run-time size info.
--   The kind of type described by the run-time type info is passed as a
--   parameter.
infoToSizeParameter :: BaseKind -> L.Val -> GenM L.Val
infoToSizeParameter ValK x = do
  ValInfo sa <- unpackReprVal x
  packSizeAlign sa

infoToSizeParameter BareK x = do
  BareInfo sa _ _ <- unpackRepr x
  packSizeAlign sa

infoToSizeParameters :: DataType -> [L.Val] -> GenM [L.Val]
infoToSizeParameters data_type xs =
  let kinds = map getBaseKind $ layoutSizeParamTypes $ dataTypeLayout' data_type
  in zipWithM infoToSizeParameter kinds xs

-- | Create all serializer functions for a given data type.
--   Return a list of serializer functions and their low-level definitions.
createSerializers :: [(Var, (L.Var, L.Var))] -> DataType
                  -> SizeComputing [(Var, L.GlobalDef)]
createSerializers serializer_overrides data_type = 
  case dataTypeKind data_type
  of ValK -> createValTypeSerializers data_type
     BoxK -> createBoxedTypeSerializers data_type
     BareK
       | dataTypeCon data_type == storedV -> 
           return []            -- No serializers for 'Stored'
       | otherwise ->
           createBareTypeSerializers serializer_overrides data_type

-- The below functions 'createBoxedTypeSerializers', etc. are very similar
-- to one another, and they probably could be refactored to share a common
-- implementation.

newSerializerVar v =
  let Just lab = varName v
  in L.newExternalVar lab (PrimType OwnedType)

createBoxedTypeSerializers data_type =
  let params = dataTypeParams data_type
      param_types = map (VarT . binderVar) params
      ty = dataTypeCon data_type `varApp` param_types
      info_types = infoParameterTypes data_type
      constructors = zip (dataTypeDataConstructors data_type) [0..]
  in
   -- For each data constructor
   liftM concat $ forM constructors $ \(dcon_var, dcon_index) -> do
     let serializer = dataTypeBoxedSerializerVar data_type dcon_var
         deserializer = dataTypeBoxedDeserializerVar data_type dcon_var

     -- DEBUG
     liftIO $ putStrLn $ "Boxed type serializer " ++ show dcon_var

     l_serializer <- newSerializerVar serializer
     l_deserializer <- newSerializerVar deserializer

     -- Create serializer code
     -- Due to how the code is set up, the serializer and deserializer are 
     -- generated redundantly, then the unused code is optimized away.
     serializer_fun <-
       parametricDefinition l_serializer (dataTypeParams data_type)
       info_types [PrimType OwnedType, PrimType OwnedType, storeType]
       [storeType] $ \ infos [obj, buffer, _] -> do
         -- Compute layout information
         sps <- infoToSizeParameters data_type (map L.VarV infos)
         layout_dyn_info <- setupDynTypeInfo data_type param_types sps
         s <- computeStructure ty
         l@(DataLayout adt) <- computeLayout layout_dyn_info BoxK s

         -- Set up dynamic serializer info
         dyn_info <- setupSerializationInfo data_type param_types (map L.VarV infos)

         -- Serialize
         serdes <- boxedLayoutSerDes dyn_info adt ty dcon_index
         boxedSerialize serdes (L.VarV obj) (L.VarV buffer)
         return [storeValue]

     deserializer_fun <-
       parametricDefinition l_deserializer (dataTypeParams data_type)
       info_types [PrimType OwnedType, PrimType OwnedType, PrimType CursorType]
       [readResultType (PrimType OwnedType)] $ \ infos [type_ob, des_info, buffer] -> do
         -- Compute layout information
         sps <- infoToSizeParameters data_type (map L.VarV infos)
         layout_dyn_info <- setupDynTypeInfo data_type param_types sps
         s <- computeStructure ty
         l@(DataLayout adt) <- computeLayout layout_dyn_info BoxK s

         -- Set up dynamic serializer info
         dyn_info <- setupSerializationInfo data_type param_types (map L.VarV infos)

         -- Deserialize
         serdes <- boxedLayoutSerDes dyn_info adt ty dcon_index
         result <- boxedDeserialize serdes (L.VarV type_ob) (L.VarV des_info) (L.VarV buffer)
         x <- packDesResult result
         return [x]

     return [ (serializer, L.GlobalFunDef $ L.Def l_serializer serializer_fun)
            , (deserializer, L.GlobalFunDef $ L.Def l_deserializer deserializer_fun)]

createBareTypeSerializers serializer_overrides data_type = do
  let params = dataTypeParams data_type
      param_types = map (VarT . binderVar) params
      ty = dataTypeCon data_type `varApp` param_types
      info_types = infoParameterTypes data_type
      serializer = dataTypeUnboxedSerializerVar data_type
      deserializer = dataTypeUnboxedDeserializerVar data_type

  -- DEBUG
  liftIO $ putStrLn $ "Bare type serializer " ++ show (dataTypeCon data_type)

  l_serializer <- newSerializerVar serializer
  l_deserializer <- newSerializerVar deserializer

  -- Create serializer code
  -- Due to how the code is set up, the serializer and deserializer are 
  -- generated redundantly, then the unused code is optimized away.
  serializer_fun <-
    parametricDefinition l_serializer (dataTypeParams data_type)
    info_types [PrimType CursorType, PrimType OwnedType, storeType]
    [storeType] $ \ infos [obj, buffer, dummy] ->
      case lookup (dataTypeCon data_type) serializer_overrides
      of Just (s, _) ->
           -- Call the override serializer function
           emitAtom [storeType] $
           L.closureCallA (L.VarV s)
           (map L.VarV $ infos ++ [obj, buffer, dummy])

         Nothing -> do
           -- Compute layout information
           sps <- infoToSizeParameters data_type (map L.VarV infos)
           layout_dyn_info <- setupDynTypeInfo data_type param_types sps
           s <- computeStructure ty
           l <- computeLayout layout_dyn_info BareK s

           -- Set up dynamic serializer info
           dyn_info <- setupSerializationInfo data_type param_types (map L.VarV infos)

           -- Serialize
           serdes <- unboxedLayoutSerDes dyn_info BareK ty l
           serialize serdes (L.VarV obj) (L.VarV buffer)
           return [storeValue]

  deserializer_fun <-
    parametricDefinition l_deserializer (dataTypeParams data_type)
    info_types [PrimType OwnedType, PrimType CursorType]
    [readResultType (PrimType OwnedType)] $ \ infos [des_info, buffer] ->
      case lookup (dataTypeCon data_type) serializer_overrides
      of Just (_, d) ->
           -- Call the override deserializer function
           emitAtom [readResultType (PrimType OwnedType)] $
           L.closureCallA (L.VarV d) (map L.VarV $ infos ++ [buffer])
         Nothing -> do
           -- Compute layout information
           sps <- infoToSizeParameters data_type (map L.VarV infos)
           layout_dyn_info <- setupDynTypeInfo data_type param_types sps
           s <- computeStructure ty
           l <- computeLayout layout_dyn_info BareK s

           -- Set up dynamic serializer info
           dyn_info <- setupSerializationInfo data_type param_types (map L.VarV infos)

           -- Deserialize
           serdes <- unboxedLayoutSerDes dyn_info BareK ty l
           result <- deserialize serdes (L.VarV des_info) (L.VarV buffer)
           x <- packDesResult result
           return [x]

  return [ (serializer, L.GlobalFunDef $ L.Def l_serializer serializer_fun)
         , (deserializer, L.GlobalFunDef $ L.Def l_deserializer deserializer_fun)]

-- | Create serializers for a type of kind @val@.
--   The serializers read or write objects of type @Stored t@.
createValTypeSerializers data_type = do
  let params = dataTypeParams data_type
      param_types = map (VarT . binderVar) params
      ty = dataTypeCon data_type `varApp` param_types
      serializer = dataTypeUnboxedSerializerVar data_type
      deserializer = dataTypeUnboxedDeserializerVar data_type

  -- DEBUG
  liftIO $ putStrLn $ "Value type serializer " ++ show (dataTypeCon data_type)

  -- Value types should not need any dynamic info
  unless (null $ infoParameterTypes data_type) $
    internalError "createValSerializer: Value's layout depends on parameters"

  -- A type is not serializable if it has type parameters that must be
  -- known statically.
  -- We generate stub functions for this type; in truth, we should
  -- really do something more visible to users.
  let serializable = null $ layoutStaticTypes $ dataTypeLayout' data_type

  l_serializer <- newSerializerVar serializer
  l_deserializer <- newSerializerVar deserializer

  -- Create serializer code
  -- Due to how the code is set up, the serializer and deserializer are 
  -- generated redundantly, then the unused code is optimized away.
  serializer_fun <-
    parametricDefinition l_serializer (dataTypeParams data_type)
    [] [PrimType CursorType, PrimType OwnedType, storeType]
    [storeType] $ \ [] [obj, buffer, _] ->
      if serializable
      then do 
        -- Compute layout information
        s <- computeStructure (storedT `AppT` ty)
        l <- computeLayout emptyTypeInfo BareK s

        -- Serialize
        serdes <- unboxedLayoutSerDes emptyTypeInfo BareK (storedT `AppT` ty) l
        serialize serdes (L.VarV obj) (L.VarV buffer)
        return [storeValue]
      else do
        -- Can't serialize this type
        emitThrow (nativeIntV (-1))
        return [storeValue]

  deserializer_fun <-
    parametricDefinition l_deserializer (dataTypeParams data_type)
    [] [PrimType OwnedType, PrimType CursorType]
    [readResultType (PrimType OwnedType)] $ \ [] [des_info, buffer] ->
      if serializable
      then do 
        -- Compute layout information
        s <- computeStructure (storedT `AppT` ty)
        l <- computeLayout emptyTypeInfo BareK s

        -- Deserialize
        serdes <- unboxedLayoutSerDes emptyTypeInfo BareK (storedT `AppT` ty) l
        result <- deserialize serdes (L.VarV des_info) (L.VarV buffer)
        x <- packDesResult result
        return [x]
      else do
        -- Can't serialize this type
        emitThrow (nativeIntV (-1))
        return [undefined]

  return [ (serializer, L.GlobalFunDef $ L.Def l_serializer serializer_fun)
         , (deserializer, L.GlobalFunDef $ L.Def l_deserializer deserializer_fun)]

createAllSerializers :: IdentSupply L.Var -> IdentSupply Var -> TypeEnv
                     -> [(Var, (L.Var, L.Var))]
                     -> IO [(Var, L.GlobalDef)]
createAllSerializers ll_ident_supply ident_supply tenv serializer_overrides =
  runTypeEvalM (runSC ll_ident_supply worker) ident_supply tenv
  where
    worker = do
      dtypes <- liftTypeEvalM get_algebraic_data_types
      defs <- mapM (createSerializers serializer_overrides) dtypes
      return $ concat defs

    get_algebraic_data_types :: UnboxedTypeEvalM [DataType]
    get_algebraic_data_types = do
      i_type_env <- freezeTypeEnv
      return $ filter dataTypeIsAlgebraic $ IntMap.elems $
        getAllDataTypeConstructors i_type_env

-- | Get a list of all serializers and their types
getAllSerializers :: IdentSupply Var -> TypeEnv -> IO [(Var, Type)]
getAllSerializers ident_supply tenv =
  runTypeEvalM worker ident_supply tenv
  where
    worker = do
      dtypes <- get_algebraic_data_types
      return $ concat $ map serializers dtypes  

    serializers dtype
      | not $ dataTypeIsAlgebraic dtype = []
      | dataTypeCon dtype == storedV = []
      | dataTypeKind dtype == ValK || dataTypeKind dtype == BareK =
          [(dataTypeUnboxedSerializerVar dtype, serializerType dtype),
           (dataTypeUnboxedDeserializerVar dtype, deserializerType dtype)]
      | dataTypeKind dtype == BoxK =
          concat [[(dataTypeBoxedSerializerVar dtype c, serializerType dtype),
                   (dataTypeBoxedDeserializerVar dtype c, deserializerType dtype)]
                 | c <- dataTypeDataConstructors dtype]

    get_algebraic_data_types :: UnboxedTypeEvalM [DataType]
    get_algebraic_data_types = do
      i_type_env <- freezeTypeEnv
      return $ filter dataTypeIsAlgebraic $ IntMap.elems $
        getAllDataTypeConstructors i_type_env
