{-| Constructor and deconstructor code generation.
-}

{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleContexts #-}
module SystemF.Datatypes.Size where

import Prelude hiding(catch)

import Control.Exception
import Control.Monad
import Control.Monad.Reader
import qualified Data.IntMap as IntMap
import Data.List
import Data.Maybe
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import Common.Supply
import Builtins.Builtins
import SystemF.Datatypes.DynamicTypeInfo
import SystemF.Datatypes.Structure
import SystemF.Datatypes.Util
import SystemF.Datatypes.Layout
import Type.Type
import Type.Environment
import LowLevel.CodeTypes
import LowLevel.Build
import qualified LowLevel.Syntax as L
import qualified LowLevel.Print as L



-- | Run the memory layout algorithm on data types and print results
testMemoryLayout :: IdentSupply Var -> IdentSupply L.Var -> TypeEnv
                 -> IO ()
testMemoryLayout var_supply ll_var_supply type_env =
  mapM_ test_one (IntMap.elems $ getAllDataTypeConstructors type_env)
  where
    test_one dcon
      | dataTypeIsAlgebraic dcon && not (null $ dataTypeDataConstructors dcon) =
          runTypeEvalM (do_test dcon) var_supply type_env `catch` \exc ->
          print (exc :: ErrorCall)
      | otherwise = return ()

    do_test dcon = do
      let ty = dataTypeCon dcon `varApp` map (VarT . binderVar) (dataTypeParams dcon)
          kind = dataTypeKind dcon
          n_data_cons = length $ dataTypeDataConstructors dcon
      liftIO $ print $ dataTypeCon dcon
      layout <- computeStructure ty
      runSC ll_var_supply $ do
        testPhysicalLayout kind layout
        testDeconstructorCode dcon
        mapM_ (testConstructorCode dcon) [0..n_data_cons-1]

testPhysicalLayout kind layout = do
  stm <- execBuild return_type $ do
    pl <- computeLayout emptyTypeInfo kind layout
    SizeAlign s a <- memorySize pl
    return $ L.ReturnE $ L.ValA [s,a]
  liftIO $ print $ L.pprStm stm
  where
    return_type = [PrimType trioletIntType, PrimType trioletIntType]

-- | Test the new code generation.  Discard the result.
--
--   This testing code cuts corners when setting up the dynamic layout
--   environment because it doesn't actually check which types are needed.
--   Consequently, it can fail to set up the environment correctly.
testDeconstructorCode :: DataType -> SizeComputing ()
testDeconstructorCode dcon =
  withDummyLayoutInfo dcon $ \param_binders -> do
    let params = map binderVar param_binders

    -- Create dummy layout information for each parameter
    let li = dummyLayoutInfo param_binders

    -- Generate deconstructor code
    let rtype = [PrimType nativeIntType]
        codegen _ _ = return [nativeIntV 9]
    code <- execBuild rtype $ do
      scrutinee <- L.newAnonymousVar (PrimType nativeIntType)
      dc <- genCase dcon params li rtype (L.VarV scrutinee) codegen
      return $ L.ReturnE $ L.ValA dc
    liftIO $ print $ L.pprStm code

testConstructorCode :: DataType -> Int -> SizeComputing ()
testConstructorCode dcon con_index = do
  withDummyLayoutInfo dcon $ \param_binders -> do
    let params = map binderVar param_binders

    -- Create dummy layout information for each parameter
    let li = dummyLayoutInfo param_binders
    
    -- Generate constructor code
    let rtype = [PrimType nativeIntType]
    code <- execBuild rtype $ do
      dc <- genConstructor dcon params li con_index
      return $ L.ReturnE $ L.ValA [dc]
    liftIO $ print $ L.pprStm code

-- | Construct type information for a non-arrow-kinded type built from 
--   the given data constructor applied to type parameters. 
--
--   Create dummy layout information for each type parameter of 'dcon'
--   and create type 
withDummyLayoutInfo dcon k = do
  -- Create parameter variables
  params <- mapM (newClonedVar . binderVar) $ dataTypeParams dcon
  let param_kinds = map binderType $ dataTypeParams dcon
  let param_binders = zipWith (:::) params param_kinds
  assumeBinders param_binders $ k param_binders

dummyLayoutInfo xs =
  let infos = map layout_info xs
  in foldr ($) emptyTypeInfo infos
  where
    layout_info (v ::: k) =
      case k
      of VarT kind_var
           | kind_var == valV ->
               insertValTypeInfo (VarT v) (SizeAlign one_val one_val)
           | kind_var == bareV ->
               insertBareTypeInfo (VarT v) (SizeAlign one_val one_val)
           | kind_var == intindexV ->
               insertIntTypeInfo (VarT v) one_val
         _ -> id

    one_val = L.LitV $ nativeIntL 1 

-------------------------------------------------------------------------------

genCase :: DataType             -- ^ Data type to deconstruct
        -> [Var]                -- ^ Type parameters
        -> DynTypeInfo          -- ^ Layout info for each unknown type
        -> [ValueType]          -- ^ Return type of case expression
        -> L.Val                            -- ^ Scrutinee
        -> (Int -> [L.Val] -> GenM [L.Val]) -- ^ Branch code generators
        -> GenM [L.Val]                     -- ^ Case code generator
genCase dtype ty_params v_layouts result_types scrutinee handlers = do
  -- Compute algebraic data type layout
  DataLayout adt <- dataTypeLayout dtype ty_params v_layouts

  -- Handle value and reference types differently 
  case dataTypeKind dtype of
    ValK  -> value_case adt
    BareK -> memory_case adt
    BoxK  -> memory_case adt
  where
    value_case adt =
      valueElim (valueLayout adt) result_types handlers scrutinee

    memory_case adt = do
      mem_adt <- memoryLayout adt
      memoryElim mem_adt result_types handlers scrutinee

-- | Create a constructor function for an algebraic data type
genConstructor :: DataType             -- ^ Data type to deconstruct
               -> [Var]                -- ^ Type parameters
               -> DynTypeInfo          -- ^ Layout info for each unknown type
               -> Int                  -- ^ Constructor index
               -> GenM L.Val           -- ^ Constructor code generator
genConstructor dtype ty_params v_layouts con_index = do
  -- Compute algebraic data type layout
  DataLayout adt <- dataTypeLayout dtype ty_params v_layouts

  -- Handle value and reference types differently 
  case dataTypeKind dtype of
    ValK  -> value_case adt
    BareK -> memory_case adt
    BoxK  -> memory_case adt
  where
    value_case adt =
      valueConstructor (valueLayout adt) con_index

    memory_case adt = do
      mem_adt <- memoryLayout adt
      memoryConstructor mem_adt con_index

dataTypeLayout :: DataType -> [Var] -> DynTypeInfo -> GenM Layout
dataTypeLayout dtype params v_layouts =
  let t = dataTypeCon dtype `varApp` map VarT params
      k = dataTypeKind dtype
  in computeLayout v_layouts k =<< computeStructure t

-- | Get the appropriate pointer type for the given algebraic data type
objectPointerType :: AlgObjectType -> ValueType
objectPointerType adt =
  case algDataBoxing adt
  of IsBoxed  -> PrimType OwnedType
     NotBoxed -> PrimType PointerType

-- | Get the appropriate type for the result of a constructor of the 
--   given algebraic data type.  The result for bare objects is an
--   initializer function's type.
constructedObjectType :: AlgObjectType -> ValueType
constructedObjectType adt =
  -- If boxed, result is a boxed object
  -- If bare, reuslt is an initializer (which is a boxed object)
  PrimType OwnedType

-- | Create a constructor function for a data type.  The constructor function
--   takes the fields as parameters, or a dummy argument if there are no
--   fields.  The function should return an object or initializer.
mkConstructorFunction :: ValueType
                      -> [ValueType]
                      -> ([L.Val] -> GenM L.Val)
                      -> GenM L.Val
mkConstructorFunction adt_type field_types mk_body =
  let param_types = addDummyParameterType field_types

      -- If there's a dummy argument, get rid of it
      get_real_args args = if null field_types then [] else args
  in genLambda param_types [adt_type] (fmap return . mk_body . get_real_args)

-------------------------------------------------------------------------------
-- Type, constructor, and deconstructor code generation for value types

fieldValueType :: LayoutField -> ValueType
fieldValueType (ValK, l) = layoutValueType l
fieldValueType (BoxK, _) = PrimType OwnedType
fieldValueType _         = internalError "fieldValueType: Unexpected kind"

valueLayout :: AlgData LayoutField -> AlgValueType
valueLayout adt = fmap fieldValueType adt

-- | Get the 'ValueType' used to store data with layout 'Layout' in
--   a local variable.
--
--   We have @layoutValueType x == asValueType (valueTypeLayout x)@ for all
--   @x@ on which the RHS is not _|_.
layoutValueType :: Layout -> ValueType
layoutValueType (PrimLayout pt)   = PrimType pt
layoutValueType (BlockLayout _)   = internalError "layoutValueType: \
                                                    \No value type"
layoutValueType (DataLayout adt) = algDataValueType adt

disjunctRecordType :: AlgDisjunct ValueType -> Maybe StaticRecord
disjunctRecordType dj =
  case algDisjunctFields dj
  of [] -> Nothing
     fs -> Just $ constStaticRecord $ map valueToFieldType fs

disjunctType :: AlgDisjunct ValueType -> Maybe ValueType
disjunctType dj = fmap RecordType $ disjunctRecordType dj

disjunctTypes adt = catMaybes $ mapDisjuncts disjunctType adt

productRecordType :: AlgValueType -> StaticRecord
productRecordType adt 
  | algDataNumConstructors adt == 1 =
      case disjunctRecordType $ disjunct 0 adt of Just t -> t
  | otherwise =
      internalError "productRecordType: Not a product type"

productValueType :: AlgValueType -> ValueType
productValueType adt = RecordType $ productRecordType adt

sumRecordType :: AlgValueType -> StaticRecord
sumRecordType adt =
  let Just tag_type = algDataTagType adt
      dj_types = disjunctTypes adt
  in constStaticRecord $ map valueToFieldType (tag_type : dj_types)

sumValueType adt = RecordType $ sumRecordType adt

-- | Get the index of each disjunct in a sum value.
--   
--   If a disjunct has no fields, its index is 'Nothing'.
--   Otherwise its index is the number of previous disjuncts having fields.
disjunctIndices :: AlgValueType -> [Maybe Int]
disjunctIndices adt =
  snd $ mapAccumL assign_index 0 $ mapDisjuncts disjunctType adt
  where
    -- Assign an index to non-empty disjuncts
    assign_index (!next_index) (Just _) = (1 + next_index, Just next_index)
    assign_index next_index    Nothing  = (next_index, Nothing)

-- | Get the 'ValueType' used to store the given unboxed value type  
--   in a local variable.
algDataValueType :: AlgData LayoutField -> ValueType
algDataValueType adt = algDataValueType' $ valueLayout adt

algDataValueType' adt
  | isEnumeration adt               = case algDataTagType adt of Just t -> t
  | algDataNumConstructors adt == 1 = productValueType adt
  | otherwise                       = sumValueType adt

{-
-- | This function sets up the lambda function part of an eliminator term.
--   The lamba function's body is created by the last parameter.
--
-- > \ scrutinee k1 ... kN -> $(mk_body scrutinee [k1, ..., kN])
eliminatorValueFunction :: AlgValueType
                        -> [ValueType]
                        -> (L.Val -> [L.Val] -> GenM L.Stm)
                        -> GenM L.Val
eliminatorValueFunction adt return_types mk_body =
  genLambdaStm param_types return_types $ \(scr : conts) -> mk_body scr conts
  where
    n_constructors = algDataNumConstructors adt
    scrutinee_type = algDataValueType' adt
    param_types = scrutinee_type : replicate n_constructors (PrimType OwnedType)

-- | Return a constructor function for an enumeration value type
enumerationConstructor :: AlgValueType
                       -> AlgDisjunct ValueType
                       -> GenM L.Val
enumerationConstructor adt dj =
  mkConstructorFunction adt dj $ \ [] -> return tag_value
  where
    Just tag_value = tagInfo dj
-}

valueIntroE :: AlgValueType -> IntroE L.Val
valueIntroE adt con_index = return tag_value
  where
    Just tag_value = varTagInfo $ disjunct con_index adt

valueElimE :: AlgValueType -> [ValueType] -> ElimE [L.Val]
valueElimE adt return_types scrutinee k 
  | algDataNumConstructors adt == 1 =
      k 0
  | otherwise =
      tagDispatch2 adt_type n scrutinee return_types k
  where
    adt_type = algDataValueType' adt
    n = algDataNumConstructors adt

valueIntroP :: AlgValueType -> IntroP L.Val
valueIntroP adt fields =
  check_fields $ packRecord (productRecordType adt) fields
  where
    check_fields x =
      if length fields /= length (algDisjunctFields $ disjunct 0 adt)
      then internalError "valueIntroP: Wrong number of fields"
      else x

valueElimP :: AlgValueType -> ElimP [L.Val]
valueElimP adt scrutinee k =
  k =<< unpackRecord2 (productRecordType adt) scrutinee

valueIntroS :: AlgValueType -> IntroS L.Val
valueIntroS adt dj =
  checkDisjunct adt dj $
  packRecord (sumRecordType adt) (tag_value : disjunct_values)
  where
    con_index = algDisjunctConIndex dj
    Just tag_value = varTagInfo dj
    disjunct_values = mapMaybe disjunct_record $ disjuncts adt
      where
        disjunct_record d
          | algDisjunctConIndex d == con_index = realDisjunct dj
          | otherwise                          = dummyDisjunct d
                                                              
    dummyDisjunct :: AlgDisjunct ValueType -> Maybe L.Val
    dummyDisjunct dj = fmap dummyValue $ disjunctType dj

    realDisjunct :: AlgDisjunct L.Val -> Maybe L.Val
    realDisjunct dj =
      case disjunctRecordType $ fmap L.valType dj
      of Nothing -> Nothing
         Just rt -> Just $ L.RecV rt (algDisjunctFields dj)

valueElimS :: AlgValueType -> [ValueType] -> ElimS [L.Val]
valueElimS adt return_types scrutinee k = do
  (tag_value : disjunct_values) <- unpackRecord2 (sumRecordType adt) scrutinee
  tagDispatch2 tag_type n tag_value return_types (call_cont disjunct_values)
  where
    Just tag_type = algDataTagType adt
    n = algDataNumConstructors adt
    dj_indices = disjunctIndices adt

    -- Construct an AlgDisjunct and pass it to the continuation
    call_cont disjunct_values index = do
      values <-
        case disjunctRecordType $ disjunct index adt
        of Nothing -> return [] -- No fields
           Just rt ->
             -- Extract the field values of this disjunct
             let Just dj_index = dj_indices !! index
                 record = disjunct_values !! dj_index
             in unpackRecord2 rt record

      -- Create a disjunct containing these values
      k $ disjunctData index values adt

-- | Create a value of the given data type
valueIntro :: AlgValueType      -- ^ Algebraic data type
           -> Int               -- ^ Constructor index
           -> [L.Val]           -- ^ Field values
           -> GenM L.Val        -- ^ Computes a result value
valueIntro adt con_index fields
  | isEnumeration adt =
      if not $ null fields
      then internalError "valueIntro: Unexpected fields"
      else valueIntroE adt con_index

  | algDataNumConstructors adt == 1 =
      valueIntroP adt fields

  | otherwise =
      valueIntroS adt $ disjunctData con_index fields adt

-- | Create a constructor function for the given data type.
--   This function takes the field values (or, if there are no fields, a 
--   unit value) and returns the constructed value.
valueConstructor :: AlgValueType -> Int -> GenM L.Val
valueConstructor adt con_index =
  let adt_type = algDataValueType' adt
      field_types = algDisjunctFields $ disjunct con_index adt
  in mkConstructorFunction adt_type field_types $ valueIntro adt con_index

-- | Inspect a value of the given algebraic data type
valueElim :: AlgValueType                     -- ^ Algebraic data type
          -> [ValueType]                      -- ^ Result types
          -> (Int -> [L.Val] -> GenM [L.Val]) -- ^ Handlers for disjuncts
          -> L.Val                            -- ^ Scrutinee
          -> GenM [L.Val]                     -- ^ Computes results
valueElim adt result_types handler scrutinee
  | isEnumeration adt =
      valueElimE adt result_types scrutinee (\i -> handler i [])
  | algDataNumConstructors adt == 1 =
      valueElimP adt scrutinee (\fs -> handler 0 fs)
  | otherwise =
      let h dj = handler (algDisjunctConIndex dj) (algDisjunctFields dj)
      in valueElimS adt result_types scrutinee h

-- | Extract fields of a single-constructor value of the
--   given algebraic data type
valueDeconstructor :: AlgValueType -> L.Val -> GenM [L.Val]
valueDeconstructor adt scrutinee
  | algDataNumConstructors adt /= 1 =
      internalError "valueDeconstructor: Type must have one constructor"
  | isEnumeration adt =
      -- This is a unit value
      return []
  | otherwise =
      -- Product value
      valueElimP adt scrutinee return

-- | Create an eliminator function that applies fields of the
--   given algebraic data type to continuation functions
valueEliminator :: AlgValueType -> [ValueType] -> L.Val -> GenM L.Val
valueEliminator adt return_types scrutinee
  | n == 0 =
      internalError "valueEliminator: Uninhabited type"
  | otherwise =
      -- Create a function that takes continuation functions and returns
      -- their results
      genLambda param_types return_types $ \handlers ->
      let apply_handler i fs =
            let args = addDummyParameterValue fs
                callee = handlers !! i
            in emitAtom return_types $ continuationCall2 callee args
      in valueElim adt return_types apply_handler scrutinee
  where
    n = algDataNumConstructors adt
    param_types = replicate n (PrimType OwnedType)

{-
-- | Return an eliminator function for an enumeration value type with
--   one constructor
enumerationDeconstructor :: AlgValueType -> GenM L.Val
enumerationDeconstructor adt =
  genLambda [adt_type] [] $ \ [_] -> return []
  where
    adt_type = algDataValueType' adt

-- | Return an eliminator function for an enumeration value type with
--   fewer or more than one constructor
enumerationEliminator :: [ValueType]
                      -> AlgValueType
                      -> GenM L.Val
enumerationEliminator return_types adt =
  eliminatorValueFunction adt return_types $ \ scrutinee conts ->
  tagDispatch adt_type scrutinee (map mk_continuation conts)
  where
    adt_type = algDataValueType' adt
    mk_continuation k = return $ continuationCall k []

-- | Return a constructor function for a product value type
productValueConstructor :: AlgValueType
                        -> AlgDisjunct ValueType
                        -> GenM L.Val
productValueConstructor adt dj =
  mkConstructorFunction adt dj $ \args -> return (static_record args)
  where
    AlgDisjunct header (Just fields) = dj
    static_record fs = L.RecV record_type fs
    record_type = constStaticRecord $ map valueToFieldType fields

productValueDeconstructor adt =
  genLambda [adt_type] field_types $ \ [scrutinee] -> do
    vs <- unpackRecord record_type scrutinee
    return $ map L.VarV vs
  where
    adt_type = algDataValueType' adt
    RecordType record_type = adt_type
    field_types = algDisjunctFields $ disjunct 0 adt

sumValueConstructor :: AlgValueType -> Int -> GenM L.Val
sumValueConstructor adt con_index =
  mkConstructorFunction adt dj $ \args ->
  return $ L.RecV (sumRecordType adt) (tag_value : disjunct_values args)
  where
    dj = disjunct con_index adt
    Just tag_value = tagInfo dj

    disjunct_values args =
      [ if i == con_index then realDisjunct dj args else dummyDisjunct dj
      | i <- [0 .. algDataNumConstructors adt - 1]
      , let dj = disjunct i adt]

sumValueEliminator return_types adt =
  eliminatorValueFunction adt return_types $ \scrutinee conts -> do
    tag : disjunct_values <- unpackRecord record_type scrutinee
    tagDispatch tag_type (L.VarV tag) $
      zipWith (mk_continuation disjunct_values) conts [0..]
  where
    adt_type = algDataValueType' adt
    Just tag_type = algDataTagType adt
    RecordType record_type = adt_type

    mk_continuation disjunct_values cont index =
      let dj = disjunct index adt
          dj_record = disjunctRecordType dj
          value = L.VarV (disjunct_values !! index)
      in do field_values <- unpackRecord dj_record value
            return $ continuationCall cont (map L.VarV field_values)


-- | Create a deconstructor function for a single-constructor value type
valueTypeDeconstructor :: AlgData ValueType -> GenM L.Val
valueTypeDeconstructor adt
  | isEnumeration adt = enumerationDeconstructor adt
  | otherwise = productValueDeconstructor adt

-- | Create an eliminator function for a multi-constructor value type
valueTypeEliminator :: [ValueType] -> AlgData ValueType -> GenM L.Val
valueTypeEliminator return_types adt
  | isEnumeration adt = enumerationEliminator return_types adt
  | otherwise = sumValueEliminator return_types adt
-}

loadValueType :: Layout -> L.Val -> GenM L.Val 
loadValueType (PrimLayout t)   ptr = primLoadConst (PrimType t) ptr
loadValueType (BlockLayout _)  _   = internalError "loadValueType: No value type"
loadValueType (DataLayout adt) ptr = loadAlgValue adt ptr

storeValueType :: Layout -> L.Val -> L.Val -> GenM ()
storeValueType (PrimLayout t)   ptr val = primStoreConst (PrimType t) ptr val
storeValueType (BlockLayout _)  _   _   = internalError "storeValueType: No value type"
storeValueType (DataLayout adt) ptr val = storeAlgValue adt ptr val

-- | Load a value into a local variable
loadAlgValue :: AlgData LayoutField -> L.Val -> GenM L.Val
loadAlgValue adt ptr = do
  mem_adt <- memoryLayout adt
  [x] <- memoryElim mem_adt [adt_type] read_value ptr
  return x
  where
    adt_type = algDataValueType adt
    val_adt = valueLayout adt
    read_value con_index fields = do
      x <- valueIntro val_adt con_index fields
      return [x]

-- | Store a local variable into a destination pointer
storeAlgValue :: AlgData LayoutField -> L.Val -> L.Val -> GenM ()
storeAlgValue adt ptr val = do
  mem_adt <- memoryLayout adt
  let write_value con_index fields = do
        initializer <- memoryIntro mem_adt con_index fields
        emitAtom [] $ L.closureCallA initializer [ptr]
  valueElim val_adt [] write_value val
  return ()
  where
    val_adt = valueLayout adt

-------------------------------------------------------------------------------

-- | Allocate a boxed object and initialize its header.  Return a pointer to
--   the new object.
--   The object's size should have been computed by 'disjunctLayout'.
createBoxedObject :: SizeAlign -> HeaderOffsets -> HeaderData -> GenM L.Val
createBoxedObject size hoff hdata = do
  ptr <- allocateHeapMemComposite (objectSize size)
  writeHeader hdata hoff ptr
  return ptr

-- | Create and return an initializer function for a bare object.  The
--   initializer function initializes its header and executes the given code 
--   to initialize its fields.
--   
--   The object's size should have been computed by 'algUnboxedLayout'.
createBareObject :: SizeAlign -> HeaderOffsets -> HeaderData
                 -> (L.Val -> GenM ()) -> GenM L.Val
createBareObject size hoff hdata init_contents =
  genLambda [PrimType PointerType] [PrimType UnitType] $ \[ptr] -> do
    writeHeader hdata hoff ptr
    init_contents ptr
    return [L.LitV L.UnitL]

-- | Create an object in memory
memoryIntro :: AlgObjectType -> Int -> [L.Val] -> GenM L.Val
memoryIntro adt con_index fields =
  case algDataBoxing adt
  of IsBoxed -> do
       (h_offsets, offsets, size) <- disjunctLayout dj
       ptr <- createBoxedObject size h_offsets (algDisjunctHeader dj)
       write_fields offsets ptr
       return ptr
     NotBoxed -> do
       (h_offsets, offsetss, size) <- algUnboxedLayout adt
       let offsets = offsetss !! con_index
       createBareObject size h_offsets (algDisjunctHeader dj) (write_fields offsets)
  where
    dj = disjunct con_index adt
    write_fields offsets ptr =
      forM_ (zip3 (algDisjunctFields dj) offsets fields) $
      \(field, offset, value) -> writeMemoryField ptr field offset value

memoryElim :: AlgObjectType -> [ValueType] -> (Int -> [L.Val] -> GenM [L.Val])
           -> L.Val -> GenM [L.Val]
memoryElim adt return_types handlers scrutinee = do
  -- Read the tag
  (h_offsets, off1) <- headerLayout header_type
  m_tag_value <- readHeaderTag header_type h_offsets scrutinee
  case m_tag_value of
    -- No tag
    Nothing -> elim_product h_offsets off1 (disjunct 0 adt)

    -- Dispatch by tag
    Just tag_value ->
      tagDispatch2 tag_type n_constructors tag_value return_types $ \i ->
        elim_product h_offsets off1 (disjunct i adt)
  where
    header_type = algDataHeaderType adt
    Just tag_type = memTagInfo header_type
    n_constructors = algDataNumConstructors adt

    -- Read fields of a particular disjunct and pass them to a handler
    elim_product h_offsets off1 dj = do
      (_, offsets, _) <- disjunctLayout1 h_offsets off1 (algDisjunctFields dj)
      let fields = algDisjunctFields dj
      values <- forM (zip fields offsets) $ \(field, offset) ->
        readMemoryField scrutinee field offset
      handlers (algDisjunctConIndex dj) values

-- | Create a constructor function for the given data type.
--   This function takes the field values (or, if there are no fields,
--   a unit value) and returns a constructed object or an initializer.
memoryConstructor :: AlgObjectType -> Int -> GenM L.Val
memoryConstructor adt con_index =
  let adt_type = constructedObjectType adt
      field_types = map memoryFieldType $
                    algDisjunctFields $ disjunct con_index adt
  in mkConstructorFunction adt_type field_types $ memoryIntro adt con_index

-- | Deconstruct an object of the given data type, which must
--   have a single data constructor.
--
--   This function takes a reference to an object and returns its fields.
memoryDeconstructor :: AlgObjectType -> L.Val -> GenM [L.Val]
memoryDeconstructor adt scrutinee 
  | algDataNumConstructors adt /= 1 =
      internalError "memoryDeconstructor: Type must have one constructor"
  | otherwise =
      memoryElim adt field_types (\_ fs -> return fs) scrutinee
  where
    dj = disjunct 0 adt
    field_types = map memoryFieldType $ algDisjunctFields dj

-- | Create an eliminator for an object of the given data type.
--   The eliminator takes a continuation for each constructor and invokes
--   the matching continuation.
memoryEliminator :: AlgObjectType -> [ValueType] -> L.Val -> GenM L.Val
memoryEliminator adt return_types scrutinee
  | n == 0 =
      internalError "valueEliminator: Uninhabited type"
  | otherwise =
      -- Create a function that takes continuation functions and returns
      -- their results
      genLambda param_types return_types $ \handlers ->
      let apply_handler i fs =
            let args = addDummyParameterValue fs
                callee = handlers !! i
            in emitAtom return_types $ continuationCall2 callee args
      in memoryElim adt return_types apply_handler scrutinee
  where
    n = algDataNumConstructors adt
    param_types = replicate n (PrimType OwnedType)

-------------------------------------------------------------------------------

-- | Get the type of a low-level variable representing a field that is
--   loaded or stored, once it has been placed in memory.
memoryFieldType :: MemoryField -> ValueType
memoryFieldType BoxedField    = PrimType OwnedType
memoryFieldType (ValField l)  = layoutValueType l
memoryFieldType (BareField _) = PrimType PointerType

readMemoryField :: L.Val -> MemoryField -> Off -> GenM L.Val
readMemoryField ptr fld (Off offset) =
  case fld
  of -- Load a pointer
     BoxedField  -> primLoadOffMutable (PrimType OwnedType) ptr offset
     -- Get address of field
     BareField _ -> primAddP ptr offset
       -- Load primitive value into a variable
     ValField l  -> loadValueType l =<< primAddP ptr offset

writeMemoryField :: L.Val -> MemoryField -> Off -> L.Val -> GenM ()
writeMemoryField ptr fld (Off offset) val =
  case fld
  of -- Store a pointer
     BoxedField  -> primStoreOffMutable (PrimType OwnedType) ptr offset val
     -- Run an initializer
     BareField _ -> do ptr <- primAddP ptr offset
                       emitAtom0 $ L.closureCallA val [ptr]
     -- Store primitive value from variable
     ValField l  -> do ptr <- primAddP ptr offset
                       storeValueType l ptr val
