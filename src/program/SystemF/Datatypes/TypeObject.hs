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
import qualified LowLevel.Types as LL
import SystemF.Syntax
import SystemF.MemoryIR
import SystemF.Datatypes.DynamicTypeInfo
import SystemF.Datatypes.Structure
import SystemF.Datatypes.Util(tagType)
import SystemF.Datatypes.Layout
import SystemF.Datatypes.InfoCall
import SystemF.Datatypes.Code
import Type.Type
import Type.Environment
import Type.Eval


-------------------------------------------------------------------------------

-- | Compute the size and alignment of an object header.
--   Size and alignment depend on whether the object is boxed and how many
--   constructors it has.
--
--   The results of this function must agree with
--   'SystemF.Datatypes.Layout.headerLayout'.
headerSize :: Boxing -> Int -> SizeAlign
headerSize boxing n_constructors =
  SizeAlign (uintL header_size) (uintL header_align)
  where
    -- Object header, if boxed
    (oh_size, oh_align) =
      case boxing
      of NotBoxed -> (0, 1) 
         IsBoxed  -> (LL.sizeOf LL.OwnedType, LL.alignOf LL.OwnedType)

    -- Add tag size, if tagged
    (header_size, header_align) =
      case tagType n_constructors
      of Nothing -> (oh_size, oh_align)
         Just ty -> let padding = negate oh_size `mod` LL.alignOf ty
                        size2 = oh_size + padding + LL.sizeOf ty
                    in (size2, oh_align `max` LL.alignOf ty)

-- | Compute the size and alignment of a type of kind 'val'
computeValInfo :: CoreDynTypeInfo
               -> Structure
               -> Gen ValInfo
computeValInfo type_info layout =
  case layout
  of PrimStruct pt            -> return $ primSize pt
     DataStruct (Data tag fs) -> sumValInfo type_info tag fs
     ForallStruct fa          -> forall_layout fa
     VarStruct v              -> var_layout v
     UninhabitedStruct        -> internalError "computeLayout: Uninhabited"
  where
    var_layout v = lift $ lookupValTypeInfo' type_info v

    forall_layout (Forall b t) = assumeBinder b $ do
      s <- lift $ computeStructure t
      computeValInfo type_info s

sumValInfo :: CoreDynTypeInfo -> Boxing -> Alternatives
           -> Gen ValInfo
sumValInfo _ _ [] =
  internalError "computeValInfo: Uninhabited type"

sumValInfo type_info tag alts = do
  let header_layout = headerSize tag (length alts)
  disjunct_info <- mapM (alt_layout header_layout) alts

  -- Combine disjuncts
  size <- overlays $ map val_info_size disjunct_info
  pointer_free <- allPointerFree $ map val_info_pointers disjunct_info
  return $ ValInfo size pointer_free

  where
    -- Layouts of fields of a case alternative
    alt_layout header_layout (Alternative decon fs) = do
      field_info <- assumeBinders (deConExTypes decon) $ mapM field_layout fs

      size <- structSize $
              header_layout : map (fieldDetailsSize . fiDetails) field_info
      pointer_free <- allPointerFree $
                      map (fieldDetailsPointerFree . fiDetails) field_info
      return $ ValInfo size pointer_free

    field_layout (k, t) = fieldInfo type_info (k, t)

primSize pt = ValInfo (SizeAlign size alignment) pointer_free
  where
    size = uintL $ LL.sizeOf pt 
    alignment = uintL $ LL.alignOf pt
    pointer_free = case pt
                   of LL.OwnedType    -> notPointerFree
                      LL.UnitType {}  -> isPointerFree
                      LL.BoolType {}  -> isPointerFree
                      LL.IntType {}   -> isPointerFree
                      LL.FloatType {} -> isPointerFree

-- | Information about how a field of an object is represented
data FieldInfo = FieldInfo Type !FieldDetails

fiDetails (FieldInfo _ d) = d

-- | Kind-specific information about how a field of an object is represented
data FieldDetails =
    ValDetails ValInfo
  | BareDetails BareInfo
  | BoxDetails

fieldDetailsSize :: FieldDetails -> SizeAlign
fieldDetailsSize BoxDetails      = val_info_size $ primSize LL.OwnedType
fieldDetailsSize (ValDetails i)  = val_info_size i
fieldDetailsSize (BareDetails i) = bare_info_size i

-- | Get the pointerlessness of this field.  The result is a boolean.
fieldDetailsPointerFree :: FieldDetails -> PointerFree
fieldDetailsPointerFree BoxDetails      = notPointerFree
fieldDetailsPointerFree (ValDetails i)  = val_info_pointers i
fieldDetailsPointerFree (BareDetails i) = bare_info_pointers i

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
      | k == BareK = fmap BareDetails $ structureRepr type_info Nothing t s
      | k == ValK  = fmap ValDetails $ computeValInfo type_info s

-- | Information about the size of a field of an object.
--   A 'FieldSize' contains size information about an unboxed field.
--   For a boxed field, it contains 'Nothing'.
data FieldSize = FieldSize Type !(Maybe SizeAlign)

fsSize (FieldSize _ d) = d

-- | Get the size of a field.  If boxed, it's the size of a pointer.
fsSize' (FieldSize _ Nothing)  = val_info_size $ primSize LL.OwnedType
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
     PrimStruct pt            -> return $ val_info_size $ primSize pt
     UninhabitedStruct        -> internalError "structureSize: Uninhabited"
  where
    continue k t l = structureSize type_info k t l

    var_layout v = 
      case kind
      of ValK  -> lift $ lookupValTypeInfo' type_info v
         BareK -> lift $ lookupBareTypeInfo' type_info v

    forall_layout (Forall b t) = assumeBinder b $ do
      structureSize type_info kind t =<< lift (computeStructure t)

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
              -> Maybe ExpM     -- ^ An expression that evaluates to
                                --   the representation of this type.
                                --   'Nothing' if not an algebraic data
                                --   structure.  This expression can only
                                --   be used lazily, under a lambda.
              -> Type
              -> Structure
              -> Gen BareInfo
structureRepr type_info m_rec_exp ty layout =
  case layout
  of DataStruct (Data tag fs) -> let Just rec_exp = m_rec_exp  
                                 in sumRepr type_info rec_exp ty tag fs
     ForallStruct fa          -> forall_layout fa
     VarStruct v              -> var_layout v
     ArrStruct t ts           -> arrRepr type_info t ts
     PrimStruct pt            -> internalError "structureRepr: Unexpected type"
     UninhabitedStruct        -> internalError "structureRepr: Uninhabited"
  where
    continue t l = structureRepr type_info Nothing t l

    var_layout v = lift $ lookupBareTypeInfo' type_info v

    forall_layout (Forall b t) =
      assumeBinder b $ continue t =<< lift (computeStructure t)

sumRepr type_info rec_exp ty tag alts = do
  let header_layout = headerSize tag (length alts)

  -- Compute representation info for all data constructors
  field_info <-
    forM alts $ \(Alternative decon fs) ->
    assumeBinders (deConExTypes decon) $
    mapM (fieldInfo type_info) fs
    
  -- Compute properties of data constructors
  constructor_info <- zipWithM (alt_repr header_layout) field_info alts

  -- A recursive call that constructs this info object; needed for
  -- converting to boxed
  lazy_rec_exp <- lazyExp (bareInfoT `AppT` ty) rec_exp

  -- Combine info
  sum_size <- overlays $ map fst constructor_info
  pointer_free <- allPointerFree $ map snd constructor_info
  copy_fun <- sumCopyFunction type_info ty (zip field_info alts)
  let as_box = varAppE' defaultAsBoxV [ty] [lazy_rec_exp]
  let as_bare = varAppE' defaultAsBareV [ty]
                [packSizeAlign ty sum_size, copy_fun]
  return $ BareInfo sum_size copy_fun as_box as_bare pointer_free
  where
    -- Compute repr information for one constructor.
    -- The returned tuple contains values for the size, copy, and pointerless 
    -- fields of 'BareInfo'.
    alt_repr :: SizeAlign -> [FieldInfo] -> Alternative
             -> Gen (SizeAlign, PointerFree)
    alt_repr header_layout field_info (Alternative decon fs) =
      assumeBinders (deConExTypes decon) $ do
        size <- let sizes = [fieldDetailsSize d | FieldInfo _ d <- field_info]
                in structSize (header_layout : sizes)

        -- Pointerless: logical 'and' of all fields; False if any fields are
        -- boxed
        bytes <- allPointerFree [fieldDetailsPointerFree d | FieldInfo _ d <- field_info]

        return (size, bytes)
        
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
copyConstructor :: CoreDynTypeInfo -> Var -> [Type] -> [ExpM]
                -> [Type] -> [(FieldInfo, ExpM)] -> ExpM
copyConstructor type_info con ty_args size_params ex_types fields =
  unboxedConE' (VarCon con ty_args ex_types) size_params (map field_expr fields)
  where
    field_expr (FieldInfo ty details, e) =
      case details
      of ValDetails _  -> e
         BoxDetails    -> e
         BareDetails d -> appE' (bare_info_copy d) [] [e]

arrRepr :: CoreDynTypeInfo -> Type -> Type -> Gen BareInfo
arrRepr type_info size elem = do
  let array_type = varApp arrV [size, elem]
  size_val <- lift $ lookupIntTypeInfo' type_info size
  elem_repr <- structureRepr type_info Nothing elem =<< lift (computeStructure elem)

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
typeInfoDefinition :: DataType
                   -> (CoreDynTypeInfo -> Gen ExpM)
                   -> UnboxedTypeEvalM (Ent Mem)
typeInfoDefinition dtype construct_info =
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
    make_body parameters = runGen $ do
      dyn_info <- makeDynTypeInfo (zip parameters param_types)
      construct_info dyn_info

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
sizeInfoDefinition :: DataConType -> UnboxedTypeEvalM (Ent Mem)
sizeInfoDefinition dcon_type =
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
    make_body parameters = runGen $ do
      dyn_info <- makeDynSizeInfo (zip parameters param_types)
      let ty = dataTypeCon dtype `varApp` [VarT v | v ::: _ <- ty_params]

      -- Compute sizes
      DataStruct dat <- lift $ computeStructure ty
      field_sizes <- disjunctSizes dyn_info ty dat (dataConCon dcon_type)

      -- Create a tuple
      return $ pack_fields field_sizes

sizeInfoDefinitions dtype =
  forM (dataTypeDataConstructors dtype) $ \c -> do
    Just dcon_type <- lookupDataCon c
    ent <- sizeInfoDefinition dcon_type
    return $ mkDef (dataTypeFieldSizeVar dtype c) ent

-------------------------------------------------------------------------------
-- Entry points

-- | Define an info variable for a primitive value type.
--   Primitive types have no data constructors, so there are no size info 
--   variables.
definePrimitiveValInfo :: DataType -> UnboxedTypeEvalM [GDef Mem]
definePrimitiveValInfo dtype
  | dataTypeIsAbstract dtype && not (dataTypeIsAlgebraic dtype) &&
    null (dataTypeDataConstructors dtype) =
      valInfoDefinition dtype
  | otherwise =
      internalError "definePrimitiveValInfo"

-- | Create definitions of layout information for the data type.
--   One definition is created for unboxed types, or one per data constructor
--   for boxed types.
valInfoDefinition :: DataType -> UnboxedTypeEvalM [GDef Mem]
valInfoDefinition dtype = do
  ent <- typeInfoDefinition dtype build_info
  let info_def = mkDef (dataTypeUnboxedInfoVar dtype) ent
  size_defs <- sizeInfoDefinitions dtype
  return (info_def : size_defs)
  where
    ty_args = [VarT v | v ::: _ <- dataTypeParams dtype] 
    ty = dataTypeCon dtype `varApp` ty_args

    -- Create the info object for this data type constructor
    build_info dyn_info = do
      sa <- computeValInfo dyn_info =<< lift (computeStructure ty)
      return $ packReprVal ty sa

bareInfoDefinition :: DataType -> UnboxedTypeEvalM [GDef Mem]
bareInfoDefinition dtype = do
  ent <- typeInfoDefinition dtype build_info
  let info_def = add_attributes $ mkDef info_var ent
  size_defs <- sizeInfoDefinitions dtype
  return (info_def : size_defs)
  where
    ty_args = [VarT v | v ::: _ <- dataTypeParams dtype] 
    ty = dataTypeCon dtype `varApp` ty_args
    info_var = dataTypeUnboxedInfoVar dtype

    -- Create the info object for this data type constructor
    build_info dyn_info = do
      -- Create a recursive call to the info object for this type constructor
      info_e <- callKnownUnboxedInfoFunction dyn_info dtype ty_args
      rep <- structureRepr dyn_info (Just info_e) ty =<< lift (computeStructure ty)
      return $ packRepr ty rep

    -- Temporarily mark type object constructors as "inline_never".
    -- These objects may be recursive, and the simplifier doesn't terminate
    -- correctly for this form of recursion. 
    -- This needs a better fix, because inlining these objects is important.
    add_attributes def =
      modifyDefAnnotation (\d -> d {defAnnInlineRequest = InlNever}) def

boxInfoDefinitions :: DataType -> UnboxedTypeEvalM [GDef Mem]
boxInfoDefinitions dtype = do 
  info_defs <- forM (dataTypeDataConstructors dtype) $ \c -> do
    Just dcon_type <- lookupDataCon c
    ent <- typeInfoDefinition dtype $ build_info dcon_type
    return $ add_attributes $ mkDef (dataTypeBoxedInfoVar dtype c) ent
  size_defs <- sizeInfoDefinitions dtype
  return (info_defs ++ size_defs)
  where
    ty_args = [VarT v | v ::: _ <- dataTypeParams dtype] 
    ty = dataTypeCon dtype `varApp` ty_args

    -- Create the info object for this data type constructor
    build_info dcon_type _ = do
      let rep = BoxInfo (uintL $ dataConIndex dcon_type)
      return $ packTypeObject ty rep

    -- Type object constructors 
    -- with no value parameters are marked "inline_never".
    -- These objects may be recursive, and the simplifier doesn't terminate
    -- correctly for this form of recursion. 
    -- Besides, they're not very useful to inline because we don't
    -- deconstruct them very often.
    add_attributes def
      | FunEnt (FunM f) <- definiens def, null $ funParams f =
          modifyDefAnnotation (\d -> d {defAnnInlineRequest = InlNever}) def
      | otherwise = def
