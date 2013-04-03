{-| Type object generation.

This code creates a global type object for each algebraic data type definition.
In many ways, type objects hold 

For type object constructor @S@ and type constructor @T@,
the global type object is a function or constant of type
@forall tys. size_parameters -> S (T tys)@.
-}

module SystemF.Datatypes.TypeObject
       (valInfoDefinition,
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
import Common.Supply
import Builtins.Builtins
import qualified LowLevel.Types as LL
import SystemF.Syntax
import SystemF.MemoryIR
import SystemF.Datatypes.DynamicTypeInfo
import SystemF.Datatypes.Structure
import SystemF.Datatypes.Util(tagType)
import SystemF.Datatypes.Layout
import Type.Type
import Type.Environment
import Type.Eval

-- | Simple expression contexts for let bindings
newtype MkExp = MkExp (ExpM -> ExpM)

instance Monoid MkExp where
  mempty = MkExp id
  mappend (MkExp f) (MkExp g) = MkExp (f . g)

type Gen a = WriterT MkExp UnboxedTypeEvalM a

-- | Size and alignment of an object.
--   Corresponds to data type @SizeAlign@ or @SizeAlignVal@.
data SizeAlign = SizeAlign {objectSize :: !Sz, objectAlign :: !Al}

-- | A length value, holding an 'int'
newtype Length = Length ExpM

-- | A boolean vaule, indicating whether a data structure doesn't
--   contain pointers to heap objects.
--   'True' means the structure has no pointers.
newtype PointerFree = PointerFree ExpM

isPointerFree, notPointerFree :: PointerFree
isPointerFree = PointerFree (conE' (VarCon true_conV [] []) [])
notPointerFree = PointerFree (conE' (VarCon false_conV [] []) [])

-- | The unpacked fields of a 'TypeObject' object
data BoxInfo =
  BoxInfo
  { box_info_conid :: !ExpM    -- An unsigned integer
  }

-- | The unpacked fields of a 'Repr' object
data BareInfo =
  BareInfo 
  { bare_info_size    :: !SizeAlign 
  , bare_info_copy    :: !ExpM
  , bare_info_asbox   :: !ExpM
  , bare_info_asbare  :: !ExpM
  , bare_info_pointers :: !PointerFree
  }

-- | The unpacked fields of a 'ReprVal' object
data ValInfo =
  ValInfo
  { val_info_size     :: !SizeAlign
  , val_info_pointers :: !PointerFree
  }

runGen :: Gen ExpM -> UnboxedTypeEvalM ExpM
runGen m = do (x, MkExp f) <- runWriterT m
              return $ f x

-- | Bind an expression's result to a variable.
--
--   This is done when an expression may be used multiple times, 
--   to avoid introducing redundant work.
emit :: Type -> ExpM -> Gen ExpM

-- Don't bind literals, variables, or nullary constructors to variables
emit ty rhs@(ExpM (VarE {})) = return rhs
emit ty rhs@(ExpM (LitE {})) = return rhs
emit ty rhs@(ExpM (ConE _ (VarCon _ [] []) [])) = return rhs

emit ty rhs = do
  v <- lift $ newAnonymousVar ObjectLevel
  tell $ MkExp (\body -> ExpM $ LetE defaultExpInfo (patM (v ::: ty)) rhs body)
  return (varE' v)

-- | Deconstruct a single-constructor type.  Return the existential types and
--   field types.
decon :: Type -> ExpM -> Gen ([Var], [ExpM])
decon prod_type scrutinee = do
  (decon_inst, field_types) <- lift $ do
    -- Get data constructor type
    Just (tycon, ty_args) <- deconVarAppType prod_type
    Just data_type <- lookupDataType tycon
    let [data_con] = dataTypeDataConstructors data_type
    Just data_con_type <- lookupDataCon data_con

    -- Instantiate the type
    (ex_binders, field_types, _) <-
      instantiateDataConTypeWithFreshVariables data_con_type ty_args

    let decon_inst = VarDeCon data_con ty_args ex_binders
    return (decon_inst, field_types)

  field_binders <- lift $ forM field_types $ \t -> do
    v <- newAnonymousVar ObjectLevel
    return $ patM (v ::: t)
  
  -- Create the case expression
  let mk_case body =
        ExpM $ CaseE defaultExpInfo scrutinee
        [AltM $ Alt decon_inst field_binders body]
  tell (MkExp mk_case)

  let ex_vars = map binderVar $ deConExTypes decon_inst
      fields = map (varE' . patMVar) field_binders
  return (ex_vars, fields)

-- | Create a case expression to deconstruct a multiple-constructor type.
--   Handle the alternatives in-place.
mkCase :: Type -> ExpM -> [(Var, [Type] -> [ExpM] -> UnboxedTypeEvalM ExpM)]
       -> UnboxedTypeEvalM ExpM
mkCase ty scrutinee alt_handlers = do
    -- Get data constructor type
    Just (tycon, ty_args) <- deconVarAppType ty
    Just data_type <- lookupDataType tycon

    -- Handle each disjunct
    alts <- forM (dataTypeDataConstructors data_type) $ \data_con -> do
      let Just handle_alt = lookup data_con alt_handlers

      -- Create a pattern to match this constructor
      Just data_con_type <- lookupDataCon data_con
      (ex_binders, field_types, _) <-
        instantiateDataConTypeWithFreshVariables data_con_type ty_args

      let decon = VarDeCon data_con ty_args ex_binders

      param_vars <- replicateM (length field_types) $
                    newAnonymousVar ObjectLevel
      let field_binders = map patM $ zipWith (:::) param_vars field_types

      -- Create the body expression
      body <- let ex_types = map (VarT . binderVar) ex_binders
                  fields = map (varE' . patMVar) field_binders
              in assumeBinders ex_binders $ assumePatMs field_binders $
                 handle_alt ex_types fields
        
      return $ AltM $ Alt decon field_binders body

    -- Build case expression
    return $ ExpM $ CaseE defaultExpInfo scrutinee alts

-- | Extract the fields of a @SizeAlignVal a@ term.
unpackSizeAlignVal :: Type -> ExpM -> Gen SizeAlign
unpackSizeAlignVal ty e = do
  ([], [s, a]) <- decon (sizeAlignValV `varApp` [ty]) e
  return $ SizeAlign s a

-- | Construct a @SizeAlignVal a@ term.
packSizeAlignVal :: Type -> SizeAlign -> ExpM
packSizeAlignVal ty (SizeAlign s a) =
  conE' (VarCon sizeAlignVal_conV [ty] []) [s, a]

-- | Extract the fields of a @ReprVal a@ term.
unpackReprVal :: Type -> ExpM -> Gen ValInfo
unpackReprVal ty e = do
  ([], [sa, p]) <- decon (valInfoV `varApp` [ty]) e
  sa' <- unpackSizeAlignVal ty sa
  return $ ValInfo sa' (PointerFree p)

-- | Construct a @SizeAlignVal a@ term.
packReprVal :: Type -> ValInfo -> ExpM
packReprVal ty (ValInfo sa (PointerFree p)) =
  conE' (VarCon valInfo_conV [ty] []) [packSizeAlignVal ty sa, p]

-- | Extract the fields of a @SizeAlign a@ term.
unpackSizeAlign :: Type -> ExpM -> Gen SizeAlign
unpackSizeAlign ty e = do
  ([], [s, a]) <- decon (sizeAlignV `varApp` [ty]) e
  return $ SizeAlign s a

-- | Construct a @SizeAlign a@ term.
packSizeAlign :: Type -> SizeAlign -> ExpM
packSizeAlign ty (SizeAlign s a) =
  conE' (VarCon sizeAlign_conV [ty] []) [s, a]

-- | Extract the fields of a @Repr a@ term.
unpackRepr :: Type -> ExpM -> Gen BareInfo
unpackRepr ty e = do
  ([], [size_align, copy, asbox, asbare, just_bytes]) <-
    decon (bareInfoV `varApp` [ty]) e
  sa <- unpackSizeAlign ty size_align
  return $ BareInfo sa copy asbox asbare (PointerFree just_bytes)

-- | Rebuild a @Repr a@ term.
packRepr :: Type -> BareInfo -> ExpM
packRepr ty (BareInfo sa copy asbox asbare (PointerFree just_bytes)) =
  conE' (VarCon bareInfo_conV [ty] [])
  [packSizeAlign ty sa, copy, asbox, asbare, just_bytes]

unpackTypeObject :: Type -> ExpM -> Gen BoxInfo
unpackTypeObject ty e = do
  ([], [conid]) <-
    decon (boxInfoV `varApp` [ty]) e
  return $ BoxInfo conid

packTypeObject :: Type -> BoxInfo -> ExpM
packTypeObject ty (BoxInfo conid) =
  conE' (VarCon boxInfo_conV [ty] []) [conid]

unpackLength :: Type -> ExpM -> Gen Length
unpackLength ty e = do
  ([], [x]) <- decon (fiIntV `varApp` [ty]) e
  return $ Length x

packLength :: Type -> Length -> ExpM
packLength ty (Length e) =
  conE' (VarCon fiInt_conV [ty] []) [e]

-------------------------------------------------------------------------------

intL :: Integral a => a -> ExpM
intL n = litE' $ IntL (fromIntegral n) intT

uintL :: Integral a => a -> ExpM
uintL n = litE' $ IntL (fromIntegral n) uintT

fromIntL :: ExpM -> Maybe Integer
fromIntL (ExpM (LitE _ (IntL n (VarT type_var)))) | type_var == intV = Just n
fromIntL _ = Nothing

fromUintL :: ExpM -> Maybe Integer
fromUintL (ExpM (LitE _ (IntL n (VarT type_var)))) | type_var == uintV = Just n
fromUintL _ = Nothing

uintToIntE :: ExpM -> ExpM
uintToIntE e
  | Just x <- fromUintL e = intL x
  | otherwise = varAppE' uintToIntV [] [e]

intToUintE :: ExpM -> ExpM
intToUintE e
  | Just x <- fromIntL e = uintL x
  | otherwise = varAppE' intToUintV [] [e]

-- | Add two integers; evaluate constants immediately if possible
addIE :: ExpM -> ExpM -> ExpM
addIE e1 e2
  | Just x <- fromIntL e1, Just y <- fromIntL e2 = intL (x + y)
  | Just 0 <- fromIntL e1 = e2
  | Just 0 <- fromIntL e2 = e1
  | otherwise = varAppE' addIV [] [e1, e2]

negIE :: ExpM -> ExpM
negIE e
  | Just x <- fromIntL e = intL (negate x)
  | otherwise = varAppE' negateIV [] [e]

-- | Compute the modulus @e1 `mod` e2@.  If possible, the modulus
--   is computed statically.  Expression e2 is assumed to be greater than zero.
modIE_safe :: ExpM -> ExpM -> ExpM
modIE_safe e1 e2
  | Just x <- fromIntL e1, Just y <- fromIntL e2 = intL (x `mod` y)
  -- 0 `mod` x == 0
  | Just 0 <- fromIntL e1 = intL 0
  -- -1 `mod` x == x - 1 for any x > 0
  | Just (-1) <- fromIntL e2 = addIE (intL (-1)) e1
  | otherwise = varAppE' modIV [] [e1, e2]

-- | Take the maximum of two integers
maxUE :: ExpM -> ExpM -> ExpM
maxUE e1 e2
  | Just x <- fromUintL e1, Just y <- fromUintL e2 = uintL (max x y)
  | Just 0 <- fromUintL e1 = e2
  | Just 0 <- fromUintL e2 = e1
  | otherwise = varAppE' maxUV [] [e1, e2]

-- | Take the maximum of two integers.  The integers are assumed to be
--   greater than or equal to 1.
maxUE_1 :: ExpM -> ExpM -> ExpM
maxUE_1 e1 e2
  | Just x <- fromUintL e1, Just y <- fromUintL e2 = uintL (max x y)
  | Just 1 <- fromUintL e1 = e2
  | Just 1 <- fromUintL e2 = e1
  | otherwise = varAppE' maxUV [] [e1, e2]

andIE :: ExpM -> ExpM -> ExpM
andIE e1 e2
  | is_true e1  = e2
  | is_false e1 = e1
  | is_true e2  = e1
  | is_false e2 = e2
  | otherwise   = varAppE' andV [] [e1, e2]
  where
    is_true (ExpM (ConE _ (VarCon c _ _) _)) = c == true_conV
    is_true _ = False

    is_false (ExpM (ConE _ (VarCon c _ _) _)) = c == false_conV
    is_false _ = False

-- negateI, addI, subI, modI
-- addU, subU, modU
-- intToUint, uintToInt

-- | An offset, with type 'int'
newtype Off = Off ExpM

zero :: Off
zero = Off (intL 0)

-- | A size, with type 'uint'
type Sz = ExpM

-- | An alignment, with type 'uint'
type Al = ExpM

instance DefaultValue SizeAlign where dummy = emptySizeAlign

instance DefaultValue Length where dummy = Length (intL 0)

instance DefaultValue PointerFree where
  dummy = PointerFree (conE' (VarCon false_conV [] []) [])

instance DefaultValue ValInfo where dummy = ValInfo dummy dummy

instance DefaultValue BareInfo where
  dummy = BareInfo dummy z z z dummy
    where
      z = intL 0

emptySizeAlign :: SizeAlign
emptySizeAlign = SizeAlign (uintL 0) (uintL 1)

data OffAlign = OffAlign {offsetOff :: !Off, offsetAlign :: !Al}

emptyOffAlign :: OffAlign
emptyOffAlign = OffAlign zero (uintL 1)

-- | Convert an offset and alignment to a size and alignment
offAlignToSize :: OffAlign -> SizeAlign
offAlignToSize (OffAlign (Off o) a) =
  SizeAlign (intToUintE o) a

-- | Round up an offset to the nearest multiple of an alignment
addRecordPadding :: Off -> Al -> Gen Off
addRecordPadding (Off o) a = do
  let disp = modIE_safe (negIE o) (uintToIntE a)
  o' <- emit intT $ addIE o disp
  return $ Off o'

-- | Add an object's size to an offset
addSize :: Off -> Sz -> Gen Off
addSize (Off off) size = do
  off' <- emit intT $ addIE off (uintToIntE size)
  return (Off off')

-- | Add padding to an offset.
--   Return the field offset and the new offset.
padOff :: OffAlign -> SizeAlign -> Gen (Off, OffAlign)
padOff (OffAlign off al) sa = do
  off' <- addRecordPadding off (objectAlign sa)
  off'' <- addSize off' (objectSize sa)
  al' <- emit uintT $ maxUE_1 al (objectAlign sa)
  return (off', OffAlign off'' al')

-- | Add padding to an offset.
--   Return the field offset and the new offset.
padOffMaybe :: OffAlign -> Maybe SizeAlign -> Gen (Maybe Off, OffAlign)
padOffMaybe start_off Nothing = return (Nothing, start_off)
padOffMaybe o (Just sa) = do
  (o', next_off) <- padOff o sa
  return (Just o', next_off)

-- | Compute the size of an array, given the size of an array element.
--   The number of array elements is an @int@.
arraySize :: Length -> SizeAlign -> Gen SizeAlign
arraySize (Length n_elements) (SizeAlign elem_size elem_align) = do
  -- Add padding to each array element
  let off1 = Off (uintToIntE elem_size)
  elem_size <- addRecordPadding off1 elem_align

  -- Multiply by number of elements.  Convert to a size.
  let array_size =
        intToUintE $
        varAppE' mulIV [] [n_elements, case elem_size of Off o -> o]

  return $ SizeAlign array_size elem_align

-- | Compute the size of a data structure consisting of two fields
--   placed consecutively in memory, with padding
abut :: OffAlign -> SizeAlign -> Gen OffAlign
abut o s = do
  (_, o') <- padOff o s
  return o'

-- | Compute the size of a data structure consisting of the given fields
--   placed consecutively in memory, with padding
structSize :: [SizeAlign] -> Gen SizeAlign
structSize xs = offAlignToSize `liftM` foldM abut emptyOffAlign xs

-- | Compute the size and alignment of two overlaid objects
overlay :: SizeAlign -> SizeAlign -> Gen SizeAlign
overlay (SizeAlign s1 a1) (SizeAlign s2 a2) = do
  s <- emit uintT $ maxUE s1 s2
  a <- emit uintT $ maxUE_1 a1 a2
  return $ SizeAlign s a

overlays :: [SizeAlign] -> Gen SizeAlign
overlays (x:xs) = foldM overlay x xs

maxAlignments :: [Al] -> Gen Al
maxAlignments xs = emit uintT $ foldl' maxUE_1 (uintL 1) xs

-- | Compute the logical AND of some boolean expressions
andE :: [ExpM] -> Gen ExpM
andE xs = emit boolT $ foldl' andIE (conE' (VarCon true_conV [] []) []) xs

allPointerFree :: [PointerFree] -> Gen PointerFree
allPointerFree xs = liftM PointerFree $ andE [e | PointerFree e <- xs]

-- | Information about how a field of an object is represented
data FieldInfo = FieldInfo Type !FieldDetails

fiDetails (FieldInfo _ d) = d

-- | Kind-specific information about how a field of an object is represented
data FieldDetails =
    ValDetails ValInfo
  | BareDetails BareInfo
  | BoxDetails

-------------------------------------------------------------------------------

-- | Static type information
type CoreStaticTypeInfo = DynTypeInfo ValInfo BareInfo Length

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
structureSize :: CoreDynTypeInfo
              -> Structure
              -> Gen ValInfo
structureSize type_info layout =
  case layout
  of PrimStruct pt            -> return $ primSize pt
     -- BoolStruct               -> return $ DataLayout BoolD
     -- ArrStruct t ts           -> arrSize type_info t ts
     DataStruct (Data tag fs) -> sumSize type_info tag fs
     ForallStruct fa          -> forall_layout fa
     VarStruct v              -> var_layout v
     UninhabitedStruct        -> internalError "computeLayout: Uninhabited"
  where
    var_layout v = lift $ lookupValTypeInfo type_info v

    forall_layout (Forall b t) = assumeBinder b $ do
      s <- lift $ computeStructure t
      structureSize type_info s

sumSize :: CoreDynTypeInfo -> Boxing -> Alternatives
        -> Gen ValInfo
sumSize _ _ [] =
  internalError "structureSize: Uninhabited type"

sumSize type_info tag alts = do
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

{-arrSize type_info size elem = do
  size_val <- lift $ lookupIntTypeInfo type_info size
  elem_repr <- structureRepr type_info =<< lift (computeStructure elem)
  arraySize size_val (bare_info_size elem_repr)-}

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
  of BoxK -> return BoxDetails
     BareK -> do s <- lift $ computeStructure t
                 r <- structureRepr type_info t s
                 return $ BareDetails r
     ValK -> do s <- lift $ computeStructure t
                r <- structureSize type_info s
                return $ ValDetails r

-------------------------------------------------------------------------------
-- Representations

-- | Dynamic type info
type CoreDynTypeInfo = DynTypeInfo ValInfo BareInfo Length

-- | Compute dynamic type information of a bare data structure
structureRepr :: CoreDynTypeInfo -> Type -> Structure -> Gen BareInfo
structureRepr type_info ty layout =
  case layout
  of DataStruct (Data tag fs) -> sumRepr type_info ty tag fs
     ForallStruct fa          -> forall_layout fa
     VarStruct v              -> var_layout v
     ArrStruct t ts           -> arrRepr type_info t ts
     PrimStruct pt            -> internalError "structureRepr: Unexpected type"
     UninhabitedStruct        -> internalError "structureRepr: Uninhabited"
  where
    continue t l = structureRepr type_info t l

    var_layout v = lift $ lookupBareTypeInfo type_info v

    forall_layout (Forall b t) =
      assumeBinder b $ continue t =<< lift (computeStructure t)

sumRepr type_info ty tag alts = do
  let header_layout = headerSize tag (length alts)

  -- Compute representation info for all constructors
  constructor_info <- mapM (alt_repr header_layout) alts
  let (sizes, reconstructors, pointers) = unzip3 constructor_info

  -- Combine info
  sum_size <- overlays sizes
  pointer_free <- allPointerFree pointers
  copy_fun <- lift $ sumCopyFunction ty reconstructors
  let as_box = varAppE' defaultAsBoxV [ty] []
  let as_bare = varAppE' defaultAsBareV [ty] [copy_fun]
  return $ BareInfo sum_size copy_fun as_box as_bare pointer_free
  where
    -- Compute repr information for one constructor.
    -- The returned tuple contains values for the size, copy, and pointerless 
    -- fields of 'BareInfo'.
    alt_repr :: SizeAlign -> Alternative
             -> Gen (SizeAlign,
                     (Var, [Type] -> [ExpM] -> ExpM),
                     PointerFree)
    alt_repr header_layout (Alternative decon fs) =
      assumeBinders (deConExTypes decon) $ do
        field_info <- mapM (fieldInfo type_info) fs

        size <- let sizes = [fieldDetailsSize d | FieldInfo _ d <- field_info]
                in structSize (header_layout : sizes)

        -- Copy: construct a new object.  Copy fields.
        let copy =
              case decon
              of VarDeCon con ty_args _ ->
                   let f ex_types fields =
                         copyConstructor con ty_args ex_types
                         (zip field_info fields)
                   in (con, f)

        -- Pointerless: logical 'and' of all fields; False if any fields are
        -- boxed
        bytes <- allPointerFree [fieldDetailsPointerFree d | FieldInfo _ d <- field_info]

        return (size, copy, bytes)
        
sumCopyFunction :: Type
                -> [(Var, [Type] -> [ExpM] -> ExpM)]
                -> UnboxedTypeEvalM ExpM
sumCopyFunction ty disjuncts = do
  copy_src <- newAnonymousVar ObjectLevel
  copy_dst <- newAnonymousVar ObjectLevel

  -- Create case expression
  let reconstructor f = \ts es -> return $ appE' (f ts es) [] [varE' copy_dst]
  copy_exp <- assume copy_src ty $ assume copy_dst (AppT outPtrT ty) $
              mkCase ty (varE' copy_src)
              [(v, reconstructor f) | (v, f) <- disjuncts]

  -- Create function
  let copy_fun = FunM $ Fun { funInfo = defaultExpInfo
                            , funTyParams = []
                            , funParams = [patM (copy_src ::: ty),
                                           patM (copy_dst ::: AppT outPtrT ty)]
                            , funReturn = storeT
                            , funBody = copy_exp}

  return $ ExpM $ LamE defaultExpInfo copy_fun

-- | Create a copy of an object.  For bare objects, create an initializer.
copyConstructor :: Var -> [Type] -> [Type] -> [(FieldInfo, ExpM)] -> ExpM
copyConstructor con ty_args ex_types fields =
  conE' (VarCon con ty_args ex_types) (map field_expr fields)
  where
    field_expr (FieldInfo ty details, e) = 
      case details
      of ValDetails _  -> e
         BoxDetails    -> e
         BareDetails d -> appE' (bare_info_copy d) [] [e]

arrRepr :: CoreDynTypeInfo -> Type -> Type -> Gen BareInfo
arrRepr type_info size elem = do
  let array_type = varApp arrV [size, elem]
  size_val <- lift $ lookupIntTypeInfo type_info size
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

-- | Create definitions of the data type's info constructors.
--   One definition is created for unboxed types, or one per data constructor
--   for boxed types.
valInfoDefinition :: DataType -> UnboxedTypeEvalM (GDef Mem)
valInfoDefinition dtype = do
  ent <- typeInfoDefinition dtype $ valInfoDefinition' dtype
  return $ mkDef (unboxedLayoutInfo $ dataTypeLayout' dtype) ent

bareInfoDefinition :: DataType -> UnboxedTypeEvalM (GDef Mem)
bareInfoDefinition dtype = do
  ent <- typeInfoDefinition dtype $ bareInfoDefinition' dtype
  return $ mkDef (unboxedLayoutInfo $ dataTypeLayout' dtype) ent

boxInfoDefinitions :: DataType -> UnboxedTypeEvalM [GDef Mem]
boxInfoDefinitions dtype = forM (dataTypeDataConstructors dtype) $ \c -> do
  Just dcon_type <- lookupDataCon c
  ent <- typeInfoDefinition dtype $ boxInfoDefinition' dtype dcon_type
  return $ mkDef (boxedLayoutInfo (dataTypeLayout' dtype) c) ent

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

-- | Create the type info term for a value type.
--
--   The created term extracts 'SizeAlign' values from all parameters,
--   computes the size of an object, and packages it into a new
--   object.
valInfoDefinition' dtype dyn_info = do
  let ty_args = [VarT v | v ::: _ <- dataTypeParams dtype] 
      ty = dataTypeCon dtype `varApp` ty_args
  sa <- structureSize dyn_info =<< lift (computeStructure ty)
  return $ packReprVal ty sa

-- | Create the type info term for a bare type
bareInfoDefinition' dtype dyn_info = do
  let ty_args = [VarT v | v ::: _ <- dataTypeParams dtype] 
      ty = dataTypeCon dtype `varApp` ty_args
  rep <- structureRepr dyn_info ty =<< lift (computeStructure ty)
  return $ packRepr ty rep

-- | Create the type info term for a boxed type
boxInfoDefinition' dtype con dyn_info = do
  let ty_args = [VarT v | v ::: _ <- dataTypeParams dtype] 
      ty = dataTypeCon dtype `varApp` ty_args
  let rep = BoxInfo (uintL $ dataConIndex con)
  return $ packTypeObject ty rep
