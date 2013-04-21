
module SystemF.Datatypes.Code where

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
import Type.Type
import Type.Environment
import Type.Eval

-- | Dynamic type info
type CoreDynTypeInfo = DynTypeInfo ValInfo BareInfo Length

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

-- | A boolean value, indicating whether a data structure doesn't
--   contain pointers to heap objects.
--   'True' means the structure has no pointers.
newtype PointerFree = PointerFree ExpM

isPointerFree, notPointerFree :: PointerFree
isPointerFree = PointerFree (valConE' (VarCon true_conV [] []) [])
notPointerFree = PointerFree (valConE' (VarCon false_conV [] []) [])

-- | A GADT indicating whether a data type is of the form 'Ref t'.
newtype IsRef = IsRef ExpM

-- | The unpacked fields of a 'TypeObject' object
data BoxInfo =
  BoxInfo
  { box_info_conid :: !ExpM    -- An unsigned integer
  }

-- | The unpacked fields of a 'Repr' object
data BareInfo =
  BareInfo 
  { bare_info_size     :: !SizeAlign 
  , bare_info_pointers :: !PointerFree
  , bare_info_isref    :: !IsRef
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

-- | Run a @Gen (Maybe ExpM)@; raise an exception if it returns 'Nothing'
runMaybeGen :: Gen (Maybe ExpM) -> UnboxedTypeEvalM ExpM
runMaybeGen m = do (mx, MkExp f) <- runWriterT m
                   case mx of
                     Nothing -> internalError "runMaybeGen"
                     Just x -> return $ f x

execGen :: Gen a -> UnboxedTypeEvalM (a, ExpM -> ExpM)
execGen m = do (x, MkExp f) <- runWriterT m
               return (x, f)

-- | Bind an expression's result to a variable.
--
--   This is done when an expression may be used multiple times, 
--   to avoid introducing redundant work.
emit :: Type -> ExpM -> Gen ExpM

-- Don't bind literals, variables, or nullary constructors to variables
emit ty rhs@(ExpM (VarE {})) = return rhs
emit ty rhs@(ExpM (LitE {})) = return rhs
emit ty rhs@(ExpM (ConE _ (VarCon _ [] []) [] Nothing [])) = return rhs

emit ty rhs = do
  v <- lift $ newAnonymousVar ObjectLevel
  tell $ MkExp (\body -> ExpM $ LetE defaultExpInfo (patM (v ::: ty)) rhs body)
  return (varE' v)

-- | Deconstruct a single-constructor type whose representation doesn't
--   depend on the type constructor's type arguments.
--   Return the existential types and field types.
decon :: Type -> ExpM -> Gen ([Var], [ExpM])
decon prod_type scrutinee = do
  (decon_inst, ty_ob_type, field_types) <- lift $ do
    -- Get data constructor type
    Just (tycon, ty_args) <- deconVarAppType prod_type
    Just data_type <- lookupDataType tycon
    let [data_con] = dataTypeDataConstructors data_type
    Just data_con_type <- lookupDataCon data_con

    -- Instantiate the type
    (ex_binders, field_types, _) <-
      instantiateDataConTypeWithFreshVariables data_con_type ty_args

    -- Get the type of the type object
    let ty_ob_type =
          case dataTypeKind data_type
          of BoxK -> Just $ boxInfoV `varApp` [prod_type]
             _ -> Nothing

    let decon_inst = VarDeCon data_con ty_args ex_binders
    return (decon_inst, ty_ob_type, field_types)

  ty_ob_pat <- lift $
    case ty_ob_type
    of Nothing -> return Nothing
       Just t  -> do v <- newAnonymousVar ObjectLevel
                     return $ Just $ patM (v ::: t)

  field_binders <- lift $ forM field_types $ \t -> do
    v <- newAnonymousVar ObjectLevel
    return $ patM (v ::: t)
  
  -- Create the case expression
  let mk_case body =
        ExpM $ CaseE defaultExpInfo scrutinee []
        [AltM $ Alt decon_inst ty_ob_pat field_binders body]
  tell (MkExp mk_case)

  let ex_vars = map binderVar $ deConExTypes decon_inst
      fields = map (varE' . patMVar) field_binders
  return (ex_vars, fields)

-- | Create a case expression to deconstruct a multiple-constructor type
--   whose representation doesn't depend on the type constructor's type
--   arguments.
--   Handle the alternatives in-place.
mkCase :: Type
       -> ExpM
       -> [ExpM]
       -> [(Var, [Type] -> [ExpM] -> UnboxedTypeEvalM ExpM)]
       -> UnboxedTypeEvalM ExpM
mkCase ty scrutinee size_params alt_handlers = do
    -- Get data constructor type
    Just (tycon, ty_args) <- deconVarAppType ty
    Just data_type <- lookupDataType tycon

    -- This function doesn't handle boxed types properly
    when (dataTypeKind data_type == BoxK) $
      internalError "mkCase"

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
        
      return $ AltM $ Alt decon Nothing field_binders body

    -- Build case expression
    return $ ExpM $ CaseE defaultExpInfo scrutinee size_params alts

-- | Extract the fields of a @SizeAlignVal a@ term.
unpackSizeAlignVal :: Type -> ExpM -> Gen SizeAlign
unpackSizeAlignVal ty e = do
  ([], [s, a]) <- decon (sizeAlignValV `varApp` [ty]) e
  return $ SizeAlign s a

-- | Construct a @SizeAlignVal a@ term.
packSizeAlignVal :: Type -> SizeAlign -> ExpM
packSizeAlignVal ty (SizeAlign s a) =
  valConE' (VarCon sizeAlignVal_conV [ty] []) [s, a]

-- | Extract the fields of a @ReprVal a@ term.
unpackReprVal :: Type -> ExpM -> Gen ValInfo
unpackReprVal ty e = do
  ([], [sa, p]) <- decon (valInfoV `varApp` [ty]) e
  sa' <- unpackSizeAlignVal ty sa
  return $ ValInfo sa' (PointerFree p)

-- | Construct a @SizeAlignVal a@ term.
packReprVal :: Type -> ValInfo -> ExpM
packReprVal ty (ValInfo sa (PointerFree p)) =
  let con = VarCon valInfo_conV [ty] []
      ty_obj = varAppE' boxInfo_valInfoV [ty] []
  in conE' con [] (Just ty_obj) [packSizeAlignVal ty sa, p]

-- | Extract the fields of a @SizeAlign a@ term.
unpackSizeAlign :: Type -> ExpM -> Gen SizeAlign
unpackSizeAlign ty e = do
  ([], [s, a]) <- decon (sizeAlignV `varApp` [ty]) e
  return $ SizeAlign s a

-- | Construct a @SizeAlign a@ term.
packSizeAlign :: Type -> SizeAlign -> ExpM
packSizeAlign ty (SizeAlign s a) =
  valConE' (VarCon sizeAlign_conV [ty] []) [s, a]

-- | Extract the fields of a @Repr a@ term.
unpackRepr :: Type -> ExpM -> Gen BareInfo
unpackRepr ty e = do
  ([], [size_align, just_bytes, is_ref]) <-
    decon (bareInfoV `varApp` [ty]) e
  sa <- unpackSizeAlign ty size_align
  return $ BareInfo sa (PointerFree just_bytes) (IsRef is_ref)

-- | Rebuild a @Repr a@ term.
packRepr :: Type -> BareInfo -> ExpM
packRepr ty (BareInfo sa (PointerFree just_bytes) (IsRef is_ref)) =
  let con = VarCon bareInfo_conV [ty] []
      ty_obj = varAppE' boxInfo_bareInfoV [ty] []
  in conE' con [] (Just ty_obj)
     [packSizeAlign ty sa, just_bytes, is_ref]

unpackTypeObject :: Type -> ExpM -> Gen BoxInfo
unpackTypeObject ty e = do
  ([], [conid]) <-
    decon (boxInfoV `varApp` [ty]) e
  return $ BoxInfo conid

packTypeObject :: Type -> BoxInfo -> ExpM
packTypeObject ty (BoxInfo conid) =
  let con = VarCon boxInfo_conV [ty] []
      ty_obj = varAppE' boxInfo_boxInfoV [ty] []
  in conE' con [] (Just ty_obj) [conid]

unpackLength :: Type -> ExpM -> Gen Length
unpackLength ty e = do
  ([], [x]) <- decon (fiIntV `varApp` [ty]) e
  return $ Length x

packLength :: Type -> Length -> ExpM
packLength ty (Length e) =
  valConE' (VarCon fiInt_conV [ty] []) [e]

-- | Convert an expression into a lambda term @(\x : NoneType. E)@.
lazyExp :: Type -> ExpM -> Gen ExpM
lazyExp return_type e = do
  v <- lift $ newAnonymousVar ObjectLevel
  let params = [patM (v ::: noneTypeT)]
      f = FunM $ Fun defaultExpInfo [] params return_type e
  return $ ExpM $ LamE defaultExpInfo f

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
    is_true (ExpM (ConE {expCon = VarCon c _ _})) = c == true_conV
    is_true _ = False

    is_false (ExpM (ConE {expCon = VarCon c _ _})) = c == false_conV
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
  dummy = PointerFree (falseE defaultExpInfo)

instance DefaultValue IsRef where
  dummy = IsRef (falseE defaultExpInfo) -- Not well-typed

instance DefaultValue ValInfo where dummy = ValInfo dummy dummy

instance DefaultValue BareInfo where
  dummy = BareInfo dummy dummy dummy
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
andE xs = emit boolT $ foldl' andIE (valConE' (VarCon true_conV [] []) []) xs

allPointerFree :: [PointerFree] -> Gen PointerFree
allPointerFree xs = liftM PointerFree $ andE [e | PointerFree e <- xs]
