{-| Utilities for lowering data types.
-}
{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleContexts #-}
module SystemF.Datatypes.Util where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import Common.Supply
import Type.Type
import Type.Environment
import LowLevel.CodeTypes
import LowLevel.Build
import qualified LowLevel.Syntax as L
import qualified LowLevel.Print as L

-------------------------------------------------------------------------------
-- Monads for managing unique identifiers and output code

-- | A monad for generating low-level size-computing code.
newtype SizeComputing a =
  SizeComputing (ReaderT (IdentSupply L.Var) (TypeEvalM UnboxedMode) a)
  deriving(Functor, Applicative, Monad, MonadIO)

runSC :: IdentSupply L.Var -> SizeComputing a -> TypeEvalM UnboxedMode a
runSC supply (SizeComputing m) = runReaderT m supply

instance TypeEnvMonad SizeComputing where
  type EvalBoxingMode SizeComputing = UnboxedMode
  getTypeEnv = SizeComputing (lift getTypeEnv)
  {-assumeWithProperties v t b (SizeComputing m) =
    SizeComputing $ ReaderT $ \env ->
    assumeWithProperties v t b $ runReaderT m env-}

instance EvalMonad SizeComputing where
  liftTypeEvalM m = SizeComputing $ lift m

instance Supplies m (Ident Var) => Supplies (Gen m) (Ident Var) where
  fresh = lift fresh

instance EvalMonad m => EvalMonad (Gen m) where
  liftTypeEvalM m = lift (liftTypeEvalM m)

instance Supplies SizeComputing (Ident L.Var) where
  fresh = SizeComputing $ ReaderT $ \env -> liftIO $ supplyValue env

instance Supplies SizeComputing (Ident Var) where
  fresh = SizeComputing $ lift fresh

type GenM a = Gen SizeComputing a

runGenM :: IdentSupply L.Var -> [ValueType] -> GenM (L.Stm, a)
        -> TypeEvalM UnboxedMode (L.Stm, a)
runGenM supply return_types m =
  runSC supply $ execBuild' return_types m

runGenM' :: IdentSupply L.Var -> [ValueType] -> GenM a
         -> TypeEvalM UnboxedMode (a, MkStm)
runGenM' supply return_types m =
  runSC supply $ runGen m return_types

-- | Run a computation, but produce an error if it generates code.
--   This is done in situations where it must be possible to statically
--   compute a data type's size, alignment, or other properties.
--   If code is generated, it represents dynamically computed information.
runGenMWithoutOutput :: IdentSupply L.Var -> GenM a -> TypeEvalM UnboxedMode a
runGenMWithoutOutput supply m = do
  (x, MkStm f) <- runSC supply $ runGen m []

  -- Verify that no code was generated
  case f (L.ReturnE (L.ValA [])) of
    L.ReturnE (L.ValA []) -> return x
    _ -> internalError "runGenMWithoutOutput: Cannot generate code here"

-------------------------------------------------------------------------------
-- Building blocks for generating low-level code

-- | A boolean value, indicating whether a type is free of pointers.
type PointerFree = L.Val

-- | An offset, which is a signed integer value.
newtype Off = Off L.Val

zero :: Off
zero = Off (L.LitV $ L.intL Signed trioletIntSize 0)

-- | A size, which is an unsigned integer value.
type Sz = L.Val

valueSize :: ValueType -> Sz
valueSize ty = nativeWordV $ sizeOf ty

-- | An alignment, which is an unsigned integer value.
type Al = L.Val

valueAlign :: ValueType -> Al
valueAlign ty = nativeWordV $ alignOf ty

valuePointerfree :: ValueType -> PointerFree
valuePointerfree ty = booleanV $ pointerlessness ty

-- | A size and alignment.  Both values are unsigned integers.
data SizeAlign = SizeAlign { objectSize :: !Sz
                           , objectAlign :: !Al
                           , objectPointerfree :: !PointerFree}

emptySizeAlign :: SizeAlign
emptySizeAlign = SizeAlign (nativeWordV 0) (nativeWordV 1) (booleanV True)

valueSizeAlign :: ValueType -> SizeAlign
valueSizeAlign ty =
  SizeAlign (valueSize ty) (valueAlign ty) (valuePointerfree ty)

-- | An offset and alignmnent.  Offset is signed.  Alignment is unsigned.
data OffAlign = OffAlign { offsetOff :: !Off
                         , offsetAlign :: !Al
                         , offsetPointerfree :: !PointerFree}

emptyOffAlign :: OffAlign
emptyOffAlign = OffAlign (Off (nativeIntV 0)) (nativeWordV 1) (booleanV True)

-- | Convert an offset and alignment to a size and alignment.
offAlignToSize :: OffAlign -> GenM SizeAlign
offAlignToSize (OffAlign (Off o) a pf) = do
  -- Convert offset to an unsigned value
  s <- primCastZ (PrimType nativeWordType) o
  return $ SizeAlign s a pf

-- | Add padding to an offset.
--   Return the field offset and the new offset.
padOff :: OffAlign -> SizeAlign -> GenM (Off, OffAlign)
padOff (OffAlign (Off off) al pf) sa = do
  off' <- addRecordPadding off (objectAlign sa)
  off'' <- addSize (Off off') (objectSize sa)
  al' <- nativeMaxUZ al (objectAlign sa)
  pf' <- primAnd pf (objectPointerfree sa)
  return (Off off', OffAlign off'' al' pf')

-- | Compute offsets of a sequence of objects.
padOffs :: OffAlign -> [SizeAlign] -> GenM ([Off], OffAlign)
padOffs start sas = go id start sas
  where
    go hd off (sa:sas) = do
      (sa_off, next_off) <- padOff off sa
      go (hd . (sa_off:)) next_off sas

    go hd off [] = return (hd [], off)

-- | Add padding to an offset, only if a 'Just' argument is given.
padOffMaybe :: OffAlign -> Maybe SizeAlign -> GenM (Maybe Off, OffAlign)
padOffMaybe start_off Nothing =
  return (Nothing, start_off)

padOffMaybe start_off (Just sa) = do
  (o, next_off) <- padOff start_off sa
  return (Just o, next_off)

-- | Add an object's size to an offset
addSize :: Off -> Sz -> GenM Off
addSize (Off off) size = do
  off' <- nativeAddZ off =<< primCastZ (PrimType trioletIntType) size
  return (Off off')

-- | Compute the size of an array
arraySize :: L.Val -> SizeAlign -> GenM SizeAlign
arraySize n_elements (SizeAlign elem_size elem_align elem_pf) 
  | L.valType n_elements /= PrimType nativeIntType =
    traceShow (L.pprVal n_elements $$ L.pprVal elem_size $$ L.pprVal elem_align) $
    internalError "arraySize: Number of elements has wrong type"

  | otherwise = do
    -- The size of one array element is the element size,
    -- plus any necessary padding
    size1 <- primCastZ (PrimType nativeIntType) elem_size
    size2 <- addRecordPadding size1 elem_align

    -- Multiply by number of elements
    size3 <- nativeMulUZ size2 =<< primCastZ (PrimType nativeWordType) n_elements

    return $ SizeAlign size3 elem_align elem_pf

-- | Compute the size and alignment of two overlaid objects
overlay :: SizeAlign -> SizeAlign -> GenM SizeAlign
overlay (SizeAlign s1 a1 pf1) (SizeAlign s2 a2 pf2) =
  liftM3 SizeAlign (nativeMaxUZ s1 s2) (nativeMaxUZ a1 a2) (primAnd pf1 pf2)

overlays :: [SizeAlign] -> GenM SizeAlign
overlays (x:xs) = foldM overlay x xs

maxAlignments :: [Al] -> GenM Al
maxAlignments xs = foldM nativeMaxUZ (nativeWordV 1) xs

-------------------------------------------------------------------------------
-- Code generation for tag operations

-- | Determine the tag type to use for an enumerative type of @n@ constructors
--   when the tag is held in a local variable
unboxedEnumVarTagType :: Int -> PrimType
unboxedEnumVarTagType n
  | n == 0    = internalError "unboxedEnumVarTagType: Uninhabited type"
  | n == 1    = UnitType
  | otherwise = nativeWordType

-- | Determine the tag type to use for an enumerative type of @n@ constructors
--   when the tag is held in memory
unboxedEnumMemTagType :: Int -> PrimType
unboxedEnumMemTagType n
  | n == 0     = internalError "unboxedEnumMemTagType: Uninhabited type"
  | n == 1     = UnitType
  | n <= 256   = IntType Unsigned S8
  | n <= 65536 = IntType Unsigned S16
  | otherwise  = nativeWordType

-- | Determine the tag type to use for a product or sum type of @n@
--   constructors when the tag is held in a local variable
unboxedVarTagType :: Int -> Maybe PrimType
unboxedVarTagType n
  | n == 1    = Nothing
  | otherwise = Just $! unboxedEnumVarTagType n

unboxedMemTagType :: Int -> Maybe PrimType
unboxedMemTagType n
  | n == 1    = Nothing
  | otherwise = Just $! unboxedEnumMemTagType n

{-
-- | Determine the tag type to use for a sum type of @n@ constructors.
--   Note that the 'Bool' type is a special case not described by this
--   function.
tagType :: Int -> Maybe PrimType
tagType n 
  | n == 0     = internalError "disjunctsTag: Uninhabited type"
  | n == 1     = Nothing
  | n <= 256   = Just $ IntType Unsigned S8
  | n <= 65536 = Just $ IntType Unsigned S16
  | otherwise  = Just $ IntType Unsigned S32
-}

-- | Create the tag value an unboxed type, given its tag type
unboxedTagLit :: ValueType -> Int -> L.Lit
unboxedTagLit (PrimType (IntType sz al)) n = L.IntL sz al (fromIntegral n)
unboxedTagLit (PrimType UnitType) 0 = L.UnitL
unboxedTagLit _ _ = internalError "unboxedTagLit: Unexpected type"

{-
-- | Create the tag value for a value type, given its low-level tag type
tagLit :: ValueType -> Int -> L.Lit
tagLit (PrimType (IntType sz al)) n = L.IntL sz al (fromIntegral n)
tagLit (PrimType UnitType)        0 = L.UnitL
tagLit pt                          n = traceShow (L.pprValueType pt) $ traceShow n $ internalError "tagLit: Unexpected type"
-}

-- | Create the tag value for a value type, given its low-level tag type
unboxedTagValue :: ValueType -> Int -> L.Val
unboxedTagValue t n = L.LitV $ unboxedTagLit t n

-- | Create an expression to inspect a tag and execute one of several 
--   code branches depending on the tag value.
tagDispatch :: ValueType        -- ^ Tag type
            -> L.Val            -- ^ Tag value
            -> [GenM L.Stm]     -- ^ Branches, in the same order as tags
            -> GenM L.Stm   -- ^ Emit code that produces return values
tagDispatch tag_type tag branches = do
  return_types <- getReturnTypes
  branch_stms <- lift $ mapM (mk_branch return_types) (zip [0..] branches)
  return $ L.SwitchE tag branch_stms
  where
    mk_branch return_types (index, mk_body) = do
      body <- execBuild return_types mk_body
      return (unboxedTagLit tag_type index, body)

-- | Create an expression to inspect a tag and execute one of several 
--   code branches depending on the tag value.
--
--   This function should eventually replace the old one.
tagDispatch2 :: ValueType        -- ^ Tag type
             -> Int              -- ^ Number of tags
             -> L.Val            -- ^ Tag value
             -> [ValueType]      -- ^ Return types of branches
             -> (Int -> GenM L.Val) -- ^ Branches, indexed by constructor
             -> GenM L.Val  -- ^ Emit code that produces return values
tagDispatch2 tag_type num_tags tag branch_return_types branches = do
  let branches' i = fmap return $ branches i -- Return a singleton list
  [x] <- genSwitch branch_return_types tag
         [(unboxedTagLit tag_type i, branches' i) | i <- [0..num_tags-1]]
  return x

-------------------------------------------------------------------------------
-- Other utility functions

-- | Create an arbitrary value of the given type.
--   The value should not affect the program behavior (usually because
--   the value isn't used).
dummyValue (PrimType UnitType)      = L.LitV L.UnitL
dummyValue (PrimType BoolType)      = L.LitV (L.BoolL False)
dummyValue (PrimType (IntType s z)) = L.LitV (L.IntL s z 0)
dummyValue (PrimType (FloatType z)) = L.LitV (L.FloatL z 0)
dummyValue (PrimType OwnedType)     = L.LitV L.NullRefL
dummyValue (PrimType PointerType)   = L.LitV L.NullL
dummyValue (RecordType r) =
  L.RecV r $ map (dummyFieldValue . fieldType) $ recordFields r

dummyFieldValue :: StaticFieldType -> L.Val
dummyFieldValue (PrimField t)   = dummyValue (PrimType t)
dummyFieldValue (RecordField r) = dummyValue (RecordType r)

-- | If the given parameter list is empty, return a dummy parameter
addDummyParameterValue :: [L.Val] -> [L.Val]
addDummyParameterValue [] = [L.LitV L.UnitL]
addDummyParameterValue xs = xs

-- | If the given parameter list is empty, return a dummy parameter
addDummyParameterType :: [ValueType] -> [ValueType]
addDummyParameterType [] = [PrimType UnitType]
addDummyParameterType xs = xs

-- | A call to a continuation function.
--   If no arguments are given, then pass a unit value as the argument.
continuationCall :: L.Val -> [L.Val] -> L.Stm
continuationCall callee args =
  L.ReturnE $ continuationCall2 callee args

-- | A call to a continuation function.
--   If no arguments are given, then pass a unit value as the argument.
continuationCall2 :: L.Val -> [L.Val] -> L.Atom
continuationCall2 callee args =
  L.closureCallA callee $ addDummyParameterValue args

