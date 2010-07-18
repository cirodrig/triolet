
{-# LANGUAGE ViewPatterns, Rank2Types, FlexibleInstances #-}
module Pyon.LowLevel.Build where

import Control.Monad
import Control.Monad.Writer
import Control.Monad.ST

import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.Supply
import Gluon.Core(Con(..))
import Pyon.SystemF.Builtins
import Pyon.LowLevel.Syntax
import Pyon.LowLevel.Types
import Pyon.LowLevel.Record

newtype FreshVarM a = FreshVarM (forall st. IdentSupply Var -> ST st a)

type MakeExp = FreshVarM Stm
type BuildBlock a = WriterT [Stm] FreshVarM a

execBuild :: BuildBlock Atom -> FreshVarM Block
execBuild m = do (atom, stms) <- runWriterT m
                 return $ Block stms atom

-- | Build a block for use in a larger expression
getBlock :: BuildBlock Atom -> BuildBlock Block
getBlock m = WriterT $ do
  block <- execBuild m
  return (block, [])

instance Functor FreshVarM where
  fmap f (FreshVarM g) = FreshVarM (\supply -> fmap f (g supply))

instance Monad FreshVarM where
  return x = FreshVarM (\_ -> return x)
  FreshVarM f >>= k = FreshVarM (\supply -> do
                                    x <- f supply
                                    case k x of FreshVarM g -> g supply)

instance Supplies FreshVarM (Ident Var) where
  fresh = FreshVarM (\x -> unsafeIOToST (supplyValue x))
  supplyToST f = FreshVarM (\x -> let get_fresh = unsafeIOToST (supplyValue x)
                                  in f get_fresh)

-------------------------------------------------------------------------------
-- Generating primops

-- | Generate an instruction that has no result value
emitAtom0 :: Atom -> BuildBlock ()
emitAtom0 atom = tell [LetE [] atom]

emitAtom1 :: ValueType -> Atom -> BuildBlock Val
emitAtom1 ty atom = do
  tmpvar <- lift $ newAnonymousVar ty
  tell [LetE [tmpvar] atom]
  return $ VarV tmpvar

bindAtom0 :: Atom -> BuildBlock ()
bindAtom0 = emitAtom0

bindAtom1 :: Var -> Atom -> BuildBlock ()
bindAtom1 var atom = tell [LetE [var] atom]

-- | Generate a binary primitive integer operation
intBinaryPrimOp :: (Integer -> Integer -> Integer) -- ^ Unlifted operation
                -> Maybe Integer                   -- ^ Left identity value
                -> Maybe Integer                   -- ^ Right identity value
                -> (Signedness -> Size -> Prim)    -- ^ Primitive operation
                -> ValueType                       -- ^ Type to generate
                -> Val                             -- ^ Left argument
                -> Val                             -- ^ Right argument
                -> BuildBlock Val                    -- ^ Result value
intBinaryPrimOp imm_op l_id r_id delayed_op prim_type m n =
  case prim_type
  of PrimType (IntType sign size) ->
       case (m, n)
       of -- Apply algebraic identities if possible
          (fromLit -> Just m_imm, _) | l_id == Just m_imm -> return n
          (_, fromLit -> Just n_imm) | r_id == Just n_imm -> return m
          
          -- Evaluate statically if both values are available
          (LitV (IntL _ _ m_imm), LitV (IntL _ _ n_imm)) ->
            return $ LitV (IntL sign size (imm_op m_imm n_imm))

          -- Otherwise generate code to compute the value
          _ -> emitAtom1 prim_type $ PrimA (delayed_op sign size) [m, n]
  where
    fromLit (LitV (IntL _ _ n)) = Just n
    fromLit _ = Nothing

primAddZ = intBinaryPrimOp (+) (Just 0) (Just 0) PrimAddZ
primSubZ = intBinaryPrimOp (-) (Just 0) (Just 0) PrimSubZ
primModZ = intBinaryPrimOp mod Nothing (Just 1) PrimModZ
primMaxZ = intBinaryPrimOp max Nothing Nothing PrimMaxZ

primNegateZ prim_type@(PrimType (IntType sign size)) n =
  primSubZ prim_type (LitV $ IntL sign size 0) n

primAddP ptr off = emitAtom1 (PrimType PointerType) $ PrimA PrimAddP [ptr, off]
primLoad ty ptr dst = bindAtom1 dst $ PrimA (PrimLoad ty) [ptr]
primLoadOff ty ptr off dst = do
  ptr' <- primAddP ptr off 
  primLoad ty ptr' dst

primStore ty ptr val = emitAtom0 $ PrimA (PrimStore ty) [ptr, val]
primStoreOff ty ptr off val = do
  ptr' <- primAddP ptr off
  primStore ty ptr' val

nativeAddUZ = primAddZ (PrimType nativeWordType)
nativeSubUZ = primSubZ (PrimType nativeWordType)
nativeModUZ = primModZ (PrimType nativeWordType)
nativeMaxUZ = primMaxZ (PrimType nativeWordType)
nativeNegateUZ = primNegateZ (PrimType nativeWordType)

nativeWordL :: Integral a => a -> Lit
nativeWordL n = IntL Unsigned nativeIntSize (fromIntegral n)

nativeWordV :: Integral a => a -> Val
nativeWordV n = LitV $ nativeWordL n

-------------------------------------------------------------------------------
-- Record operations

-- | Unpack a pass-by-value record
unpackRecord :: StaticRecord -> Val -> BuildBlock [Var]
unpackRecord rtype val = do
  -- Create a variable to hold each field value
  vars <- lift $ mapM newFieldVar $ recordFields rtype
  
  -- Create an 'unpack' expression
  tell [LetE vars $ UnpackA rtype val]
  return vars
  where
    newFieldVar sfield = 
      case fieldType sfield
      of PrimField vtype -> newAnonymousVar (PrimType vtype)
         BytesField {} -> internalError "unpackRecord"

-- | Select one field of a pass-by-value record
selectField :: StaticRecord -> Int -> Val -> BuildBlock Var
selectField ty index val = do
  fields <- unpackRecord ty val
  return $ fields !! index

toDynamicRecord :: StaticRecord -> DynamicRecord
toDynamicRecord rec = let
  fs = map toDynamicField $ recordFields rec
  size = nativeWordV $ recordSize rec
  alignment = nativeWordV $ recordAlignment rec
  in record fs size alignment

toDynamicField :: StaticField -> DynamicField
toDynamicField (Field off ty) =
  Field (nativeWordV off) (toDynamicFieldType ty)

toDynamicFieldType :: StaticFieldType -> DynamicFieldType
toDynamicFieldType (PrimField t) = PrimField t
toDynamicFieldType (RecordField p rec) = RecordField p $ toDynamicRecord rec
toDynamicFieldType (BytesField s a) =
      BytesField (nativeWordV s) (nativeWordV a)

dynamicFieldSize :: DynamicField -> Val
dynamicFieldSize f = dynamicFieldTypeSize $ fieldType f

dynamicFieldAlignment :: DynamicField -> Val
dynamicFieldAlignment f = dynamicFieldTypeAlignment $ fieldType f

dynamicFieldTypeSize :: DynamicFieldType -> Val
dynamicFieldTypeSize ft =
  case ft
  of PrimField vt   -> nativeWordV $ sizeOf vt
     RecordField _ r -> recordSize r
     BytesField s _  -> s

dynamicFieldTypeAlignment :: DynamicFieldType -> Val
dynamicFieldTypeAlignment ft = 
  case ft
  of PrimField vt   -> nativeWordV $ alignOf vt
     RecordField _ r -> recordAlignment r
     BytesField _ a  -> a

-- | Create a dynamic record.  Given the record field types, the offsets of
-- all fields are computed and returned.  Code is emitted to compute the
-- offsets.
createDynamicRecord :: [DynamicFieldType] -> BuildBlock DynamicRecord
createDynamicRecord field_types = do
  -- Compute record size and field offsets
  (offsets, size, alignment) <- compute_offsets [] zero one field_types
  
  -- Create the record
  let fields = zipWith Field offsets field_types
  return $ record fields size alignment
  where
    zero = nativeWordV 0
    one = nativeWordV 1

    -- Compute offsets of one structure field.  First,
    -- add padding bytes to reach a suitable alignment; this is the field's
    -- offset.  Then add in the size of the field to get the next free offset.
    -- The alignment is the maximum alignment of all fields (must be a power
    -- of 2).
    compute_offsets :: [Val] -> Val -> Val -> [DynamicFieldType]
                    -> BuildBlock ([Val], Val, Val)
    compute_offsets offsets cur_offset cur_align (field:fields) = do
      start_offset <- addRecordPadding cur_offset $
                      dynamicFieldTypeAlignment field
      end_offset <- nativeAddUZ start_offset $ dynamicFieldTypeSize field
      next_align <- nativeMaxUZ cur_align $ dynamicFieldTypeAlignment field
      compute_offsets (start_offset : offsets) end_offset next_align fields

    compute_offsets offsets cur_offset cur_align [] = do
      -- Add padding to end of structure
      end_offset <- addRecordPadding cur_offset cur_align
      return (reverse offsets, end_offset, cur_align)

-- | Compute the necessary record padding for a given offset
addRecordPadding :: Val -> Val -> BuildBlock Val
addRecordPadding off alignment = do
  neg_off <- nativeNegateUZ off 
  disp <- neg_off `nativeModUZ` alignment
  off `nativeAddUZ` disp

-- | Load one field of a record into a local variable
loadFieldAs :: DynamicRecord -> Val -> Int -> Var -> BuildBlock ()
loadFieldAs rtype ptr index dst =
  let field = recordFields rtype !! index 
      off = fieldOffset field
      ty = case fieldType field
           of PrimField ty -> PrimType ty
              _ -> internalError "loadField: Only implemented for primitive types"
  in primLoadOff ty ptr off dst

-------------------------------------------------------------------------------
-- Other operations

-- | Allocate temporary local memory over the scope of some computation.
--   The allocated memory is not initialized, and must be initialized by 
--   the given code generator.
allocateLocalObject :: Var      -- ^ Pointer that will reference the object
                    -> Val      -- ^ Passing convention of object
                    -> [ValueType] -- ^ Return type(s) of the generated code
                    -> BuildBlock Atom -- ^ Code generator
                    -> BuildBlock Atom
allocateLocalObject ptr_var pass_conv rtypes mk_block = do
  -- Allocate the object
  size <- selectPassConvSize pass_conv
  bindAtom1 ptr_var $ PrimCallA (ConV (pyonBuiltin the_prim_alloc)) [VarV size]
  
  -- Generate code and bind its results to temporary variables
  rvars <- lift $ mapM newAnonymousVar rtypes
  ret_atom <- mk_block
  tell [LetE rvars ret_atom]
  
  -- Free the object
  free <- selectPassConvFree pass_conv
  bindAtom0 $ PrimCallA (VarV free) [VarV ptr_var]
  
  -- Return the temporary values
  return $ ValA $ map VarV rvars

-------------------------------------------------------------------------------

-- | A parameter passing convention consists of size, alignment, copy,
-- and free functions
passConvRecord :: StaticRecord
passConvRecord = staticRecord [ PrimField nativeWordType
                              , PrimField nativeWordType
                              , PrimField OwnedType
                              , PrimField OwnedType
                              ]

selectPassConvSize, selectPassConvAlignment,
  selectPassConvCopy, selectPassConvFree :: Val -> BuildBlock Var
selectPassConvSize = selectField passConvRecord 0
selectPassConvAlignment = selectField passConvRecord 1
selectPassConvCopy = selectField passConvRecord 2
selectPassConvFree = selectField passConvRecord 3

passConvValue :: Int -> Int -> Con -> Con -> Val
passConvValue size align copy free =
  RecV passConvRecord
  [ LitV $ IntL Unsigned S32 (fromIntegral size)
  , LitV $ IntL Unsigned S32 (fromIntegral align)
  , ConV copy
  , ConV free
  ]

intPassConvValue :: Val
intPassConvValue =
  passConvValue 4 4 (pyonBuiltin the_prim_copy_int) (pyonBuiltin the_prim_free)

