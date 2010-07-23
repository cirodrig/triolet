
{-# LANGUAGE ViewPatterns, FlexibleInstances, FlexibleContexts, NoMonomorphismRestriction, ScopedTypeVariables #-}
module Pyon.LowLevel.Build where

import Control.Monad
import Control.Monad.Writer

import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.Supply
import Gluon.Core(Con(..))
import Pyon.LowLevel.Builtins
import Pyon.LowLevel.FreshVar
import Pyon.LowLevel.Syntax
import Pyon.LowLevel.Types
import Pyon.LowLevel.Record

type Gen m a = WriterT [Stm] m a

execBuild :: Monad m => Gen m Atom -> m Block
execBuild m = do (atom, stms) <- runWriterT m
                 return $ Block stms atom

-- | Build a block for use in a larger expression
getBlock :: Monad m => Gen m Atom -> Gen m Block
getBlock m = WriterT $ do
  block <- execBuild m
  return (block, [])

putBlock :: Monad m => Block -> Gen m Atom
putBlock (Block stms atom) = WriterT $ return (atom, stms)

-------------------------------------------------------------------------------
-- Generating primops

-- | Generate an instruction that has no result value
emitAtom0 :: Monad m => Atom -> Gen m ()
emitAtom0 atom = tell [LetE [] atom]

emitAtom1 :: (Monad m, Supplies m (Ident Var)) =>
             ValueType -> Atom -> Gen m Val
emitAtom1 ty atom = do
  tmpvar <- lift $ newAnonymousVar ty
  tell [LetE [tmpvar] atom]
  return $ VarV tmpvar

emitAtom :: (Monad m, Supplies m (Ident Var)) =>
            [ValueType] -> Atom -> Gen m [Val]
emitAtom tys atom = do
  tmpvars <- lift $ mapM newAnonymousVar tys
  tell [LetE tmpvars atom]
  return $ map VarV tmpvars

bindAtom0 :: Monad m => Atom -> Gen m ()
bindAtom0 = emitAtom0

bindAtom1 :: Monad m => Var -> Atom -> Gen m ()
bindAtom1 var atom = tell [LetE [var] atom]

bindAtom :: Monad m => [Var] -> Atom -> Gen m ()
bindAtom vars atom = tell [LetE vars atom]

genIf :: Monad m => Val -> Gen m Atom -> Gen m Atom -> Gen m Atom
genIf bool if_true if_false = do
  true_block <- getBlock if_true
  false_block <- getBlock if_false
  return $ SwitchA bool [ (BoolL True, true_block)
                        , (BoolL False, false_block)]

builtinVar :: (LowLevelBuiltins -> Var) -> Val
builtinVar v = VarV $ llBuiltin v

genPrimFun :: Monad m => [ParamVar] -> [ValueType] -> Gen m Atom -> Gen m Fun
genPrimFun params returns body =
  liftM (Fun True params returns) $ getBlock body

genClosureFun :: Monad m =>
                 [ParamVar] -> [ValueType] -> Gen m Atom -> Gen m Fun
genClosureFun params returns body =
  liftM (Fun False params returns) $ getBlock body

-- | Generate a binary primitive integer operation
intBinaryPrimOp :: (Monad m, Supplies m (Ident Var)) =>
                   (Integer -> Integer -> Integer) -- ^ Unlifted operation
                -> Maybe Integer                   -- ^ Left identity value
                -> Maybe Integer                   -- ^ Right identity value
                -> (Signedness -> Size -> Prim)    -- ^ Primitive operation
                -> ValueType                       -- ^ Type to generate
                -> Val                             -- ^ Left argument
                -> Val                             -- ^ Right argument
                -> Gen m Val                       -- ^ Result value
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

primCmpZ prim_type@(PrimType (IntType sign size)) comparison x y =
  emitAtom1 prim_type $ PrimA (PrimCmpZ sign size comparison) [x, y]

primAddP ptr off =
  emitAtom1 (PrimType PointerType) $ PrimA PrimAddP [ptr, off]

primLoad ty ptr dst = bindAtom1 dst $ PrimA (PrimLoad ty) [ptr]
primLoadOff ty ptr off dst = do
  ptr' <- primAddP ptr off 
  primLoad ty ptr' dst

primStore ty ptr val = emitAtom0 $ PrimA (PrimStore ty) [ptr, val]
primStoreOff ty ptr off val = do
  ptr' <- primAddP ptr off
  primStore ty ptr' val

primAAddZ prim_type@(PrimType (IntType sign size)) ptr n =
  emitAtom1 prim_type $ PrimA (PrimAAddZ sign size) [ptr, n]

nativeAddUZ = primAddZ (PrimType nativeWordType)
nativeSubUZ = primSubZ (PrimType nativeWordType)
nativeModUZ = primModZ (PrimType nativeWordType)
nativeMaxUZ = primMaxZ (PrimType nativeWordType)
nativeNegateUZ = primNegateZ (PrimType nativeWordType)

nativeWordL :: Integral a => a -> Lit
nativeWordL n = IntL Unsigned nativeIntSize (fromIntegral n)

nativeWordV :: Integral a => a -> Val
nativeWordV n = LitV $ nativeWordL n

nativeIntL :: Integral a => a -> Lit
nativeIntL n = IntL Signed nativeIntSize (fromIntegral n)

nativeIntV :: Integral a => a -> Val
nativeIntV n = LitV $ nativeIntL n

-------------------------------------------------------------------------------
-- Record operations

-- | Unpack a pass-by-value record
unpackRecord :: (Monad m, Supplies m (Ident Var)) =>
                StaticRecord -> Val -> Gen m [Var]
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
selectField :: (Monad m, Supplies m (Ident Var)) =>
               StaticRecord -> Int -> Val -> Gen m Val
selectField ty index val = do
  fields <- unpackRecord ty val
  return $ VarV $ fields !! index

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
createDynamicRecord :: forall m. (Monad m, Supplies m (Ident Var)) =>
                       [DynamicFieldType] -> Gen m DynamicRecord
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
                    -> Gen m ([Val], Val, Val)
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
addRecordPadding :: (Monad m, Supplies m (Ident Var)) =>
                    Val -> Val -> Gen m Val
addRecordPadding off alignment = do
  neg_off <- nativeNegateUZ off 
  disp <- neg_off `nativeModUZ` alignment
  off `nativeAddUZ` disp

fromPrimType :: DynamicFieldType -> ValueType
fromPrimType (PrimField ty) = PrimType ty
fromPrimType _ = internalError "Expecting a primitive field type"

-- | Load one field of a record into a variable
loadField :: (Monad m, Supplies m (Ident Var)) =>
             DynamicField -> Val -> Gen m Val
loadField field ptr = do
  let off = fieldOffset field
      ty = fromPrimType $ fieldType field
  v <- lift $ newAnonymousVar ty
  primLoadOff ty ptr off v
  return (VarV v)

-- | Load one field of a record into a local variable
loadFieldAs :: (Monad m, Supplies m (Ident Var)) =>
               DynamicField -> Val -> Var -> Gen m ()
loadFieldAs field ptr dst =
  let off = fieldOffset field
      ty = fromPrimType $ fieldType field
  in primLoadOff ty ptr off dst

-- | Store into one field of a record
storeField :: (Monad m, Supplies m (Ident Var)) =>
              DynamicField -> Val -> Val -> Gen m ()
storeField field ptr value =
  let off = fieldOffset field
      ty = fromPrimType $ fieldType field
  in primStoreOff ty ptr off value

-------------------------------------------------------------------------------
-- Other operations

-- | Allocate temporary local memory over the scope of some computation.
--   The allocated memory is not initialized, and must be initialized by 
--   the given code generator.
allocateLocalObject :: (Monad m, Supplies m (Ident Var)) =>
                       Var      -- ^ Pointer that will reference the object
                    -> Val      -- ^ Passing convention of object
                    -> [ValueType] -- ^ Return type(s) of the generated code
                    -> Gen m Atom -- ^ Code generator
                    -> Gen m Atom
allocateLocalObject ptr_var pass_conv rtypes mk_block = do
  -- Allocate the object
  size <- selectPassConvSize pass_conv
  allocateHeapObjectAs size ptr_var
  
  -- Generate code and bind its results to temporary variables
  rvars <- lift $ mapM newAnonymousVar rtypes
  ret_atom <- mk_block
  tell [LetE rvars ret_atom]
  
  -- Free the object
  free <- selectPassConvFree pass_conv
  bindAtom0 $ CallA free [VarV ptr_var]
  
  -- Return the temporary values
  return $ ValA $ map VarV rvars

-- | Allocate the given number of bytes on the heap.
allocateHeapObject :: (Monad m, Supplies m (Ident Var)) => Val -> Gen m Val
allocateHeapObject size =
  emitAtom1 (PrimType PointerType) $
  PrimCallA (builtinVar the_prim_alloc) [size]

allocateHeapObjectAs :: (Monad m, Supplies m (Ident Var)) =>
                        Val -> Var -> Gen m ()
allocateHeapObjectAs size dst =
  bindAtom1 dst $ PrimCallA (builtinVar the_prim_alloc) [size]

deallocateHeapObject :: (Monad m, Supplies m (Ident Var)) => Val -> Gen m ()
deallocateHeapObject ptr =
  emitAtom0 $ PrimCallA (builtinVar the_prim_dealloc) [ptr]

-------------------------------------------------------------------------------

-- | The object header common to all reference-counted objects.
--
-- The header consists of a reference count and a pointer to a 'free' function.
objectHeader :: [StaticFieldType]
objectHeader = [ PrimField nativeWordType
               , PrimField PointerType               
               ]

objectHeaderRecord :: StaticRecord
objectHeaderRecord = staticRecord objectHeader

objectHeaderRecord' :: DynamicRecord
objectHeaderRecord' = toDynamicRecord objectHeaderRecord

-- | Generate code that initializes an object header.
-- The reference count is initialized to 1.
initializeHeader :: (Monad m, Supplies m (Ident Var)) =>
                    Val         -- ^ Object-freeing function
                 -> Val         -- ^ Pointer to object
                 -> Gen m ()
initializeHeader free_function ptr = do
  storeField (objectHeaderRecord' !!: 0) ptr (nativeWordV 1)
  storeField (objectHeaderRecord' !!: 1) ptr free_function

-- | Generate code to increment an object header's reference count.
increfHeader :: (Monad m, Supplies m (Ident Var)) => Val -> Gen m ()
increfHeader ptr = increfHeaderBy 1 ptr

-- | Generate code to increment an object header's reference count by some
-- non-negative amount.
increfHeaderBy :: (Monad m, Supplies m (Ident Var)) => Int -> Val -> Gen m ()
increfHeaderBy n ptr
  | n < 0 = internalError "increfHeaderBy: Negative increment"
  | n == 0 = return ()
  | otherwise = do
      let off = fieldOffset $ recordFields objectHeaderRecord' !! 0
      field_ptr <- primAddP ptr off
      _ <- primAAddZ (PrimType nativeIntType) field_ptr (nativeIntV n)
      return ()

-- | Generate code to decrease an object's reference count, and free it
-- if the reference count is zero.  The parameter variable is an owned
-- reference.
decrefHeader :: (Monad m, Supplies m (Ident Var)) => Val -> Gen m ()
decrefHeader ptr = do
  let off = fieldOffset $ recordFields objectHeaderRecord' !! 0
  field_ptr <- primAddP ptr off
  
  -- Decrement the value, get the old reference count
  old_rc <- primAAddZ (PrimType nativeIntType) field_ptr (nativeIntV (-1))
  
  -- If old reference count was 1, free the pointer
  rc_test <- primCmpZ (PrimType nativeIntType) CmpEQ old_rc (nativeIntV 1)
  if_atom <- genIf rc_test
             (do free_func <- loadField (objectHeaderRecord' !!: 1) ptr
                 return $ PrimCallA free_func [ptr])
             (do return $ ValA [])
  emitAtom0 if_atom

-- | Generate code to decrease an object's reference count, and free it
-- if the reference count is zero.  The parameter variable is an owned
-- reference.
decrefHeaderBy :: (Monad m, Supplies m (Ident Var)) => Int -> Val -> Gen m ()
decrefHeaderBy n ptr
  | n < 0 = internalError "decrefHeaderBy"
  | n == 0 = return ()
  | otherwise = do
      let off = fieldOffset $ recordFields objectHeaderRecord' !! 0
      field_ptr <- primAddP ptr off
  
      -- Subtract the value, get the old reference count
      old_rc <- primAAddZ (PrimType nativeIntType) field_ptr $
                nativeIntV (negate n)
  
      -- If old reference count was less than or equal to n, free the pointer
      rc_test <- primCmpZ (PrimType nativeIntType) CmpLE old_rc $
                 nativeIntV n
      if_atom <- genIf rc_test
                 (do free_func <- loadField (objectHeaderRecord' !!: 1) ptr
                     return $ PrimCallA free_func [ptr])
                 (do return $ ValA [])
      emitAtom0 if_atom

-- | A parameter passing convention consists of size, alignment, copy,
-- and free functions
passConvRecord :: StaticRecord
passConvRecord = staticRecord [ PrimField nativeWordType
                              , PrimField nativeWordType
                              , PrimField OwnedType
                              , PrimField OwnedType
                              ]

selectPassConvSize, selectPassConvAlignment,
  selectPassConvCopy,
  selectPassConvFree :: (Monad m, Supplies m (Ident Var)) => Val -> Gen m Val
selectPassConvSize = selectField passConvRecord 0
selectPassConvAlignment = selectField passConvRecord 1
selectPassConvCopy = selectField passConvRecord 2
selectPassConvFree = selectField passConvRecord 3

passConvValue :: Int -> Int -> Var -> Var -> Val
passConvValue size align copy free =
  RecV passConvRecord
  [ LitV $ IntL Unsigned S32 (fromIntegral size)
  , LitV $ IntL Unsigned S32 (fromIntegral align)
  , VarV copy
  , VarV free
  ]

intPassConvValue :: Val
intPassConvValue =
  passConvValue 4 4 (llBuiltin the_fun_copy4) (llBuiltin the_fun_dealloc)

floatPassConvValue :: Val
floatPassConvValue =
  passConvValue 4 4 (llBuiltin the_fun_copy4) (llBuiltin the_fun_dealloc)

