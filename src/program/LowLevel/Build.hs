
{-# LANGUAGE ViewPatterns, FlexibleInstances, FlexibleContexts, NoMonomorphismRestriction, ScopedTypeVariables #-}
module LowLevel.Build where

import Control.Monad
import Control.Monad.Writer

import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.Label
import Gluon.Common.Supply
import Gluon.Core(Con(..))
import LowLevel.Builtins
import LowLevel.FreshVar
import LowLevel.Syntax
import LowLevel.Types
import LowLevel.Record
import LowLevel.Records

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

emitLetrec :: Monad m => [FunDef] -> Gen m ()
emitLetrec defs = tell [LetrecE defs]

-- | Generate a no-op
gen0 :: Monad m => Gen m Atom
gen0 = return $ ValA [] 

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

primLoad ty ptr dst = primLoadOff ty ptr (nativeIntV 0)
primLoadOff ty ptr off dst = 
  bindAtom1 dst $ PrimA (PrimLoad ty) [ptr, off]

primStore ty ptr val = primStoreOff ty ptr (nativeIntV 0) val
primStoreOff ty ptr off val =
  emitAtom0 $ PrimA (PrimStore ty) [ptr, off, val]

isZeroLit (LitV (IntL _ _ 0)) = True
isZeroLit _ = False

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

uint8V :: Integral a => a -> Val
uint8V n = LitV $ IntL Unsigned S8 $ fromIntegral n

uint16V :: Integral a => a -> Val
uint16V n = LitV $ IntL Unsigned S16 $ fromIntegral n

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
toDynamicFieldType (RecordField rec) = RecordField $ toDynamicRecord rec
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
     RecordField r -> recordSize r
     BytesField s _  -> s

dynamicFieldTypeAlignment :: DynamicFieldType -> Val
dynamicFieldTypeAlignment ft = 
  case ft
  of PrimField vt   -> nativeWordV $ alignOf vt
     RecordField r -> recordAlignment r
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

-- | Load an owned field as a non-owned pointer.  Reference counts will not 
-- be tracked or adjusted.
loadFieldWithoutOwnership :: (Monad m, Supplies m (Ident Var)) =>
                             DynamicField -> Val -> Gen m Val
loadFieldWithoutOwnership field ptr = do
  let off = fieldOffset field

  -- Must be an owned field
  case fieldType field of
    PrimField OwnedType -> return ()
    _ -> internalError "loadFieldWithoutOwnership: Wrong type"

  v <- lift $ newAnonymousVar (PrimType PointerType)
  primLoadOff (PrimType PointerType) ptr off v
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
allocateLocalMem :: (Monad m, Supplies m (Ident Var)) =>
                    Var      -- ^ Pointer that will reference the object
                 -> Val      -- ^ Passing convention of object
                 -> [ValueType] -- ^ Return type(s) of the generated code
                 -> Gen m Atom -- ^ Code generator
                 -> Gen m Atom
allocateLocalMem ptr_var pass_conv rtypes mk_block = do
  -- Allocate the object
  size <- selectPassConvSize pass_conv
  allocateHeapMemAs size ptr_var
  
  -- Generate code and bind its results to temporary variables
  rvars <- lift $ mapM newAnonymousVar rtypes
  ret_atom <- mk_block
  tell [LetE rvars ret_atom]
  
  -- Finalize and free the object
  fini <- selectPassConvFinalize pass_conv
  bindAtom0 $ CallA fini [VarV ptr_var]
  bindAtom0 $ PrimCallA (builtinVar the_prim_pyon_dealloc) [VarV ptr_var]
  
  -- Return the temporary values
  return $ ValA $ map VarV rvars

-- | Allocate the given number of bytes on the heap.
allocateHeapMem :: (Monad m, Supplies m (Ident Var)) => Val -> Gen m Val
allocateHeapMem size =
  emitAtom1 (PrimType PointerType) $
  PrimCallA (builtinVar the_prim_pyon_alloc) [size]

allocateHeapMemAs :: (Monad m, Supplies m (Ident Var)) =>
                     Val -> Var -> Gen m ()
allocateHeapMemAs size dst =
  bindAtom1 dst $ PrimCallA (builtinVar the_prim_pyon_alloc) [size]

deallocateHeapMem :: (Monad m, Supplies m (Ident Var)) => Val -> Gen m ()
deallocateHeapMem ptr =
  emitAtom0 $ PrimCallA (builtinVar the_prim_pyon_dealloc) [ptr]

-------------------------------------------------------------------------------
-- Manipulating objects

objectHeaderRecord' :: DynamicRecord
objectHeaderRecord' = toDynamicRecord objectHeaderRecord

objectHeaderData :: Val -> [Val]
objectHeaderData info_ptr = [nativeWordV 1, info_ptr]

infoTableHeaderRecord' :: DynamicRecord
infoTableHeaderRecord' = toDynamicRecord infoTableHeaderRecord

-- | Generate code that initializes an object header.
-- The reference count is initialized to 1.
initializeObject :: (Monad m, Supplies m (Ident Var)) =>
                    Val         -- ^ Pointer to object
                 -> Val         -- ^ Info table pointer
                 -> Gen m ()
initializeObject ptr info_ptr = do
  storeField (objectHeaderRecord' !!: 0) ptr (nativeWordV 1)
  storeField (objectHeaderRecord' !!: 1) ptr info_ptr

-- | Generate code that frees an object.
freeObject :: (Monad m, Supplies m (Ident Var)) =>
              Val               -- ^ Pointer to object
           -> Gen m ()
freeObject ptr = do
  info_ptr <- loadField (objectHeaderRecord' !!: 1) ptr
  free_func <- loadField (infoTableHeaderRecord' !!: 0) info_ptr
  emitAtom0 $ PrimCallA free_func [ptr]  

-- | Generate code to increment an object header's reference count.
increfObject :: (Monad m, Supplies m (Ident Var)) => Val -> Gen m ()
increfObject ptr = increfObjectBy 1 ptr

-- | Generate code to increment an object header's reference count by some
-- non-negative amount.
increfObjectBy :: (Monad m, Supplies m (Ident Var)) => Int -> Val -> Gen m ()
increfObjectBy n ptr
  | n < 0 = internalError "increfHeaderBy: Negative increment"
  | n == 0 = return ()
  | otherwise = do
      let off = fieldOffset $ recordFields objectHeaderRecord' !! 0
      field_ptr <- primAddP ptr off
      _ <- primAAddZ (PrimType nativeIntType) field_ptr (nativeIntV n)
      return ()

-- | Generate code to decrease an object's reference count, and free it
-- if the reference count is zero.  The parameter variable is an owned
-- reference or a non-owned pointer.
decrefObject :: (Monad m, Supplies m (Ident Var)) => Val -> Gen m ()
decrefObject ptr = do
  let off = fieldOffset $ recordFields objectHeaderRecord' !! 0
  field_ptr <- primAddP ptr off
  
  -- Decrement the value, get the old reference count
  old_rc <- primAAddZ (PrimType nativeIntType) field_ptr (nativeIntV (-1))
  
  -- If old reference count was 1, free the pointer
  rc_test <- primCmpZ (PrimType nativeIntType) CmpEQ old_rc (nativeIntV 1)
  if_atom <- genIf rc_test (freeObject ptr >> gen0) gen0
  emitAtom0 if_atom

-- | Generate code to decrease an object's reference count, and free it
-- if the reference count is zero.  The parameter variable is an owned
-- reference.
decrefObjectBy :: (Monad m, Supplies m (Ident Var)) => Int -> Val -> Gen m ()
decrefObjectBy n ptr
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
      if_atom <- genIf rc_test (freeObject ptr >> gen0) gen0
      emitAtom0 if_atom

-- | Add the given number (which may be negative) to an object's reference  
-- count.  If positive, 'increfObjectBy' is called; if negative,
-- 'decrefObjectBy' is called.
adjustObjectBy :: (Monad m, Supplies m (Ident Var)) => Int -> Val -> Gen m ()
adjustObjectBy n ptr
  | n > 0     = increfObjectBy n ptr
  | n < 0     = decrefObjectBy (negate n) ptr
  | otherwise = return ()

selectPassConvSize, selectPassConvAlignment,
  selectPassConvCopy,
  selectPassConvFinalize :: (Monad m, Supplies m (Ident Var)) =>
                            Val -> Gen m Val
selectPassConvSize = selectField passConvRecord 0
selectPassConvAlignment = selectField passConvRecord 1
selectPassConvCopy = selectField passConvRecord 2
selectPassConvFinalize = selectField passConvRecord 3

-------------------------------------------------------------------------------
-- Values

data WantClosureDeallocator =
    CannotDeallocate            -- ^ The closure is never deallocated
  | DefaultDeallocator          -- ^ The closure has no captured variables and
                                --   is not recursive; use the default
                                --   deallocation function
  | CustomDeallocator           -- ^ Generate a specialized deallocator

-- | Create an 'EntryPoints' data structure and populate it with new variables.
-- 
-- The deallocation function can either be a new variable or the default 
-- deallocation function.
mkEntryPoints :: (Monad m, Supplies m (Ident Var)) =>
                 WantClosureDeallocator
              -> FunctionType   -- ^ Function type
              -> Maybe Label    -- ^ Function name
              -> m EntryPoints  -- ^ Creates an EntryPoints structure
mkEntryPoints want_dealloc ftype label 
  | ftIsPrim ftype = internalError "mkEntryPoints: Not a closure function"
  | otherwise = do
      [inf, dir, exa, ine] <-
        replicateM 4 $ newVar label (PrimType PointerType)
      dea <- case want_dealloc
             of CannotDeallocate -> return Nothing
                DefaultDeallocator ->
                  return $ Just $ llBuiltin the_prim_dealloc_global_closure
                CustomDeallocator ->
                  liftM Just $ newVar label (PrimType PointerType)
      let arity = length $ ftParamTypes ftype
      return $! EntryPoints ftype arity dir exa ine dea inf

passConvValue :: Int -> Int -> Var -> Var -> Val
passConvValue size align copy finalize =
  RecV passConvRecord
  [ LitV $ IntL Unsigned S32 (fromIntegral size)
  , LitV $ IntL Unsigned S32 (fromIntegral align)
  , VarV copy
  , VarV finalize
  ]

intPassConvValue :: Val
intPassConvValue =
  let size = sizeOf pyonIntType
      align = alignOf pyonIntType
      copy = case size
             of 4 -> llBuiltin the_fun_copy4_closure
                _ -> internalError "intPassConvValue"
  in passConvValue size align copy (llBuiltin the_fun_dummy_finalize)

floatPassConvValue :: Val
floatPassConvValue =
  let size = sizeOf pyonFloatType
      align = alignOf pyonFloatType
      copy = case size
             of 4 -> llBuiltin the_fun_copy4_closure
                _ -> internalError "intPassConvValue"
  in passConvValue size align copy (llBuiltin the_fun_dummy_finalize)

boolPassConvValue :: Val
boolPassConvValue =
  let size = sizeOf pyonBoolType
      align = alignOf pyonBoolType
      copy = case size
             of 4 -> llBuiltin the_fun_copy4_closure
                _ -> internalError "intPassConvValue"
  in passConvValue size align copy (llBuiltin the_fun_dummy_finalize)

-- | Create a lambda function that constructs an additive dictionary
genAdditiveDictFun :: (Monad m, Supplies m (Ident Var)) => Gen m Atom
genAdditiveDictFun = do
  type_param <- lift $ newAnonymousVar (PrimType UnitType)
  zero_param <- lift $ newAnonymousVar (PrimType OwnedType)
  add_param <- lift $ newAnonymousVar (PrimType OwnedType)
  sub_param <- lift $ newAnonymousVar (PrimType OwnedType)
  let params = [type_param, zero_param, add_param, sub_param]
  fun_body <- getBlock $ return $ PackA additiveDictRecord (map VarV params)
  return $ ValA [LamV $ closureFun params [RecordType additiveDictRecord] fun_body]