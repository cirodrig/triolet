
{-# LANGUAGE ViewPatterns, FlexibleInstances, FlexibleContexts, NoMonomorphismRestriction, ScopedTypeVariables, RecursiveDo #-}
module LowLevel.Build where

import Control.Monad
import Control.Monad.Writer
import qualified Data.Set as Set
import Data.Set(Set)

import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.Supply
import Gluon.Core(Con(..))
import LowLevel.Builtins
import LowLevel.FreshVar
import LowLevel.Label
import LowLevel.Syntax
import LowLevel.Types
import LowLevel.Record
import LowLevel.Records

newtype MkStm = MkStm (Stm -> Stm)

instance Monoid MkStm where
  mempty = MkStm id
  MkStm f `mappend` MkStm g = MkStm (f . g)

-- | A code generator.
--
-- It knows the return type of the code it will generate, and builds a
-- statement as a side effect.
newtype Gen m a = Gen {runGen :: [ValueType] -> m (a, MkStm)}

instance Monad m => Functor (Gen m) where
  fmap f (Gen m) = Gen (\rt -> do (x, stms) <- m rt
                                  return (f x, stms))

instance Monad m => Monad (Gen m) where
  return x = Gen (\_ -> return (x, mempty))
  Gen m >>= k = Gen (\rt -> do (x, mk1) <- m rt
                               (y, mk2) <- runGen (k x) rt
                               return (y, mk1 `mappend` mk2))

instance MonadFix m => MonadFix (Gen m) where
  mfix f = Gen (\rt -> mdo rv@(x, stms) <- case f x of Gen m -> m rt
                           return rv)

instance MonadTrans Gen where
  lift m = Gen (\_ -> do x <- m
                         return (x, mempty))

instance Monad m => MonadWriter MkStm (Gen m) where
  tell w = Gen (\_ -> return ((), w))
  listen (Gen m) = Gen (\rt -> do x@(_, w) <- m rt
                                  return (x, w))
  pass (Gen m) = Gen (\rt -> do ((x, f), w) <- m rt
                                return (x, f w))

execBuild :: Monad m => [ValueType] -> Gen m Stm -> m Stm
execBuild return_type m = do
  (stm, MkStm mk_stm) <- runGen m return_type
  return $ mk_stm stm

execBuild' :: Monad m => [ValueType] -> Gen m (Stm, a) -> m (Stm, a)
execBuild' return_type m = do
  ((stm, a), MkStm mk_stm) <- runGen m return_type
  return (mk_stm stm, a)

{-
-- | Build a block for use in a larger expression
getBlock :: Monad m => Gen m Atom -> Gen m Block
getBlock m = WriterT $ do
  block <- execBuild m
  return (block, [])

-- | Produce a block and return some other value as well
getBlock' :: Monad m => Gen m (Atom, a) -> Gen m (Block, a)
getBlock' m = WriterT $ do
  ((atom, x), stms) <- runWriterT m
  return ((Block stms atom, x), [])

putBlock :: Monad m => Block -> Gen m Atom
putBlock (Block stms atom) = WriterT $ return (atom, stms)
-}

-- | Run a code generator, but don't produce output here.  Instead, a code
--   generator is returned that produces its output.
suspendGen :: (Monad m, Supplies m (Ident Var),
               Monad m', Supplies m' (Ident Var)) =>
              [ValueType] -> Gen m a -> m (Gen m' (), a)
suspendGen return_type m = do
  (x, stms) <- runGen m return_type
  return (tell stms, x)

emit :: Monad m => (Stm -> Stm) -> Gen m ()
emit f = tell (MkStm f)

-- | Wrap the continuation into a function.  The locally live-out variables
-- become the function parameters.
--
-- Each of the locally live-out variables may become multiple variables with 
-- the same name and ID.  The variables will have disjoint lifetimes.  One 
-- instance of the variables becomes the continuation's parameters.  The other
-- instances become temporary variables that are passed as arguments when
-- calling the continuation.
getContinuation :: (Monad m, Supplies m (Ident Var)) =>
                   Bool         -- ^ Create a primitive call?
                -> [ParamVar]   -- ^ Live-out variables
                -> (Stm -> Gen m Stm) -- ^ Code using the continuation
                -> Gen m ()
getContinuation primcall live_outs f = Gen $ \return_type -> do
  -- Create a call to the continuation
  cont_var <- newAnonymousVar (PrimType PointerType)
  let cont_call =
        if primcall
        then ReturnE $ PrimCallA (VarV cont_var) (map VarV live_outs)
        else ReturnE $ CallA (VarV cont_var) (map VarV live_outs)
      
  -- Construct a statement that calls the continuation
  (stm, MkStm stms) <- runGen (f cont_call) return_type
  
  -- Put the continuation into a 'letrec' statement
  let stms' cont_stm = LetrecE [FunDef cont_var cont_fun] (stms stm)
        where
          cont_fun =
            if primcall
            then primFun live_outs return_type cont_stm
            else closureFun live_outs return_type cont_stm
  
  return ((), MkStm stms')

valFreeVars :: Val -> Set Var
valFreeVars val = 
  case val
  of VarV v    -> Set.singleton v
     RecV _ vs -> valsFreeVars vs
     LitV _    -> Set.empty
     LamV f    -> funFreeVars f

valsFreeVars :: [Val] -> Set Var
valsFreeVars vs = Set.unions (map valFreeVars vs)

atomFreeVars :: Atom -> Set Var
atomFreeVars atom =
  case atom
  of ValA vs        -> valsFreeVars vs
     CallA v vs     -> valsFreeVars (v:vs)
     PrimCallA v vs -> valsFreeVars (v:vs)
     PrimA _ vs     -> valsFreeVars vs
     PackA _ vs     -> valsFreeVars vs
     UnpackA _ v    -> valFreeVars v

stmFreeVars :: Stm -> Set Var
stmFreeVars stm =
  case stm
  of LetE params rhs body ->
       let body_fv = foldr Set.delete (stmFreeVars body) params
       in Set.union body_fv $ atomFreeVars rhs
     LetrecE defs body ->
       let fun_vars = [v | FunDef v _ <- defs]
           body_fv = stmFreeVars body
           funs_fvs = [funFreeVars d | FunDef _ d <- defs]
       in foldr Set.delete (Set.unions (body_fv : funs_fvs)) fun_vars
     SwitchE v alts ->
       Set.unions (valFreeVars v : [stmFreeVars s | (_, s) <- alts])
     ReturnE atom ->
       atomFreeVars atom

funFreeVars :: Fun -> Set Var
funFreeVars f = foldr Set.delete (stmFreeVars (funBody f)) (funParams f)

-------------------------------------------------------------------------------
-- Generating primops

-- | Generate an instruction that has no result value
emitAtom0 :: Monad m => Atom -> Gen m ()
emitAtom0 atom = emit $ LetE [] atom

emitAtom1 :: (Monad m, Supplies m (Ident Var)) =>
             ValueType -> Atom -> Gen m Val
emitAtom1 ty atom = do
  tmpvar <- lift $ newAnonymousVar ty
  emit $ LetE [tmpvar] atom
  return $ VarV tmpvar

emitAtom :: (Monad m, Supplies m (Ident Var)) =>
            [ValueType] -> Atom -> Gen m [Val]
emitAtom tys atom = do
  tmpvars <- lift $ mapM newAnonymousVar tys
  emit $ LetE tmpvars atom
  return $ map VarV tmpvars

bindAtom0 :: Monad m => Atom -> Gen m ()
bindAtom0 = emitAtom0

bindAtom1 :: Monad m => Var -> Atom -> Gen m ()
bindAtom1 var atom = emit $ LetE [var] atom

bindAtom :: Monad m => [Var] -> Atom -> Gen m ()
bindAtom vars atom = emit $ LetE vars atom

emitLetrec :: Monad m => [FunDef] -> Gen m ()
emitLetrec defs = emit $ LetrecE defs

-- | Generate a no-op
gen0 :: Monad m => Gen m Stm
gen0 = return $ ReturnE (ValA [])

genIf :: Monad m => Val -> Gen m Stm -> Gen m Stm -> Gen m Stm
genIf bool if_true if_false = Gen $ \rt -> do
  true_block <- execBuild rt if_true
  false_block <- execBuild rt if_false
  return (SwitchE bool [ (BoolL True, true_block)
                       , (BoolL False, false_block)], mempty)

genIf' :: Monad m =>
          Val -> Gen m (Stm, a) -> Gen m (Stm, b) -> Gen m (Stm, a, b)
genIf' bool if_true if_false = Gen $ \rt -> do
  (true_block, x) <- execBuild' rt if_true
  (false_block, y) <- execBuild' rt if_false
  let if_exp = SwitchE bool [ (BoolL True, true_block)
                            , (BoolL False, false_block)]
  return ((if_exp, x, y), mempty)

builtinVar :: (LowLevelBuiltins -> Var) -> Val
builtinVar v = VarV $ llBuiltin v

genPrimFun :: Monad m => [ParamVar] -> [ValueType] -> Gen m Stm -> m Fun
genPrimFun params returns body =
  liftM (Fun True params returns) $ execBuild returns body

genClosureFun :: Monad m =>
                 [ParamVar] -> [ValueType] -> Gen m Stm -> m Fun
genClosureFun params returns body =
  liftM (Fun False params returns) $ execBuild returns body

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
  emitAtom1 (PrimType BoolType) $ PrimA (PrimCmpZ sign size comparison) [x, y]

primAnd x y =
  emitAtom1 (PrimType BoolType) $ PrimA PrimAnd [x, y]

primAddP ptr off =
  emitAtom1 (PrimType PointerType) $ PrimA PrimAddP [ptr, off]

primAddPAs ptr off ptr' =
  bindAtom1 ptr' $ PrimA PrimAddP [ptr, off]

primLoad ty ptr dst = primLoadOff ty ptr (nativeIntV 0)
primLoadOff ty ptr off dst =
  bindAtom1 dst $ PrimA (PrimLoad ty) [ptr, off]

primStore ty ptr val = primStoreOff ty ptr (nativeIntV 0) val
primStoreOff ty ptr off val =
  emitAtom0 $ PrimA (PrimStore ty) [ptr, off, val]

primCastToOwned ptr =
  emitAtom1 (PrimType OwnedType) $ PrimA PrimCastToOwned [ptr]

primCastFromOwned ptr =
  emitAtom1 (PrimType OwnedType) $ PrimA PrimCastFromOwned [ptr]

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

-- | A convenience class for interpreting records as dynamic records.
--
-- Static records are interpreted as dynamic records by converting all
-- 'Int' fields to constant integer values.
class ToDynamicRecordData a where
  toDynamicRecord :: Record a -> Record Val
  toDynamicField :: Field a -> Field Val
  toDynamicFieldType :: FieldType a -> FieldType Val

instance ToDynamicRecordData Val where
  toDynamicRecord x = x
  toDynamicField x = x
  toDynamicFieldType x = x

instance ToDynamicRecordData Int where
  toDynamicRecord rec = let
    fs = map toDynamicField $ recordFields rec
    size = nativeWordV $ recordSize rec
    alignment = nativeWordV $ recordAlignment rec
    in record fs size alignment

  toDynamicField (Field off ty) =
    Field (nativeWordV off) (toDynamicFieldType ty)

  toDynamicFieldType (PrimField t) = PrimField t
  toDynamicFieldType (RecordField rec) = RecordField $ toDynamicRecord rec
  toDynamicFieldType (BytesField s a) =
        BytesField (nativeWordV s) (nativeWordV a)

-- | Unpack a pass-by-value record
unpackRecord :: (Monad m, Supplies m (Ident Var)) =>
                StaticRecord -> Val -> Gen m [Var]
unpackRecord rtype val = do
  -- Create a variable to hold each field value
  vars <- lift $ mapM newFieldVar $ recordFields rtype
  
  -- Create an 'unpack' expression
  emit $ LetE vars (UnpackA rtype val)
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

dynamicFieldSize :: (ToDynamicRecordData a) => Field a -> Val
dynamicFieldSize f = dynamicFieldTypeSize $ fieldType f

dynamicFieldAlignment :: (ToDynamicRecordData a) => Field a -> Val
dynamicFieldAlignment f = dynamicFieldTypeAlignment $ fieldType f

dynamicFieldTypeSize :: (ToDynamicRecordData a) => FieldType a -> Val
dynamicFieldTypeSize (toDynamicFieldType -> ft) =
  case ft
  of PrimField vt   -> nativeWordV $ sizeOf vt
     RecordField r -> recordSize r
     BytesField s _  -> s

dynamicFieldTypeAlignment :: (ToDynamicRecordData a) => FieldType a -> Val
dynamicFieldTypeAlignment (toDynamicFieldType -> ft) =
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

-- | Create a dynamic record, but don't generate the code for it now.
--   Returns a dynamic record, and a code generator that computes values used
--   in the record.  The code generator calls 'createDynamicRecord'.
suspendedCreateDynamicRecord :: forall m m'.
                                (Monad m, Supplies m (Ident Var),
                                 Monad m', Supplies m' (Ident Var)) =>
                                [DynamicFieldType]
                             -> m (Gen m' (), DynamicRecord)
suspendedCreateDynamicRecord field_types = do
  -- Create variables to stand for size, alignment, and field offsets
  -- that will be computed later
  size_v <- newAnonymousVar (PrimType nativeWordType)
  align_v <- newAnonymousVar (PrimType nativeWordType)
  offsets <- replicateM (length field_types) $
             newAnonymousVar (PrimType nativeWordType)
  let fields = zipWith Field (map VarV offsets) field_types
      code = compute_record_layout size_v align_v offsets
  return (code, record fields (VarV size_v) (VarV align_v))
  where
    -- Compute the actual data
    compute_record_layout size_v align_v offset_vs = do
      record <- createDynamicRecord field_types
      
      -- Assign values
      bindAtom1 size_v $ ValA [recordSize record]
      bindAtom1 align_v $ ValA [recordAlignment record]
      forM_ (zip offset_vs $ recordFields record) $ \(offset_v, fld) -> 
        bindAtom1 offset_v $ ValA [fieldOffset fld]

-- | Compute the necessary record padding for a given offset
addRecordPadding :: (Monad m, Supplies m (Ident Var)) =>
                    Val -> Val -> Gen m Val
addRecordPadding off alignment = do
  neg_off <- nativeNegateUZ off 
  disp <- neg_off `nativeModUZ` alignment
  off `nativeAddUZ` disp

fromPrimType :: DynamicFieldType -> ValueType
fromPrimType (PrimField ty) = PrimType ty
fromPrimType (RecordField rec) =
  RecordType $ staticRecord $ map (as_value_type . fromPrimType . fieldType) $ recordFields rec
  where
    as_value_type (PrimType ty) = PrimField ty
    as_value_type (RecordType rec) = RecordField rec
fromPrimType _ = internalError "Expecting a primitive field type"

-- | Load one field of a record into a variable
loadField :: (Monad m, Supplies m (Ident Var), ToDynamicRecordData a) =>
             Field a -> Val -> Gen m Val
loadField (toDynamicField -> field) ptr = do
  let off = fieldOffset field
      ty = fromPrimType $ fieldType field
  v <- lift $ newAnonymousVar ty
  primLoadOff ty ptr off v
  return (VarV v)

-- | Load an owned field as a non-owned pointer.  Reference counts will not 
-- be tracked or adjusted.
loadFieldWithoutOwnership :: (Monad m, Supplies m (Ident Var),
                              ToDynamicRecordData a) =>
                             Field a -> Val -> Gen m Val
loadFieldWithoutOwnership (toDynamicField -> field) ptr = do
  let off = fieldOffset field

  -- Must be an owned field
  case fieldType field of
    PrimField OwnedType -> return ()
    _ -> internalError "loadFieldWithoutOwnership: Wrong type"

  v <- lift $ newAnonymousVar (PrimType PointerType)
  primLoadOff (PrimType PointerType) ptr off v
  return (VarV v)

-- | Load one field of a record into a local variable
loadFieldAs :: (Monad m, Supplies m (Ident Var), ToDynamicRecordData a) =>
               Field a -> Val -> Var -> Gen m ()
loadFieldAs (toDynamicField -> field) ptr dst =
  let off = fieldOffset field
      ty = fromPrimType $ fieldType field
  in primLoadOff ty ptr off dst

-- | Store into one field of a record
storeField :: (Monad m, Supplies m (Ident Var), ToDynamicRecordData a) =>
              Field a -> Val -> Val -> Gen m ()
storeField (toDynamicField -> field) ptr value =
  let off = fieldOffset field
      ty = fromPrimType $ fieldType field
  in primStoreOff ty ptr off value

-- | Get a pointer to a field of a record, given the base pointer.
referenceField :: (Monad m, Supplies m (Ident Var), ToDynamicRecordData a) =>
                  Field a -> Val -> Gen m Val
referenceField (toDynamicField -> field) ptr = primAddP ptr $ fieldOffset field

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
  emit (LetE rvars ret_atom)
  
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

passConvRecord' :: DynamicRecord
passConvRecord' = toDynamicRecord passConvRecord

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
decrefObject :: (Monad m, Supplies m (Ident Var)) => Bool -> Val -> Gen m ()
decrefObject make_primcall ptr = getContinuation make_primcall [] $ \cont -> do
  let off = fieldOffset $ recordFields objectHeaderRecord' !! 0
  field_ptr <- primAddP ptr off
  
  -- Decrement the value, get the old reference count
  old_rc <- primAAddZ (PrimType nativeIntType) field_ptr (nativeIntV (-1))
  
  -- If old reference count was 1, free the pointer
  rc_test <- primCmpZ (PrimType nativeIntType) CmpEQ old_rc (nativeIntV 1)
  genIf rc_test (freeObject ptr >> return cont) (return cont)

-- | Generate code to decrease an object's reference count, and free it
-- if the reference count is zero.  The parameter variable is an owned
-- reference.
decrefObjectBy :: (Monad m, Supplies m (Ident Var)) =>
                  Bool -> Int -> Val -> Gen m ()
decrefObjectBy make_primcall n ptr
  | n < 0 = internalError "decrefHeaderBy"
  | n == 0 = return ()
  | otherwise = getContinuation make_primcall [] $ \cont -> do
      let off = fieldOffset $ recordFields objectHeaderRecord' !! 0
      field_ptr <- primAddP ptr off
  
      -- Subtract the value, get the old reference count
      old_rc <- primAAddZ (PrimType nativeIntType) field_ptr $
                nativeIntV (negate n)
  
      -- If old reference count was less than or equal to n, free the pointer
      rc_test <- primCmpZ (PrimType nativeIntType) CmpLE old_rc $
                 nativeIntV n
      genIf rc_test (freeObject ptr >> return cont) (return cont)

-- | Add the given number (which may be negative) to an object's reference  
-- count.  If positive, 'increfObjectBy' is called; if negative,
-- 'decrefObjectBy' is called.
adjustObjectBy :: (Monad m, Supplies m (Ident Var)) =>
                  Bool -> Int -> Val -> Gen m ()
adjustObjectBy make_primcall n ptr
  | n > 0     = increfObjectBy n ptr
  | n < 0     = decrefObjectBy make_primcall (negate n) ptr
  | otherwise = return ()

selectPassConvSize, selectPassConvAlignment,
  selectPassConvCopy,
  selectPassConvFinalize :: (Monad m, Supplies m (Ident Var)) =>
                            Val -> Gen m Val
selectPassConvSize = loadField (passConvRecord' !!: 0)
selectPassConvAlignment = loadField (passConvRecord' !!: 1)
selectPassConvCopy = loadField (passConvRecord' !!: 2)
selectPassConvFinalize = loadField (passConvRecord' !!: 3)

-------------------------------------------------------------------------------
-- Dictionaries

-- | The record type of an additive class dictionary
additiveDictRecord :: (Monad m, Supplies m (Ident Var)) =>
                      DynamicFieldType -> Gen m DynamicRecord
additiveDictRecord ftype =
  createDynamicRecord [ RecordField passConvRecord'
                      , PrimField OwnedType
                      , PrimField OwnedType
                      , PrimField OwnedType
                      , ftype]

suspendedAdditiveDictRecord ftype =
  suspendedCreateDynamicRecord [ RecordField passConvRecord'
                               , PrimField OwnedType
                               , PrimField OwnedType
                               , PrimField OwnedType
                               , ftype]

suspendedMultiplicativeDictRecord ftype = do
  (additive_code, additive_record) <- suspendedAdditiveDictRecord ftype
  (multiplicative_code, multiplicative_record) <-
    suspendedCreateDynamicRecord [ RecordField additive_record
                                 , PrimField OwnedType
                                 , PrimField OwnedType
                                 , ftype]
  return (additive_code >> multiplicative_code, multiplicative_record)

complexRecord' eltype = createDynamicRecord [eltype, eltype]

suspendedComplexRecord' eltype = suspendedCreateDynamicRecord [eltype, eltype]

-------------------------------------------------------------------------------
-- Values

data WantClosureDeallocator =
    NeverDeallocate             -- ^ The closure is never deallocated
  | DefaultDeallocator          -- ^ The closure has no captured variables and
                                --   is not recursive; use the default
                                --   deallocation function
  | CustomDeallocator !Var      -- ^ Use the given deallocation function

-- | Create an 'EntryPoints' data structure for an externally visible
-- global function and populate it with new variables.
mkGlobalEntryPoints :: (Monad m, Supplies m (Ident Var)) =>
                       FunctionType   -- ^ Function type
                    -> Label          -- ^ Function name
                    -> Var            -- ^ Global closure variable
                    -> m EntryPoints  -- ^ Creates an EntryPoints structure
mkGlobalEntryPoints ftype label global_closure
  | ftIsPrim ftype = internalError "mkEntryPoints: Not a closure function"
  | otherwise = do
      inf <- newVar (Just label) (PrimType PointerType)
      dir <- make_entry_point DirectEntryLabel
      exa <- make_entry_point ExactEntryLabel
      ine <- make_entry_point InexactEntryLabel
      let arity = length $ ftParamTypes ftype
      return $! EntryPoints ftype arity dir exa ine Nothing inf (Just global_closure)
  where
    -- If the global closure is externally visible, the other entry points
    -- will also be externally visible
    make_entry_point tag =
      let new_label = label {labelTag = tag, labelExternalName = Nothing}
      in if varIsExternal global_closure
         then newExternalVar new_label (PrimType PointerType)
         else newVar (Just new_label) (PrimType PointerType)

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
             of NeverDeallocate -> return Nothing
                DefaultDeallocator ->
                  -- The default deallocator simply calls pyon_dealloc 
                  return $ Just $ llBuiltin the_prim_pyon_dealloc
                CustomDeallocator f ->
                  return $ Just f
      let arity = length $ ftParamTypes ftype
      return $! EntryPoints ftype arity dir exa ine dea inf Nothing
{-
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
             of 4 -> llBuiltin the_fun_copy4F
                _ -> internalError "intPassConvValue"
  in passConvValue size align copy (llBuiltin the_fun_dummy_finalizer)

floatPassConvValue :: Val
floatPassConvValue =
  let size = sizeOf pyonFloatType
      align = alignOf pyonFloatType
      copy = case size
             of 4 -> llBuiltin the_fun_copy4F
                _ -> internalError "intPassConvValue"
  in passConvValue size align copy (llBuiltin the_fun_dummy_finalizer)

boolPassConvValue :: Val
boolPassConvValue =
  let size = sizeOf pyonBoolType
      align = alignOf pyonBoolType
      copy = case size
             of 4 -> llBuiltin the_fun_copy4F
                _ -> internalError "intPassConvValue"
  in passConvValue size align copy (llBuiltin the_fun_dummy_finalizer)

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
-}