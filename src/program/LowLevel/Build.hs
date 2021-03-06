
{-# LANGUAGE ViewPatterns, FlexibleInstances, FlexibleContexts, NoMonomorphismRestriction, ScopedTypeVariables, DoRec #-}
module LowLevel.Build where

import Control.Applicative
import Control.Monad
import Control.Monad.Writer
import Data.Bits
import Data.Maybe
import qualified Data.Set as Set
import Data.Set(Set)
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import Common.Supply
import Common.Label
import LowLevel.Builtins
import LowLevel.FreshVar
import LowLevel.Syntax
import LowLevel.CodeTypes
import LowLevel.Records
import LowLevel.Print
import qualified Type.Type as Type
import qualified Type.Environment as Type

newtype MkStm = MkStm (Stm -> Stm)

instance Monoid MkStm where
  mempty = MkStm id
  MkStm f `mappend` MkStm g = MkStm (f . g)

-- | A code generator.
--
-- It knows the return type of the code it will generate, and builds a
-- statement as a side effect.
newtype Gen m a = Gen {runGen :: [ValueType] -> m (a, MkStm)}

instance Functor m => Functor (Gen m) where
  fmap f (Gen m) = Gen (\rt -> fmap app (m rt)) 
    where app (x, stms) = (f x, stms)

instance Applicative m => Applicative (Gen m) where
  pure x = Gen (\_ -> pure (x, mempty))
  Gen x <*> Gen y = Gen (\rt -> app <$> x rt <*> y rt) 
    where app (f, mk1) (z, mk2) = (f z, mk1 `mappend` mk2)

instance Monad m => Monad (Gen m) where
  return x = Gen (\_ -> return (x, mempty))
  Gen m >>= k = Gen (\rt -> do (x, mk1) <- m rt
                               (y, mk2) <- runGen (k x) rt
                               return (y, mk1 `mappend` mk2))

instance MonadIO m => MonadIO (Gen m) where
  liftIO m = Gen (\_ -> do x <- liftIO m
                           return (x, mempty))

instance MonadFix m => MonadFix (Gen m) where
  mfix f = Gen (\rt -> do rec rv@(x, stms) <- case f x of Gen m -> m rt
                          return rv)

instance MonadTrans Gen where
  lift m = Gen (\_ -> do x <- m
                         return (x, mempty))

instance Monad m => MonadWriter (Gen m) where
  type WriterType (Gen m) = MkStm

  tell w = Gen (\_ -> return ((), w))
  listen (Gen m) = Gen (\rt -> do x@(_, w) <- m rt
                                  return (x, w))
  pass (Gen m) = Gen (\rt -> do ((x, f), w) <- m rt
                                return (x, f w))

instance (Supplies m (Ident Var)) => Supplies (Gen m) (Ident Var) where
  fresh = lift fresh

instance Type.TypeEnvMonad m => Type.TypeEnvMonad (Gen m) where
  type EvalBoxingMode (Gen m) = Type.EvalBoxingMode m
  getTypeEnv = lift Type.getTypeEnv
  --assumeWithProperties v t b m =
  --  Gen $ \env -> Type.assumeWithProperties v t b (runGen m env)


execBuild :: Monad m => [ValueType] -> Gen m Stm -> m Stm
execBuild return_type m = do
  (stm, MkStm mk_stm) <- runGen m return_type
  return $ mk_stm stm

execBuild' :: Monad m => [ValueType] -> Gen m (Stm, a) -> m (Stm, a)
execBuild' return_type m = do
  ((stm, a), MkStm mk_stm) <- runGen m return_type
  return (mk_stm stm, a)

getReturnTypes :: Monad m => Gen m [ValueType]
getReturnTypes = Gen (\rt -> return (rt, mempty))

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
                   Bool         -- ^ Create a join call?
                -> [ParamVar]   -- ^ Live-out variables
                -> (Stm -> Gen m Stm) -- ^ Code using the continuation
                -> Gen m ()
getContinuation primcall live_outs f = Gen $ \return_type -> do
  -- Create a call to the continuation
  cont_var <- newAnonymousVar cont_var_type
  let cont_call =
        ReturnE $ CallA convention (VarV cont_var) (map VarV live_outs)
      
  -- Construct a statement that calls the continuation
  (stm, MkStm stms) <- runGen (f cont_call) return_type

  -- Construct entry points if needed
  let fun_type = closureFunctionType (map varType live_outs) return_type
  entry_points <-
    if primcall
    then return (internalError "getContinuation") -- Not used
    else mkEntryPoints False fun_type cont_var

  -- Put the continuation into a 'letrec' statement
  let stms' cont_stm = LetrecE (NonRec (Def cont_var cont_fun)) (stms stm)
        where
          cont_fun =
            if primcall
            then joinFun live_outs return_type cont_stm
            else closureFun entry_points live_outs return_type cont_stm
  
  return ((), MkStm stms')
  where
    !convention = if primcall then JoinCall else ClosureCall

    !cont_var_type = if primcall
                     then PrimType PointerType
                     else PrimType OwnedType

valFreeVars :: Val -> Set Var
valFreeVars val = 
  case val
  of VarV v    -> Set.singleton v
     RecV _ vs -> valsFreeVars vs
     LitV _    -> Set.empty

valsFreeVars :: [Val] -> Set Var
valsFreeVars vs = Set.unions (map valFreeVars vs)

atomFreeVars :: Atom -> Set Var
atomFreeVars atom =
  case atom
  of ValA vs        -> valsFreeVars vs
     CallA _ v vs   -> valsFreeVars (v:vs)
     PrimA _ vs     -> valsFreeVars vs
     PackA _ vs     -> valsFreeVars vs
     UnpackA _ v    -> valFreeVars v

stmFreeVars :: Stm -> Set Var
stmFreeVars stm =
  case stm
  of LetE params rhs body ->
       let body_fv = foldr Set.delete (stmFreeVars body) params
       in Set.union body_fv $ atomFreeVars rhs
     LetrecE (NonRec def) body ->
       let body_fv = stmFreeVars body
           fun_fv = funFreeVars $ definiens def
       in Set.delete (definiendum def) body_fv `Set.union` fun_fv
     LetrecE (Rec defs) body ->
       let fun_vars = map definiendum defs
           body_fv = stmFreeVars body
           funs_fvs = map (funFreeVars . definiens) defs
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

emitLetrec :: Monad m => Group FunDef -> Gen m ()
emitLetrec defs = emit $ LetrecE defs

-- | Generate a new closure-call lambda function.
--
--   Given a function that takes a name and constructs a new 'Fun' having 
--   that name, run the function with a new name and bind it with a
--   letrec.
emitLambda :: (Monad m, Supplies m (Ident Var)) => (Var -> m Fun) -> Gen m Var
emitLambda mk_function = do
  v <- newAnonymousVar (PrimType OwnedType)
  f <- lift $ mk_function v
  emit $ LetrecE (NonRec (Def v f))
  return v

-- | Create a piece of code that requires parameters.  If fewer arguments 
--   are passed than expected, a local function is generated.  Otherwise the
--   code is emitted directly.  
genLambdaOrCall :: (Monad m, Supplies m (Ident Var)) =>
                   [ValueType] -> [ValueType] -> ([Val] -> Gen m [Val])
                -> [Val] -> Gen m [Val]
genLambdaOrCall param_types return_types mk_code args
  | n_args == n_params =
      mk_code args

  | n_args < n_params = do
      -- Create a function that takes the extra parameters
      let extra_param_types = drop (length args) param_types
      extra_params <- mapM newAnonymousVar extra_param_types
      
      f <- emitLambda $ \v -> genClosureFun v extra_params return_types $ do
        ret_values <- mk_code (args ++ map VarV extra_params)
        return $ ReturnE $ ValA ret_values
      return [VarV f]
        
  | n_args > n_params = internalError "genLambdaOrCall: Too many arguments"
  where
    n_args = length args
    n_params = length param_types

genLambdaOrCall1 :: (Monad m, Supplies m (Ident Var)) =>
                    [ValueType] -> ValueType -> ([Val] -> Gen m Val)
                 -> [Val] -> Gen m Val
genLambdaOrCall1 parameter_types return_type mk_body args = do
  [x] <- genLambdaOrCall parameter_types [return_type]
         (\x -> liftM return $ mk_body x) args
  return x

genLambda :: (Monad m, Supplies m (Ident Var)) =>
             [ValueType] -> [ValueType] -> ([Val] -> Gen m [Val]) -> Gen m Val
genLambda parameter_types return_types mk_body = do
  [x] <- genLambdaOrCall parameter_types return_types mk_body []
  return x

-- | Create a lambda function whose body is generated by the given function
genLambdaStm :: (Monad m, Supplies m (Ident Var)) =>
                [ValueType] -> [ValueType] -> ([Val] -> Gen m Stm) -> Gen m Val
genLambdaStm parameter_types return_types mk_body = do
  params <- mapM newAnonymousVar parameter_types
  f <- emitLambda $ \v -> genClosureFun v params return_types $ do
    mk_body (map VarV params)
  return (VarV f)

-- | Generate a 'ThrowE' term.
--   Any subsequently generated code on the same control flow path
--   is discarded.
emitThrow :: Monad m => Val -> Gen m ()
emitThrow throw_value = emit $ \_ -> ThrowE throw_value

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

genSwitch :: (Monad m, Supplies m (Ident Var)) =>
             [ValueType]          -- ^ Result types of switch branches
          -> Val                  -- ^ Scrutinee
          -> [(Lit, Gen m [Val])] -- ^ Branches
          -> Gen m [Val]          -- ^ Generate code and return results
genSwitch result_types scr branches = do
  live_outs <- lift $ mapM newAnonymousVar result_types
  getContinuation False live_outs (make_switch live_outs)
  return $ map VarV live_outs
  where
    make_switch live_outs cont = Gen $ \rt -> do
      alts <- mapM (make_branch rt) branches 
      return (SwitchE scr alts, mempty)
      where
        make_branch rt (tag, mk_body) = do
          body <- execBuild rt $ do
            values <- mk_body
            bindAtom live_outs $ ValA values
            return cont
          return (tag, body)

builtinVar :: (LowLevelBuiltins -> Var) -> Val
builtinVar v = VarV $ llBuiltin v

genPrimFun :: Monad m => [ParamVar] -> [ValueType] -> Gen m Stm -> m Fun
genPrimFun params returns body =
  liftM (primFun params returns) $ execBuild returns body

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

primCastZ ty src
  | dst_sz /= src_sz = internalError "primCastZ"
  | dst_sgn == src_sgn = return src
  | LitV (IntL _ _ n) <- src =
      if n < smallestRepresentableInt src_sgn src_sz ||
         n > largestRepresentableInt src_sgn src_sz
      then internalError "primCastZ: Integer out of bounds"
      else let n' = case dst_sgn 
                    of Unsigned ->
                         if n >= 0 then n else n + intCardinality dst_sz 
                       Signed ->
                         if n > largestRepresentableInt Signed dst_sz
                         then n - intCardinality dst_sz
                         else n
           in return $! LitV $! IntL dst_sgn dst_sz n'
  | otherwise =
      emitAtom1 ty $ PrimA (PrimCastZ src_sgn dst_sgn dst_sz) [src]
  where
    PrimType (IntType dst_sgn dst_sz) = ty
    PrimType (IntType src_sgn src_sz) = valType src

primExtendZ ty src
  | dst_sgn /= src_sgn = internalError "primExtendZ"
  | dst_sz == src_sz = return src
  | LitV (IntL _ _ n) <- src =
      if n < smallestRepresentableInt src_sgn src_sz ||
         n > largestRepresentableInt src_sgn src_sz
      then internalError "primCastZ: Integer out of bounds"
      else let n' = if dst_sz > src_sz then n
                    else case dst_sgn
                         of Unsigned ->
                              -- Truncate
                              n .&. (intCardinality dst_sz - 1)
                            Signed ->
                              -- Signed truncate
                              let card = intCardinality dst_sz
                                  shifted_n =
                                    n + (card `shiftR` 1)
                                  shifted_n' = shifted_n .&. (card - 1)
                              in shifted_n' - (card `shiftR` 1)
           in return $! LitV $! IntL dst_sgn dst_sz n'
  | otherwise =
      emitAtom1 ty $ PrimA (PrimExtendZ src_sgn src_sz dst_sz) [src]
  where
    PrimType (IntType dst_sgn dst_sz) = ty
    PrimType (IntType src_sgn src_sz) = valType src

primAddZ = intBinaryPrimOp (+) (Just 0) (Just 0) PrimAddZ
primSubZ = intBinaryPrimOp (-) Nothing (Just 0) PrimSubZ
primMulZ = intBinaryPrimOp (*) (Just 1) (Just 1) PrimMulZ
primModZ = intBinaryPrimOp mod Nothing Nothing PrimModZ
primMaxZ = intBinaryPrimOp max Nothing Nothing PrimMaxZ

primNegateZ prim_type@(PrimType (IntType sign size)) n =
  primSubZ prim_type (LitV $ IntL sign size 0) n

primCmpZ prim_type@(PrimType (IntType sign size)) comparison x y =
  emitAtom1 (PrimType BoolType) $ PrimA (PrimCmpZ sign size comparison) [x, y]

primCmpP comparison x y =
  emitAtom1 (PrimType BoolType) $ PrimA (PrimCmpP comparison) [x, y]

primAnd x y 
  | LitV (BoolL True) <- x  = return y
  | LitV (BoolL False) <- x = return x
  | LitV (BoolL True) <- y  = return x
  | LitV (BoolL False) <- y = return y
  | otherwise = emitAtom1 (PrimType BoolType) $ PrimA PrimAnd [x, y]

primAddP ptr off =
  let ptr_kind = case valType ptr of PrimType pt -> pointerKind pt
  in emitAtom1 (PrimType $ fromPointerKind $ addPResultType ptr_kind) $
     PrimA (PrimAddP ptr_kind) [ptr, off]

primAddPAs ptr off ptr' =
  let ptr_kind = case valType ptr of PrimType pt -> pointerKind pt
  in bindAtom1 ptr' $ PrimA (PrimAddP ptr_kind) [ptr, off]

primLoadAs mut ty ptr dst = primLoadOffAs mut ty ptr (nativeIntV 0) dst
primLoadOffAs mut ty ptr off dst
  | valType off /= PrimType nativeIntType =
      internalError "primLoadOff: Offset has wrong type"
  | otherwise =
      let ptr_kind = case valType ptr of PrimType pt -> pointerKind pt
      in bindAtom1 dst $ PrimA (PrimLoad mut ptr_kind ty) [ptr, off]

primLoadMutableAs ty ptr dst = primLoadAs Mutable ty ptr dst
primLoadOffMutableAs ty ptr off dst = primLoadOffAs Mutable ty ptr off dst
primLoadConstAs ty ptr dst = primLoadAs Constant ty ptr dst
primLoadOffConstAs ty ptr off dst = primLoadOffAs Constant ty ptr off dst

primLoad mut ty ptr = primLoadOff mut ty ptr (nativeIntV 0)
primLoadOff mut ty ptr off = do
  v <- lift (newAnonymousVar ty)
  primLoadOffAs mut ty ptr off v
  return (VarV v)

primLoadMutable ty ptr = primLoad Mutable ty ptr
primLoadOffMutable ty ptr off = primLoadOff Mutable ty ptr off
primLoadConst ty ptr = primLoad Constant ty ptr
primLoadOffConst ty ptr off = primLoadOff Constant ty ptr off

primStore mut ty ptr val = primStoreOff mut ty ptr (nativeIntV 0) val
primStoreOff mut ty ptr off val =
  let ptr_kind = case valType ptr of PrimType pt -> pointerKind pt
  in emitAtom0 $ PrimA (PrimStore mut ptr_kind ty) [ptr, off, val]

primStoreMutable ty ptr val = primStore Mutable ty ptr val
primStoreOffMutable ty ptr off val = primStoreOff Mutable ty ptr off val
primStoreConst ty ptr val = primStore Constant ty ptr val
primStoreOffConst ty ptr off val = primStoreOff Constant ty ptr off val

primCastToOwned ptr =
  emitAtom1 (PrimType OwnedType) $ PrimA PrimCastToOwned [ptr]

primCastFromOwned ptr =
  emitAtom1 (PrimType OwnedType) $ PrimA PrimCastFromOwned [ptr]

-- | Convert any integral type to a boolean
primIntToBool val =
  let ty@(PrimType (IntType sgn sz)) = valType val
  in primCmpZ ty CmpNE val (LitV $ IntL sgn sz 0)

-- | Convert a boolean to any integral type
primBoolToInt ty@(PrimType (IntType sgn sz)) val =
  let zero = LitV $ IntL sgn sz 0
      one = LitV $ IntL sgn sz 1
  in emitAtom1 ty $ PrimA (PrimSelect ty) [val, zero, one]

isZeroLit (LitV (IntL _ _ 0)) = True
isZeroLit _ = False

primAAddZ prim_type@(PrimType (IntType sign size)) ptr n =
  emitAtom1 prim_type $ PrimA (PrimAAddZ sign size) [ptr, n]

nativeAddZ = primAddZ (PrimType nativeIntType)
nativeSubZ = primSubZ (PrimType nativeIntType)
nativeMulZ = primMulZ (PrimType nativeIntType)
nativeModZ = primModZ (PrimType nativeIntType)
nativeMaxZ = primMaxZ (PrimType nativeIntType)
nativeNegateZ = primNegateZ (PrimType nativeIntType)

nativeAddUZ = primAddZ (PrimType nativeWordType)
nativeSubUZ = primSubZ (PrimType nativeWordType)
nativeMulUZ = primMulZ (PrimType nativeWordType)
nativeModUZ = primModZ (PrimType nativeWordType)
nativeMaxUZ = primMaxZ (PrimType nativeWordType)
nativeNegateUZ = primNegateZ (PrimType nativeWordType)

nativeWordL :: Integral a => a -> Lit
nativeWordL n 
  | not $ isRepresentableInt Unsigned nativeIntSize (fromIntegral n) =
      internalError "nativeWordL: Integer out of range"
  | otherwise = IntL Unsigned nativeIntSize (fromIntegral n)

nativeWordV :: Integral a => a -> Val
nativeWordV n = LitV $ nativeWordL n

nativeIntL :: Integral a => a -> Lit
nativeIntL n
  | not $ isRepresentableInt Signed nativeIntSize (fromIntegral n) =
      internalError "nativeIntL: Integer out of range"
  | otherwise = IntL Signed nativeIntSize (fromIntegral n)

nativeIntV :: Integral a => a -> Val
nativeIntV n = LitV $ nativeIntL n

uint8V :: Integral a => a -> Val
uint8V n
  | not $ isRepresentableInt Unsigned S8 (fromIntegral n) =
      internalError "uint8V: Integer out of range"
  | otherwise = LitV $ IntL Unsigned S8 $ fromIntegral n

uint16V :: Integral a => a -> Val
uint16V n
  | not $ isRepresentableInt Unsigned S16 (fromIntegral n) =
      internalError "uint16V: Integer out of range"
  | otherwise = LitV $ IntL Unsigned S16 $ fromIntegral n

funArityV :: Int -> Val
funArityV n =
  let IntType sgn sz = funArityType
  in LitV $ IntL sgn sz $ fromIntegral n

booleanV :: Bool -> Val
booleanV b = LitV (BoolL b)

-------------------------------------------------------------------------------
-- List operations


primAll :: (Monad m, Supplies m (Ident Var)) =>
           (a -> Gen m Val) -> [a] -> Gen m Val
primAll f xs = foldM primAnd (booleanV True) =<< mapM f xs

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
  toDynamicRecord recd = let
    fs = map toDynamicField $ recordFields recd
    size = nativeWordV $ recordSize recd
    alignment = nativeWordV $ recordAlignment recd
    in record fs size alignment

  toDynamicField (Field off m ty) =
    Field (nativeIntV off) m (toDynamicFieldType ty)

  toDynamicFieldType (PrimField t) = PrimField t
  toDynamicFieldType (RecordField recd) = RecordField $ toDynamicRecord recd
  toDynamicFieldType (BytesField s a) =
        BytesField (nativeWordV s) (nativeWordV a)

-- | Pack a pass-by-value record
packRecord :: (Monad m, Supplies m (Ident Var)) =>
              StaticRecord -> [Val] -> Gen m Val
packRecord rtype fields = emitAtom1 (RecordType rtype) $ PackA rtype fields

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
         RecordField rtype -> newAnonymousVar (RecordType rtype)
         BytesField {} -> internalError "unpackRecord"

-- | Unpack a pass-by-value record
unpackRecord2 :: (Monad m, Supplies m (Ident Var)) =>
                 StaticRecord -> Val -> Gen m [Val]
unpackRecord2 rtype val = liftM (map VarV) $ unpackRecord rtype val

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
     RecordField r  -> recordSize r
     BytesField s _ -> s
     AlignField _   -> nativeWordV 0

dynamicFieldTypeAlignment :: (ToDynamicRecordData a) => FieldType a -> Val
dynamicFieldTypeAlignment (toDynamicFieldType -> ft) =
  case ft
  of PrimField vt   -> nativeWordV $ alignOf vt
     RecordField r  -> recordAlignment r
     BytesField _ a -> a
     AlignField a   -> a

createConstDynamicRecord :: forall m. (Monad m, Supplies m (Ident Var)) =>
                            [DynamicFieldType] -> Gen m DynamicRecord
createConstDynamicRecord fs = createDynamicRecord [(Constant, f) | f <- fs]

createMutableDynamicRecord :: forall m. (Monad m, Supplies m (Ident Var)) =>
                            [DynamicFieldType] -> Gen m DynamicRecord
createMutableDynamicRecord fs = createDynamicRecord [(Mutable, f) | f <- fs]

-- | Create a dynamic record.  Given the record field types, the offsets of
-- all fields are computed and returned.  Code is emitted to compute the
-- offsets.
createDynamicRecord :: forall m. (Monad m, Supplies m (Ident Var)) =>
                       [(Mutability, DynamicFieldType)] -> Gen m DynamicRecord
createDynamicRecord field_types = do
  -- Compute record size and field offsets
  (offsets, size, alignment) <-
    compute_offsets [] zero one (map snd field_types)
  
  -- Create the record
  let fields = [mkDynamicField o m t
               | (o, (m, t)) <- zip offsets field_types,
                 not $ isAlignField t]
  return $ record fields size alignment
  where
    zero = nativeIntV 0
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
      i_size <- primCastZ (PrimType nativeIntType) $ dynamicFieldTypeSize field
      end_offset <- nativeAddZ start_offset i_size
      next_align <- nativeMaxUZ cur_align $ dynamicFieldTypeAlignment field
      compute_offsets (start_offset : offsets) end_offset next_align fields

    compute_offsets offsets cur_offset cur_align [] = do
      return (reverse offsets, cur_offset, cur_align)

-- | Create a dynamic record with only one field.  No code is generated.
singletonDynamicRecord :: Mutability -> DynamicFieldType -> DynamicRecord
singletonDynamicRecord mut field_type =
  let fields = [mkField' (nativeIntV 0) mut field_type]
      size = dynamicFieldTypeSize field_type
      align = dynamicFieldTypeAlignment field_type
  in record fields size align

suspendedCreateConstDynamicRecord :: forall m m'.
                                     (Monad m, Supplies m (Ident Var),
                                      Monad m', Supplies m' (Ident Var)) =>
                                     [DynamicFieldType]
                                  -> m (Gen m' (), DynamicRecord)
suspendedCreateConstDynamicRecord fs =
  suspendedCreateDynamicRecord [(Constant, f) | f <- fs]

-- | Create a dynamic record, but don't generate the code for it now.
--   Returns a dynamic record, and a code generator that computes values used
--   in the record.  The code generator calls 'createDynamicRecord'.
suspendedCreateDynamicRecord :: forall m m'.
                                (Monad m, Supplies m (Ident Var),
                                 Monad m', Supplies m' (Ident Var)) =>
                                [(Mutability, DynamicFieldType)]
                             -> m (Gen m' (), DynamicRecord)
suspendedCreateDynamicRecord field_types = do
  -- Create variables to stand for size, alignment, and field offsets
  -- that will be computed later
  size_v <- newAnonymousVar (PrimType nativeWordType)
  align_v <- newAnonymousVar (PrimType nativeWordType)
  offsets <- replicateM (length field_types) $
             newAnonymousVar (PrimType nativeIntType)
  let fields = [ mkDynamicField (VarV off) m o
               | (off, (m, o)) <- zip offsets field_types]
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
addRecordPadding off alignment 
  | valType off /= PrimType nativeIntType =
      internalError "addRecordPadding: Offset has wrong type"
  | otherwise = do
      neg_off <- nativeNegateZ off
      i_alignment <- primCastZ (PrimType nativeIntType) alignment
      disp <- neg_off `nativeModZ` i_alignment
      off `nativeAddZ` disp

fromPrimType :: DynamicFieldType -> ValueType
fromPrimType (PrimField ty) = PrimType ty
fromPrimType (RecordField recd) =
  let sz = from_lit $ recordSize recd
      al = from_lit $ recordAlignment recd
      fs = map from_dynamic_field $ recordFields recd
  in RecordType $ record fs sz al
  where
    from_dynamic_field fld =
      mkField (from_lit $ fieldOffset fld) (fieldMutable fld) (valueToFieldType $ fromPrimType $ fieldType fld)

    from_lit (LitV (IntL _ _ n)) = fromIntegral n
    from_lit _ = internalError "fromPrimType: Unexpected non-constant value"

fromPrimType _ = internalError "Expecting a primitive field type"

-- | Load one field of a record into a variable
loadField :: (Monad m, Supplies m (Ident Var), ToDynamicRecordData a) =>
             Field a -> Val -> Gen m Val
loadField (toDynamicField -> field) ptr = do
  let off = fieldOffset field
      mut = fieldMutable field
      ty = fromPrimType $ fieldType field
  primLoadOff mut ty ptr off

-- | Load an owned field as a non-owned pointer.  Reference counts will not 
-- be tracked or adjusted.
loadFieldWithoutOwnership :: (Monad m, Supplies m (Ident Var),
                              ToDynamicRecordData a) =>
                             Field a -> Val -> Gen m Val
loadFieldWithoutOwnership (toDynamicField -> field) ptr = do
  let off = fieldOffset field
      mut = fieldMutable field

  -- Must be an owned field
  case fieldType field of
    PrimField OwnedType -> return ()
    _ -> internalError "loadFieldWithoutOwnership: Wrong type"

  primLoadOff mut (PrimType PointerType) ptr off

-- | Load one field of a record into a local variable
loadFieldAs :: (Monad m, Supplies m (Ident Var), ToDynamicRecordData a) =>
               Field a -> Val -> Var -> Gen m ()
loadFieldAs (toDynamicField -> field) ptr dst =
  let off = fieldOffset field
      mut = fieldMutable field
      ty = fromPrimType $ fieldType field
  in primLoadOffAs mut ty ptr off dst

-- | Store into one field of a record
storeField :: (Monad m, Supplies m (Ident Var), ToDynamicRecordData a) =>
              Field a -> Val -> Val -> Gen m ()
storeField (toDynamicField -> field) ptr value =
  let off = fieldOffset field
      mut = fieldMutable field
      ty = fromPrimType $ fieldType field
  in primStoreOff mut ty ptr off value

-- | Get a pointer to a field of a record, given the base pointer.
referenceField :: (Monad m, Supplies m (Ident Var), ToDynamicRecordData a) =>
                  Field a -> Val -> Gen m Val
referenceField (toDynamicField -> field) ptr = primAddP ptr $ fieldOffset field

-- | Convert a value to its promoted form.
--   The value must be a primitive type, not a record type.
promoteVal :: (Monad m, Supplies m (Ident Var)) =>
              Val -> Gen m Val
promoteVal v
  | original_type == promoted_type = return v
  | otherwise =
    case original_type
    of BoolType ->
         -- Promote to native int
         primBoolToInt (PrimType nativeIntType) v
       IntType Signed _ ->
         primExtendZ (PrimType promoted_type) v
       IntType Unsigned sz ->
         -- Zero-extend, then cast to signed int
         let IntType Signed sz' = promoted_type
         in primExtendZ (PrimType $ IntType Unsigned sz') v >>=
            primCastZ (PrimType promoted_type)
       _ -> internalError "promoteVal: Not implemented for this type"
  where
    original_type =
      case valType v
      of PrimType pt -> pt
         RecordType _ -> internalError "promoteVal: Not a primtype"

    promoted_type = promoteType original_type

-- | Convert a value from its promoted form to its demoted form.
--   The value must be a primitive type, not a record type.
demoteVal :: (Monad m, Supplies m (Ident Var)) =>
             PrimType -> Val -> Gen m Val
demoteVal original_type v
  | original_type == promoted_type = return v
  | otherwise =
    case original_type
    of BoolType ->
         -- Demote native int to boolean
         primIntToBool v
       IntType Signed _ ->
         primExtendZ (PrimType original_type) v
       IntType Unsigned sz ->
         -- Cast to unsigned int, then truncate
         let IntType Signed sz' = promoted_type
         in primCastZ (PrimType $ IntType Unsigned sz') v >>=
            primExtendZ (PrimType original_type)
       _ -> internalError "demoteVal: Not implemented for this type"
  where
    promoted_type = promoteType original_type

-------------------------------------------------------------------------------
-- Other operations

-- | Helper function for 'allocateHeapMem' and friends.
allocate_with_dst f = do
  dst_var <- lift $ newAnonymousVar (PrimType PointerType)
  f dst_var
  return (VarV dst_var)

-- | Allocate the given number of bytes on the heap, deciding based on a
--   value whether the data may contain pointers. 
allocateHeapMem :: (Monad m, Supplies m (Ident Var)) =>
                   Val          -- ^ Size of heap data (uint)
                -> Val          -- ^ Whether data is pointerless (bool)
                -> Gen m Val
allocateHeapMem size is_pointerless =
  allocate_with_dst (allocateHeapMemAs size is_pointerless)

allocateHeapMemComposite :: (Monad m, Supplies m (Ident Var)) =>
                            Val -> Gen m Val
allocateHeapMemComposite size =
  allocate_with_dst (allocateHeapMemCompositeAs size)

allocateHeapMemPointerless :: (Monad m, Supplies m (Ident Var)) =>
                              Val -> Gen m Val
allocateHeapMemPointerless size =
  allocate_with_dst (allocateHeapMemPointerlessAs size)

allocateHeapMemAs :: (Monad m, Supplies m (Ident Var)) =>
                     Val        -- ^ Size of heap data (uint)
                  -> Val        -- ^ Whether data is pointerless (bool)
                  -> Var        -- ^ Output variable
                  -> Gen m ()
allocateHeapMemAs size is_pointerless dst =
  getContinuation True [dst] $ \cont ->
  genIf is_pointerless (pointerless >> return cont) (composite >> return cont)
  where
    composite = allocateHeapMemCompositeAs size dst
    pointerless = allocateHeapMemPointerlessAs size dst

allocateHeapMemCompositeAs size dst =
  bindAtom1 dst $ primCallA (builtinVar the_prim_triolet_alloc) [size]

allocateHeapMemPointerlessAs size dst =
  bindAtom1 dst $ primCallA (builtinVar the_prim_triolet_alloc_nopointers) [size]

deallocateHeapMem :: (Monad m, Supplies m (Ident Var)) => Val -> Gen m ()
deallocateHeapMem ptr =
  emitAtom0 $ primCallA (builtinVar the_prim_triolet_dealloc) [ptr]

-------------------------------------------------------------------------------
-- Manipulating objects

-- | Load an object header
readObjectHeader ptr = primLoadConst (PrimType OwnedType) ptr

-- | Write an object header
writeObjectHeader ptr val = primStoreConst (PrimType OwnedType) ptr val

-- | Read a function's info table reference.
--   This can also be used on PAPs.  The returned value will contain
--   NULL at run time if the argument is a PAP.
readFunInfoTable = loadField (localClosureRecord0 !!: 1)
refFunCapturedVars captured = referenceField (localClosureRecord captured !!: 2)

writeFunInfoTable = storeField (localClosureRecord0 !!: 1)

readInfoTableArity = loadField (infoTableRecord0 !!: 0)
readInfoTableCaptureCount = loadField (infoTableRecord0 !!: 1)
readInfoTableExact = loadField (infoTableRecord0 !!: 2)
readInfoTableInexact = loadField (infoTableRecord0 !!: 3)
refInfoTableTags captured = referenceField (infoTableRecord captured !!: 4)

writeInfoTableArity = storeField (infoTableRecord0 !!: 0)
writeInfoTableExact = storeField (infoTableRecord0 !!: 1)
writeInfoTableInexact = storeField (infoTableRecord0 !!: 2)

readPapOperator = loadField (papRecord0 !!: 2)
readPapArity = loadField (papRecord0 !!: 3)
readPapOperand t = loadField (papRecord t !!: 4)

writePapPapTag ptr = storeField (papRecord0 !!: 0) ptr (LitV NullL)

selectTypeObjectConIndex = loadField (toDynamicRecord typeObjectRecord !!: 1)

writeLazyValue t = storeField (lazyRecord t !!: 2)

readLazyValue t = loadField (lazyRecord t !!: 2)

-------------------------------------------------------------------------------
-- Values

genClosureFun :: (Monad m, Supplies m (Ident Var)) =>
                 Var -> [ParamVar] -> [ValueType] -> Gen m Stm -> m Fun
genClosureFun v params returns body =
  newClosureFun v params returns =<< execBuild returns body

-- | Generate a new closure-call function with the given variable name.
--   Variables are created for each entry point.
newClosureFun :: (Monad m, Supplies m (Ident Var)) =>
                 Var -> [ParamVar] -> [ValueType] -> Stm -> m Fun
newClosureFun name params returns body = do
  let fun_type = closureFunctionType (map varType params) returns
  ep <- mkEntryPoints False fun_type name
  return $ closureFun ep params returns body

-- | Create an 'EntryPoints' data structure for an externally visible
-- global function and populate it with new variables.
--
-- TODO: merge with mkEntryPoints
mkGlobalEntryPoints :: (Monad m, Supplies m (Ident Var)) =>
                       FunctionType   -- ^ Function type
                    -> Label          -- ^ Function name
                    -> Var            -- ^ Global closure variable
                    -> m EntryPoints  -- ^ Creates an EntryPoints structure
mkGlobalEntryPoints ftype label global_closure
  | not $ ftIsClosure ftype =
    internalError $
    "mkGlobalEntryPoints: Not a closure function: " ++ show global_closure
  | isJust $ labelExternalName label =
    -- Closure-call functions cannot be externally visible
    internalError $
    "mkGlobalEntryPoints: Closure function has external name: " ++ show global_closure
  | Just name <- varName global_closure, 
    any isEntryPointTag $ labelTags name =
    internalError $
    "mkGlobalEntryPoints: Invalid variable name"
  | otherwise = do
      inf <- make_entry_point InfoTableLabel
      dir <- make_entry_point DirectEntryLabel
      exa <- make_entry_point ExactEntryLabel
      ine <- make_entry_point InexactEntryLabel
      let arity = length $ ftParamTypes ftype
      return $! EntryPoints ftype arity dir Nothing exa ine inf global_closure
  where
    -- If the global closure is externally visible, the other entry points
    -- will also be externally visible
    make_entry_point tag =
      let new_label = appendLabelTag tag label
      in if varIsExternal global_closure
         then newExternalVar new_label (PrimType PointerType)
         else newVar (Just new_label) (PrimType PointerType)

-- | Create an 'EntryPoints' data structure for a non-externally-visible
-- global function.
mkEntryPoints :: (Monad m, Supplies m (Ident Var)) =>
                 Bool           -- ^ If true, create a vector entry point
              -> FunctionType   -- ^ Function type
              -> Var            -- ^ Global closure variable
              -> m EntryPoints  -- ^ Creates an EntryPoints structure
mkEntryPoints False ftype global_closure
  | not $ ftIsClosure ftype =
    internalError "mkEntryPoints: Not a closure function"
  | Just label <- varName global_closure,
    isJust $ labelExternalName label =
    -- Closure-call functions cannot be externally visible
    internalError $
    "mkGlobalEntryPoints: Closure function has external name: " ++ show global_closure
  | Just label <- varName global_closure, 
    any isEntryPointTag $ labelTags label =
    internalError $
    "mkGlobalEntryPoints: Invalid variable name"
  | otherwise = do
      let label = varName global_closure
      inf <- make_entry_point label InfoTableLabel
      dir <- make_entry_point label DirectEntryLabel
      exa <- make_entry_point label ExactEntryLabel
      ine <- make_entry_point label InexactEntryLabel
      let arity = length $ ftParamTypes ftype
      return $! EntryPoints ftype arity dir Nothing exa ine inf global_closure
  where
    -- If the global closure is externally visible, the other entry points
    -- will also be externally visible
    make_entry_point m_label tag =
      let new_label = fmap (appendLabelTag tag) m_label
      in if varIsExternal global_closure
         then let Just l = new_label 
              in newExternalVar l (PrimType PointerType)
         else newVar new_label (PrimType PointerType)
      --in newVar new_label (PrimType PointerType)
