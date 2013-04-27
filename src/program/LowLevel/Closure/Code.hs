
{-# LANGUAGE FlexibleInstances, Rank2Types #-}
module LowLevel.Closure.Code
       (CC, GenM,
        runCC,
        writeFun,
        writeData,
        lookupCCInfo,
        withCCInfo,
        LocalClosureTempData,
        allocateLocalClosures,
        populateLocalClosures,
        emitClosureGlobalData,
        genClosureCall,
        genPrimCall,
        genJoinCall,
        genIndirectCall,
        genVarRef
       )
where

import Control.Monad
import Control.Monad.Fix
import Control.Monad.Trans
import qualified Data.IntSet as IntSet
import qualified Data.Map as Map
import qualified Data.Set as Set
import Debug.Trace

import Common.Error
import Common.Supply
import Common.Identifier

import LowLevel.Build
import LowLevel.Builtins
import LowLevel.Print
import LowLevel.Records
import LowLevel.RecordFlattening
import LowLevel.FreshVar
import LowLevel.CodeTypes
import LowLevel.Syntax
import LowLevel.Closure.CCInfo

-- | The monad used when closure-converting a top-level definition group.
--
-- When scanning part of a program, closure conversion keeps track of the 
-- set of free variables referenced in that part of the program.
-- The set of free variables when scanning a function--that is,
-- the variables that are used by the function, but not a parameter of 
-- the function--are the captured variables.  Globals
-- are not included in the free variables set because they cannot be captured.
--
-- During scanning, all functions (including local and global functions) 
-- are written out as global definitions.  These definitions are assembled
-- into the body of the closure-converted module.
newtype CC a = CC (CCEnv -> IO (a, [GlobalDef]))

data CCEnv =
  CCEnv
  { envVarIDSupply :: {-# UNPACK #-}!(IdentSupply Var)
    -- | IDs of global variables.  Global variables are never captured.
  , envGlobals :: !IntSet.IntSet
    -- | Information about the closure-converted form of functions that are
    --   in scope
  , envEntryPoints :: Map.Map Var CCInfo
  }

-- | For generating closure-converted code in the CC monad
type GenM a = Gen CC a

emptyCCEnv var_ids globals imps =
  let globals_set = IntSet.fromList $ map (fromIdent . varID) globals
  in CCEnv var_ids globals_set imps

-- | Run some closure-conversion code
runCC :: IdentSupply Var        -- ^ Variable ID supply
      -> Set.Set Var            -- ^ Global variables
      -> Map.Map Var CCInfo     -- ^ Imported function descriptions
      -> CC a                   -- ^ Computation to run
      -> IO (a, [GlobalDef])    -- ^ Compute new global definitions 
runCC var_ids globals imps (CC f) = do
  let global_ids = IntSet.fromList $ map (fromIdent . varID) $ Set.toList globals
      env = CCEnv var_ids global_ids imps
  f env

returnCC :: a -> IO (a, [GlobalDef])
returnCC x = return (x, [])

instance Functor CC where
  fmap f (CC x) = CC $ \env -> do (y, b) <- x env
                                  return (f y, b)

instance Monad CC where
  return x = CC $ \_ -> returnCC x
  CC f >>= k = CC $ \env -> do
    (x, defs1) <- f env
    case k x of
      CC g -> do
        (y, defs2) <- g env
        return (y, defs1 ++ defs2)

instance MonadIO CC where
  liftIO m = CC $ \_ -> m >>= returnCC

instance MonadFix CC where
  mfix f = CC $ \env -> mfix $ \ ~(x, _) -> case (f x) of CC f' -> f' env

instance Supplies CC (Ident Var) where
  fresh = CC $ \env -> returnCC =<< supplyValue (envVarIDSupply env)

liftFreshVarM :: FreshVarM a -> CC a
liftFreshVarM m = CC $ \env ->
  returnCC =<< runFreshVarM (envVarIDSupply env) m

liftT :: (forall a. CC a -> CC a) -> GenM a -> GenM a
liftT f m = do
  rt <- getReturnTypes
  (m1, x) <- lift $ f $ suspendGen rt m
  m1
  return x

lookupCCInfo :: Var -> CC (Maybe CCInfo)
lookupCCInfo v = CC $ \env -> returnCC $ Map.lookup v (envEntryPoints env)

withCCInfo :: [(Var, CCInfo)] -> CC a -> CC a
withCCInfo inf (CC f) = CC $ \env ->
  let local_env =
        env {envEntryPoints =
                foldr (uncurry Map.insert) (envEntryPoints env) inf}
  in f local_env

-- | Write some global object definitions
writeDefs :: [GlobalDef] -> CC ()
writeDefs defs = CC $ \_ ->
  return ((), defs) 

writeFun f = writeDefs [GlobalFunDef f]
writeData d = writeDefs [GlobalDataDef d]

-------------------------------------------------------------------------------
-- Dynamic closure creation

-- | Allocate a dynamic closure.
--   The closure's info pointer is initialized.  Other fields remain
--   uninitialized.
--
--   An owned reference to the closure is assigned to variable @v@. 
--   A pointer to the closure is returned.
allocateClosure :: EntryPoints -> StaticRecord -> Var -> GenM Val
allocateClosure ep closure_record v = do
  ptr <- allocateHeapMemComposite (nativeWordV $ sizeOf closure_record)

  -- Assign the type object and info table fields
  writeObjectHeader ptr (VarV $ llBuiltin the_bivar_triolet_typeObject_function)
  writeFunInfoTable ptr (VarV $ infoTableEntry ep)
  -- Captured variables are uninitialized
  
  -- Convert to an owned pointer
  bindAtom1 v $ PrimA PrimCastToOwned [ptr]
  return ptr

-- | Write captured variables into a record
populateCapturedVars :: [Var] -> StaticRecord -> Val -> GenM ()
populateCapturedVars captured captured_record ptr
  | length captured /= length captured_fields =
      internalError "populateCapturedVars"
  | otherwise = mapM_ write_var (zip captured captured_fields)
  where
    captured_fields = recordFields captured_record
    write_var (v, fld) = storeField fld ptr =<< promoteVal (VarV v)

-- | Read captured variables from a record.
--   The record contains promoted data types; these are demoted 
--   to the expected types.
readCapturedVars :: [PrimType] -> StaticRecord -> Val -> GenM [Val]
readCapturedVars cap_types cap_recd ptr
  | length cap_types /= length captured_fields =
      internalError "readCapturedVars"
  | otherwise = mapM read_var (zip cap_types captured_fields)
  where
    captured_fields = recordFields cap_recd
    read_var (ty, fld) = demoteVal ty =<< loadField fld ptr

-- | Populate the closure-captured variables of a dynamic closure
populateClosure :: [Var]        -- ^ Captured variables
                -> StaticRecord -- ^ Captured variable record
                -> StaticRecord -- ^ Closure record
                -> Val          -- ^ The closure to populate
                -> GenM ()
populateClosure captured captured_record clo_record ptr = do
  captured_ptr <- refFunCapturedVars clo_record ptr
  populateCapturedVars captured captured_record captured_ptr

-- | Allocate a closure if one is prescribed.
--   Save the closure pointer.
allocateClosureByCCInfo :: (Var, CCInfo) -> GenM (Var, Maybe Val, CCInfo)
allocateClosureByCCInfo (fun_name, inf) =
  case inf
  of LocalClosure { _cEntryPoints = ep
                  , _cRecord = recd
                  , _cWantClosure = True} -> do
       x <- allocateClosure ep recd fun_name
       return (fun_name, Just x, inf)
     LocalClosure {_cWantClosure = False} ->
       return (fun_name, Nothing, inf)
     LocalPrim {} ->
       return (fun_name, Nothing, inf)
     -- Other terms cannot occur for local variables
     _ ->
       internalError "allocateClosureByCCInfo: Unexpected value"

-- | Populate a closure if one is prescribed.
populateClosureByCCInfo :: (Var, Maybe Val, CCInfo) -> GenM ()
populateClosureByCCInfo (fun_name, m_closure_ptr, inf) =
  case inf
  of LocalClosure { _cRecord = recd
                  , _cClosureCaptured = cap
                  , _cClosureCapturedRecord = cap_recd
                  , _cWantClosure = True} ->
       case m_closure_ptr
       of Just closure_ptr ->
            populateClosure cap cap_recd recd closure_ptr
          Nothing -> internalError "populateClosureByCCInfo"
     LocalClosure {_cWantClosure = False} ->
       return ()
     LocalPrim {} ->
       return ()
     -- Other terms cannot occur for local variables
     _ ->
       internalError "populateClosureByCCInfo: Unexpected value"

-- | Temporary data produced when allocating local closures
type LocalClosureTempData = [(Var, Maybe Val, CCInfo)]

-- | Allocate memory for a group of local, possibly mutually recursive
--   closures corresponding to a definition group.  Captured variables
--   must be initialized by calling 'populateLocalClosures'.
--
--   For each @(Var, CCInfo)@ value, the variable will be defined with a
--   closure as specified by the @CCInfo@ value.
--
--   All recursive closures in the group must have the same
--   closure-captured variables.
allocateLocalClosures :: [(Var, CCInfo)] -> GenM LocalClosureTempData
allocateLocalClosures funs = mapM allocateClosureByCCInfo funs

-- | Assign captured variables in a group of local closures.
--   This creates valid closure objects.
populateLocalClosures :: LocalClosureTempData -> GenM ()
populateLocalClosures funs = mapM_ populateClosureByCCInfo funs

-------------------------------------------------------------------------------
-- Global data and functions created from closures

-- | Create a statically defined closure for a global function
mkGlobalClosure :: EntryPoints -> CC ()
mkGlobalClosure ep =
  let closure_values =
        [ VarV $ llBuiltin the_bivar_triolet_typeObject_function -- Object header
        , VarV $ infoTableEntry ep                 -- Info table
        , RecV (constStaticRecord []) []           -- No captured variables
        ]
      data_value = RecV (flattenStaticRecord globalClosureRecord)
                        (flattenGlobalValues closure_values)
  in writeData $ Def (globalClosure ep) (StaticData data_value)

-- | Create argument type tags for an info table entry.
--   The type tags are a sequence of bytes describing the function's
--   argument types, followed by a sequence of bytes describing the
--   function's closure contents.
mkArgumentTypeTags :: [ValueType] -> [ValueType] -> (StaticRecord, Val)
mkArgumentTypeTags arg_types clo_captured = (record_type, arg_type_val)
  where
    record_type = typeTagsRecord (length arg_types + length clo_captured)

    arg_type_tags =
      map (uint8V . fromEnum . toBitsTag . promoteType . valueToPrimType)
      (arg_types ++ clo_captured)

    arg_type_val = RecV record_type arg_type_tags

-- | Create an info table.  The info table contains data needed by the run-time
--   implementation of function currying.
mkInfoTable :: CCInfo -> CC ()
mkInfoTable cc = writeData $ Def info_table (StaticData static_value)
  where
    entry_points = ccEntryPoints cc
    info_table = infoTableEntry entry_points
    
    (type_tags_record, type_tags_value) =
      mkArgumentTypeTags (ccExactParamTypes cc) (map varType $ ccClosureCaptured cc)

    fun_info_type = infoTableRecord type_tags_record
    
    fun_info =
      RecV fun_info_type
      [ -- The arity will be different after closure conversion if there are
        -- any call-captured variables.  Use the number of arguments as the
        -- arity.
        funArityV $ length $ ccExactParamTypes cc
      , funArityV $ length $ ccClosureCaptured cc
      , VarV $ exactEntry entry_points
      , VarV $ inexactEntry entry_points
      , type_tags_value]

    static_value = RecV (flattenStaticRecord fun_info_type)
                        (flattenGlobalValue fun_info)

-- | Create an exact entry point for a closure-call function.
--
--   The exact entry point takes parameters
--   (other than closure-captured variables) and passes them on to the
--   direct entry point.
mkExactEntry :: CCInfo -> CC ()
mkExactEntry cc = do
  -- Parameters are the call-captured variables and original function parameters
  let param_types = ccExactParamTypes cc
  closure_ptr <- newAnonymousVar (PrimType OwnedType)
  params <- mapM newAnonymousVar param_types
  let return_types = ftReturnTypes ftype

  fun_body <- execBuild return_types $ do
    -- Load each closure-captured variable
    cap_vars <- load_captured_vars (VarV closure_ptr)
    
    -- Call the direct entry point
    let direct_entry = VarV $ directEntry $ ccEntryPoints cc
    return $ ReturnE $ primCallA direct_entry (cap_vars ++ map VarV params)
  
  let fun = primFun (closure_ptr : params) return_types fun_body
  writeFun $ Def (exactEntry $ ccEntryPoints cc) fun
  where
    ftype = ccType cc
    
    load_captured_vars closure_ptr =
      case cc
      of LocalClosure { _cRecord = recd
                      , _cClosureCaptured = captured_vars
                      , _cClosureCapturedRecord = captured_recd} -> do
           -- Load captured variables from the closure
           captured_ptr <- refFunCapturedVars recd closure_ptr
           let captured_types = map varPrimType captured_vars
           readCapturedVars captured_types captured_recd captured_ptr
         GlobalClosure {} ->
           -- Global closures don't capture variables
           return []

-- | Create an inexact entry point for a closure-call function.
--
-- The inexact entry point takes a PAP and an unitialized record to
-- hold function return values.  It extracts the parameters, demotes them,
-- and then calls the exact entry point.
-- It promotes the return values upon returning.
mkInexactEntry :: CCInfo -> CC ()
mkInexactEntry cc = do
  pap_ptr <- newAnonymousVar (PrimType OwnedType)
  returns_ptr <- newAnonymousVar (PrimType PointerType)
  fun_body <- execBuild [] $ do
    -- Load and demote parameter values from the PAP
    (param_vals, clo_ptr) <- unpackPapParameters cc (VarV pap_ptr)

    -- Call the exact entry
    let exact_entry = VarV $ exactEntry $ ccEntryPoints cc
    return_vals <- emitAtom (ftReturnTypes ftype) $
                   primCallA exact_entry (clo_ptr : param_vals)

    -- Store each return value
    store_returns (VarV returns_ptr) return_vals
    gen0

  let fun = primFun [pap_ptr, returns_ptr] [] fun_body
  writeFun $ Def (inexactEntry $ ccEntryPoints cc) fun
  where
    ftype = ccType cc

    store_returns returns_ptr return_vals =
      sequence [storeField fld returns_ptr =<< promoteVal val
               | (fld, val) <- zip (recordFields return_record) return_vals]

    -- Record type of returns
    return_record = promotedPrimTypesRecord Constant $
                    map valueToPrimType $
                    ftReturnTypes ftype

-- | Given a PAP that represents a fully applied function,
--   Extract all arguments and the function.
--
--   The argument is a chain of PAPs, with the last application at the
--   head of the chain.  Thus, walking the chain gives us the arguments
--   in reverse order, starting from the final argument.
--   This function will put the arguments in the correct order before
--   returning them.
unpackPapParameters cc pap_ptr =
  -- Arguments are in reverse order, so reverse the list of parameter types
  go (reverse $ ccExactParamTypes cc) [] pap_ptr
  where
    go (param_type : pts) arguments pap_ptr = do
      -- Parameter must have a primitive type
      let PrimType param_prim_type = param_type
      let promoted_type = promoteType param_prim_type

      -- Load the operator and operand
      operator <- readPapOperator pap_ptr
      promoted_param <- readPapOperand promoted_type pap_ptr
      param <- demoteVal param_prim_type promoted_param

      -- Load remaining operands
      go pts (param : arguments) operator

    go [] arguments operator =
      -- All parameters have been read.  The operator is a function.
      return (arguments, operator)

-- | Emit global objects (other than the direct entry point) for a
--   function or procedure.
emitClosureGlobalData :: CCInfo -> CC ()
emitClosureGlobalData ccinfo =
  case ccinfo
  of GlobalClosure {_cEntryPoints = ep} -> do
       mkGlobalClosure ep
       mkInfoTable ccinfo
       mkExactEntry ccinfo
       mkInexactEntry ccinfo
     LocalClosure {_cEntryPoints = ep, _cWantClosure = True} -> do
       mkInfoTable ccinfo
       mkExactEntry ccinfo
       mkInexactEntry ccinfo
     
     -- Primitive functions, direct-called hoisted functions, and 
     -- jump targets don't have any global data
     LocalClosure {_cEntryPoints = ep, _cWantClosure = False} ->
       return ()
     GlobalPrim {} ->
       return ()
     LocalPrim {} ->
       return ()

-------------------------------------------------------------------------------
-- Function calls

-- | Generate the closure-converted form of a closure-call to a
-- variable.  If the variable has a known direct entry point and is
-- applied to enough arguments, a direct call is generated.
-- Otherwise, an indirect call is generated.
genClosureCall :: [PrimType]        -- ^ Return types
               -> Var               -- ^ Function that is called
               -> [Val]             -- ^ Arguments
               -> GenM Atom
genClosureCall return_types fun args = do
  info <- lift $ lookupCCInfo fun
  case info of
    -- If function is unknown, generate an indirect function call
    Nothing -> indirect_call []
    
    -- If it's a closure-call function, generate a direct or indirect call
    -- depending on the number of arguments
    Just cc@(GlobalClosure {}) -> closure_call cc
    Just cc@(LocalClosure {}) -> closure_call cc
    
    -- If it's a prim-call function, the arguments must match exactly
    Just cc@(GlobalPrim {}) -> check_args cc $ prim_call fun cc
    Just cc@(LocalPrim {_cEntryPoint = ep}) -> check_args cc $ join_call ep cc
  where
    closure_call cc =
      case length args `compare` ccArity cc
      of LT | not (ccWantClosure cc) ->
           -- A closure record was not created for this function
           internalError "genClosureCall: Did not generate a closure"
         LT -> do               -- Undersaturated
           let call_captured = ccCallCaptured cc
           indirect_call (map VarV call_captured)
         EQ -> do               -- Saturated
           genDirectCall cc args
         GT -> do               -- Oversaturated
           -- Generate a direct call with the correct number of arguments.
           -- Then, call the return value with remaining arguments.
           let (direct_args, indir_args) = splitAt (ccArity cc) args
           app <- emitAtom1 (PrimType OwnedType) =<<
                  genDirectCall cc direct_args

           genIndirectCall return_types app indir_args

    indirect_call call_captured =
      genIndirectCall return_types (VarV fun) (call_captured ++ args)

    check_args cc k
      | length args /= (ccArity cc) =
          -- Error to call with the wrong number of arguments
          internalError "genClosureCall: Procedure call has wrong number of arguments"
      | otherwise = k

    prim_call entry_point cc =
      return $ primCallA (VarV entry_point) args

    join_call entry_point cc =
      let call_captured = map VarV (ccCallCaptured cc)
      in return $ joinCallA (VarV entry_point) (call_captured ++ args)

-- | Generate a call to a global procedure.
genPrimCall :: Var               -- ^ Function that is called
            -> [Val]             -- ^ Arguments
            -> GenM Atom
genPrimCall fun args = do
  info <- lift $ lookupCCInfo fun
  case info of
    -- If function is unknown, it doesn't capture variables
    Nothing -> return call

    -- If it's a prim-call function, generate a primitive call 
    Just cc@(GlobalPrim {}) -> return call

    -- Closure-call functions cannot be called with this calling convention
    Just _ -> internalError "genPrimCall"
  where
    call = primCallA (VarV fun) args

-- | Generate a call to a local procedure.
genJoinCall :: Var               -- ^ Function that is called
            -> [Val]             -- ^ Arguments
            -> GenM Atom
genJoinCall fun args = do
  info <- lift $ lookupCCInfo fun
  case info of
    Just cc@(LocalPrim {})  -> make_call $ ccCallCaptured cc

    -- Similar to 'genClosureCall'.
    -- Since join calls are always saturated, we can go directly to the
    -- saturated case.
    Just cc@(LocalClosure {}) -> genDirectCall cc args

    -- Closure-call functions cannot be called with this calling convention
    Just _ -> internalError "genJoinCall"
  where
    make_call extra_args =
      return $ joinCallA (VarV fun) (map VarV extra_args ++ args)

-- | Generate the closure-converted form of a variable reference.
--
--   If the variable has call-captured arguments, they are applied to the
--   variable.
genVarRef :: Var -> GenM Val
genVarRef fun = do
  info <- lift $ lookupCCInfo fun
  case info of
    Nothing -> return (VarV fun)
    Just cc | not $ ccIsClosure cc ->
      -- Cannot reference procedures except as the callee of a primcall
      internalError "genVarRef: Invalid procedure reference"
    Just cc | not $ ccWantClosure cc ->
      -- A closure record was not created for this function
      internalError "genVarRef: Did not generate a closure"
    Just cc ->
      case ccCallCaptured cc
      of [] -> return (VarV fun)
         capt ->
           -- The result of application must be a partially-applied function,
           -- therefore there must be some function parameters
           if null $ ftParamTypes $ ccType cc
           then internalError "genVarRef: Nullary function"
           else emitAtom1 (PrimType OwnedType) =<<
                genIndirectCall [OwnedType] (VarV fun) (map VarV capt)

genDirectCall :: CCInfo         -- ^ Closure conversion information
              -> [Val]          -- ^ Arguments
              -> GenM Atom
genDirectCall cc args =
  let captured = map VarV $ ccCaptured cc
      entry_point = directEntry $ ccEntryPoints cc
  in return $ primCallA (VarV entry_point) (captured ++ args)

-- | Generate the closure-converted form of a closure-call to an arbitrary 
--   callee.  This is done when the callee is unknown or when 'genClosureCall'
--   cannot produce a more efficient function call.
genIndirectCall :: [PrimType]     -- ^ Return types
                -> Val            -- ^ Callee
                -> [Val]          -- ^ Arguments
                -> GenM Atom

-- No arguments: Don't call
genIndirectCall return_types op [] = return $ ValA [op]

genIndirectCall return_types op args = do
  -- Get the function info table
  inf_ptr <- readFunInfoTable op

  -- Create branch target for inexact call
  ret_vars <- lift $ mapM newAnonymousVar return_value_types
  getContinuation True ret_vars $ \cont -> do
    inexact_target <- define_inexact_call ret_vars cont

    -- Is the callee a function?
    is_function <- primCmpP CmpNE inf_ptr (LitV NullL)
    genIf is_function
      (call_function cont ret_vars inexact_target inf_ptr)
      (goto_inexact_call inexact_target)
  return $ ValA (map VarV ret_vars)
  where
    return_value_types = map PrimType return_types
    given_arity = length args

    -- Callee is a function
    call_function cont ret_vars inexact_target inf_ptr = do
      -- Check whether function arity matches the number of given arguments
      arity <- readInfoTableArity inf_ptr
      is_saturated <- primCmpZ (PrimType funArityType) CmpEQ
                      arity (funArityV given_arity)

      -- If exact match, produce an exact call; otherwise, inexact call
      genIf is_saturated
        (exact_call ret_vars inf_ptr >> return cont)
        (goto_inexact_call inexact_target)

    goto_inexact_call inexact_target =
      return $ ReturnE $ joinCallA inexact_target []

    -- Create a local jump target that performs an inexact call
    define_inexact_call ret_vars cont = do
      inexact_target <- lift $ newAnonymousVar (PrimType PointerType)
      inexact_fun_body <- lift $ execBuild return_value_types $ do
        inexact_call ret_vars
        return cont
      let inexact_fun = joinFun [] return_value_types inexact_fun_body
      emitLetrec (NonRec (Def inexact_target inexact_fun))
      return (VarV inexact_target)
    
    -- An inexact function call
    inexact_call ret_vars = do
      -- Create temporary storage for promoted return values
      let ret_record = promotedPrimTypesRecord Constant return_types
      ret_ptr <- allocateHeapMemComposite $ nativeWordV $ recordSize ret_record
      
      -- Apply the function to all arguments
      genApply op args ret_ptr
      
      -- Extract and demote return values
      ret_vals <-
        sequence [demoteVal rtype =<< loadField fld ret_ptr
                 | (fld, rtype) <- zip (recordFields ret_record) return_types]

      -- Free temporary storage
      deallocateHeapMem ret_ptr
      
      -- Move return values to the expected variables
      bindAtom ret_vars $ ValA ret_vals
    
    -- An exact function call
    exact_call ret_vars inf_ptr = do
      -- Get the exact entry point
      fn <- readInfoTableExact inf_ptr

      -- Get the function's captured variables, then call the function
      bindAtom ret_vars $ primCallA fn (op : args)

-- | Create a dynamic function application.
genApply :: Val -> [Val] -> Val -> GenM ()
genApply _ [] _ = internalError "genApply: No arguments"
genApply f [x] ret_ptr = genApplyLast f x ret_ptr
genApply f (x:xs) ret_ptr = do f' <- genApply1 f x
                               genApply f' xs ret_ptr

-- Generate a partial application that returns a function
genApply1 f x = do
  -- Promote the argument
  promoted_x <- promoteVal x

  -- Decide which PAP to build depending on the argument type
  let op = case valType promoted_x
           of PrimType UnitType             -> llBuiltin the_prim_apply_u_f
              PrimType (IntType Signed S32) -> llBuiltin the_prim_apply_i32_f
              PrimType (FloatType S32)      -> llBuiltin the_prim_apply_f32_f
              PrimType PointerType          -> llBuiltin the_prim_apply_p_f
              PrimType OwnedType            -> llBuiltin the_prim_apply_o_f
              PrimType CursorType           -> llBuiltin the_prim_apply_c_f
              t -> internalError $ "genApply1: No method for " ++ show (pprValueType t)

  emitAtom1 (PrimType OwnedType) $ primCallA (VarV op) [promoted_x]

genApplyLast f x ret_ptr = do
  -- Promote the argument
  promoted_x <- promoteVal x

  -- Decide which PAP to build depending on the argument type
  let op = case valType promoted_x
           of PrimType UnitType             -> llBuiltin the_prim_apply_u
              PrimType (IntType Signed S32) -> llBuiltin the_prim_apply_i32
              PrimType (FloatType S32)      -> llBuiltin the_prim_apply_f32
              PrimType PointerType          -> llBuiltin the_prim_apply_p
              PrimType OwnedType            -> llBuiltin the_prim_apply_o
              PrimType CursorType           -> llBuiltin the_prim_apply_c
              t -> internalError $ "genApplyLast: No method for " ++ show (pprValueType t)

  emitAtom0 $ primCallA (VarV op) [promoted_x, ret_ptr]

{-
genApply fun args ret_ptr =
  gen_apply fun args (map (promotedTypeTag . valPrimType) args)
  where
    gen_apply fun args arg_types =
      -- If all arguments are consumed, then call apply_mem
      -- Otherwise, call apply_ret
      if null args'
      then do finish_apply (VarV apply_mem) fun app_args
      else do closure' <- partial_apply (VarV apply_ret) fun app_args
              gen_apply closure' args' arg_types'
      where
        (n, apply_ret, apply_mem) = pickApplyFun arg_types
        (app_args, args') = splitAt n args
        arg_types' = drop n arg_types

    -- Apply some arguments
    partial_apply f clo args =
      emitAtom1 (PrimType OwnedType) $ primCallA f (clo : args)

    -- Apply arguments and write result in to the return struct
    finish_apply f clo args =
      emitAtom0 $ primCallA f (clo : args ++ [ret_ptr])

-- | An apply trie node contains the apply functions for parameter sequences
-- with a common prefix of types.
--
-- The two variables at a node both are used for applying a parameter sequence
-- having these types.  They differ in how they return: the first returns an 
-- owned pointer, while the second writes its return values into memory.
data ApplyTrieNode = ApplyTrieNode !Var !Var !ApplyTrie 
type ApplyTrie = [(TypeTag, ApplyTrieNode)]

-- | Pick a function that can apply as many arguments as possible, given 
-- the argument types in the list.
pickApplyFun :: [TypeTag] -> (Int, Var, Var)
pickApplyFun tags =
  pick 0 err err tags applyFunctions
  where
    err :: forall a. a
    err = internalError "pickApplyFun: Cannot apply"

    pick n f g (tag:tags) trie =
      case lookup tag trie
      of Just (ApplyTrieNode f' g' trie') -> pick (n+1) f' g' tags trie'
         Nothing 
           | n == 0 -> err 
                       | otherwise -> (n, f, g)

    pick 0 f g [] _ = err
    pick n f g [] _ = (n, f, g)

-- | The available 'apply' functions
applyFunctions :: ApplyTrie
applyFunctions = [ (UnitTag, u_node)
                 , (Int32Tag, i32_node)
                 , (Float32Tag, f_node)
                 , (Int64Tag, i64_node)]
  where
    u_node = ApplyTrieNode
             (llBuiltin the_prim_apply_u_f)
             (llBuiltin the_prim_apply_u)
             []
    i32_node = ApplyTrieNode
             (llBuiltin the_prim_apply_i32_f) 
             (llBuiltin the_prim_apply_i32)
             []
    f_node = ApplyTrieNode
             (llBuiltin the_prim_apply_f32_f)
             (llBuiltin the_prim_apply_f32)
             []
    i64_node = ApplyTrieNode
               (llBuiltin the_prim_apply_i64_f)
               (llBuiltin the_prim_apply_i64)
               []
-}