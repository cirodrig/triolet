
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
import LowLevel.Records hiding(globalClosureRecord) -- TODO: remove these functions from the other module
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
-- Closure creation

-- | A global closure consists of only an object header
globalClosureRecord :: StaticRecord
globalClosureRecord = constStaticRecord [RecordField objectHeaderRecord]

-- | A dynamically created function closure consists of an object header and
--   some captured variables
dynamicClosureRecord :: StaticRecord -> StaticRecord
dynamicClosureRecord captured =
  constStaticRecord [ RecordField objectHeaderRecord
                    , RecordField captured]

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
  
  -- Assign the info pointer to field 0
  -- Other fields uninitialized
  header <- referenceField (closure_record !!: 0) ptr
  storeField (objectHeaderRecord !!: 0) ptr (VarV $ infoTableEntry ep)
  
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
    write_var (v, fld) = storeField fld ptr (VarV v)

-- | Populate the closure-captured variables of a dynamic closure
populateClosure :: [Var]        -- ^ Captured variables
                -> StaticRecord -- ^ Captured variable record
                -> StaticRecord -- ^ Closure record
                -> Val          -- ^ The closure to populate
                -> GenM ()
populateClosure captured captured_record clo_record ptr = do
  captured_ptr <- referenceField (clo_record !!: 1) ptr
  populateCapturedVars captured captured_record captured_ptr

-- | Allocate a closure if one is prescribed.
--   Save the closure pointer.
allocateClosureByCCInfo :: (Var, CCInfo) -> GenM (Var, Maybe Val, CCInfo)
allocateClosureByCCInfo (fun_name, inf) =
  case inf
  of LocalClosure {_cEntryPoints = ep, _cRecord = recd} -> do
       x <- allocateClosure ep recd fun_name
       return (fun_name, Just x, inf)
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
                  , _cClosureCapturedRecord = cap_recd} ->
       case m_closure_ptr
       of Just closure_ptr ->
            populateClosure cap cap_recd recd closure_ptr
          Nothing -> internalError "populateClosureByCCInfo"
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
        [RecV objectHeaderRecord $ objectHeaderData $ VarV $ infoTableEntry ep]
      static_value = StaticData
                     (flattenStaticRecord globalClosureRecord)
                     (flattenGlobalValues closure_values)
      var = case globalClosure ep
            of Just x -> x
               Nothing -> internalError "mkGlobalClosure"
  in writeData $ Def var static_value

-- | Create argument type tags for an info table entry.
--   The type tags are a sequence of bytes describing the function's
--   argument type.
mkArgumentTypeTags :: [ValueType] -> (StaticRecord, Val)
mkArgumentTypeTags arg_types = (record_type, arg_type_val)
  where
    record_type = typeTagsRecord (length arg_types)

    arg_type_tags =
      map (uint8V . fromEnum . toBitsTag . promoteType . valueToPrimType) arg_types
    
    arg_type_val = RecV record_type arg_type_tags

-- | Create an info table.  The info table contains data needed by the run-time
--   implementation of function currying.
mkInfoTable :: CCInfo -> CC ()
mkInfoTable cc = writeData $ Def info_table static_value
  where
    entry_points = ccEntryPoints cc
    info_table = infoTableEntry entry_points
    
    (type_tags_record, type_tags_value) =
      mkArgumentTypeTags $ ccExactParamTypes cc

    fun_info_type = funInfoHeaderRecord type_tags_record
    
    fun_info =
      RecV fun_info_type
      [ info_header
        -- The arity will be different after closure conversion if there are
        -- any call-captured variables.  Use the number of arguments as the
        -- arity.
      , uint16V $ length $ ccExactParamTypes cc
      , VarV $ exactEntry entry_points
      , VarV $ inexactEntry entry_points
      , type_tags_value]
      where
        info_header = RecV infoTableHeaderRecord [uint8V $ fromEnum FunTag]

    static_value = StaticData (flattenStaticRecord fun_info_type)
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
                      , _cClosureCapturedRecord = captured_recd} -> do
           -- Load captured variables from the closure
           captured_ptr <- referenceField (recd !!: 1) closure_ptr
           forM (recordFields captured_recd) $ \fld -> do
             loadField fld captured_ptr
         GlobalClosure {} ->
           -- Global closures don't capture variables
           return []

-- | Create an inexact entry point for a closure-call function.
--
-- The inexact entry point takes the closure, a record holding function
-- parameters, and an unitialized record to hold function return values.
--
-- The given parameters are promoted, and must be demoted before calling
-- the exact entry point.  The return values are promoted.
mkInexactEntry :: CCInfo -> CC ()
mkInexactEntry cc = do
  clo_ptr <- newAnonymousVar (PrimType OwnedType)
  params_ptr <- newAnonymousVar (PrimType PointerType)
  returns_ptr <- newAnonymousVar (PrimType PointerType)
  fun_body <- execBuild [] $ do
    -- Load and demote parameter values from the parameters record
    param_vals <- load_parameters (VarV params_ptr)

    -- Call the exact entry
    let exact_entry = VarV $ exactEntry $ ccEntryPoints cc
    return_vals <- emitAtom (ftReturnTypes ftype) $
                   primCallA exact_entry (VarV clo_ptr : param_vals)

    -- Store each return value
    store_returns (VarV returns_ptr) return_vals
    gen0

  let fun = primFun [clo_ptr, params_ptr, returns_ptr] [] fun_body
  writeFun $ Def (inexactEntry $ ccEntryPoints cc) fun
  where
    ftype = ccType cc

    load_parameters params_ptr =
      sequence [demoteVal (valueToPrimType param_type) =<< loadField fld params_ptr
               | (fld, param_type) <-
                   zip (recordFields param_record) param_types]

    store_returns returns_ptr return_vals =
      sequence [storeField fld returns_ptr =<< promoteVal val
               | (fld, val) <- zip (recordFields return_record) return_vals]

    -- Actual types of parameters (except for the closure pointer)
    param_types = ccExactParamTypes cc

    -- Record type of parameters
    param_record = papArgsRecord Constant $ map valueToPrimType param_types

    -- Record type of returns
    return_record = promotedPrimTypesRecord Constant $
                    map valueToPrimType $
                    ftReturnTypes ftype

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
     LocalClosure {_cEntryPoints = ep} -> do
       mkInfoTable ccinfo
       mkExactEntry ccinfo
       mkInexactEntry ccinfo
     
     -- Primitive functions or jump targets don't have any global data
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
    
    -- If it's a prim-call function, generate a primitive call 
    Just cc@(GlobalPrim {}) -> prim_call fun cc
    Just cc@(LocalPrim {_cEntryPoint = ep}) -> prim_call ep cc
  where
    arity cc = length (ftParamTypes $ ccType cc)

    closure_call cc =
      case length args `compare` arity cc
      of LT -> do               -- Undersaturated
           let call_captured = ccCallCaptured cc
           indirect_call (map VarV call_captured)
         EQ -> do               -- Saturated
           genDirectCall cc args
         GT -> do               -- Oversaturated
           -- Generate a direct call with the correct number of arguments.
           -- Then, call the return value with remaining arguments.
           let (direct_args, indir_args) = splitAt (arity cc) args
           app <- emitAtom1 (PrimType OwnedType) =<<
                  genDirectCall cc direct_args

           genIndirectCall return_types app indir_args

    indirect_call call_captured =
      genIndirectCall return_types (VarV fun) (call_captured ++ args)
    
    prim_call entry_point cc
      | length args /= (arity cc) =
          -- Error to call with the wrong number of arguments
          internalError "genClosureCall: Procedure call has wrong number of arguments"
      | otherwise =
        let call_captured = map VarV (ccCallCaptured cc)
        in return $ primCallA (VarV entry_point) (call_captured ++ args)

-- | Generate a call to a procedure.  Since procedures aren't closure-converted,
--   the only change is to add call-captured variables.
genPrimCall :: Var               -- ^ Function that is called
            -> [Val]             -- ^ Arguments
            -> GenM Atom
genPrimCall fun args = do
  info <- lift $ lookupCCInfo fun
  case info of
    -- If function is unknown, it doesn't capture variables
    Nothing -> make_call []

    -- If it's a prim-call function, generate a primitive call 
    Just cc@(GlobalPrim {}) -> make_call $ ccCallCaptured cc
    Just cc@(LocalPrim {})  -> make_call $ ccCallCaptured cc

    -- Closure-call functions cannot be called with this calling convention
    Just _ -> internalError "genPrimCall"
  where
    make_call extra_args =
      return $ primCallA (VarV fun) (map VarV extra_args ++ args)

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
  -- Get the function info table and captured variables
  inf_ptr <- loadField (objectHeaderRecord !!: 0) op

  -- Can make an exact call if the callee is a function and
  -- the number of arguments matches the function's arity
  inf_tag <- loadField (infoTableHeaderRecord !!: 0) inf_ptr
  inf_tag_test <- primCmpZ (PrimType (IntType Unsigned S8)) CmpEQ inf_tag $
                  uint8V $ fromEnum FunTag

  -- Branch to the code for an exact or an inexact call
  ret_vars <- lift $ mapM newAnonymousVar return_value_types
  getContinuation True ret_vars $ \cont -> do
    inexact_target <- define_inexact_call ret_vars cont
    
    genIf inf_tag_test
      -- True: Callee is a function
      (do
          -- Check whether function arity matches the number of given arguments
          arity <- loadField (funInfoHeaderRecord0 !!: 1) inf_ptr
          arity_eq <- primCmpZ (PrimType (IntType Unsigned S16)) CmpEQ arity $
                      uint16V $ length args
          genIf arity_eq
            -- True: Callee is fully applied
            (do exact_call ret_vars inf_ptr
                return cont)
            -- False: Callee is under- or over-saturated
            (return $ ReturnE $ primCallA inexact_target []))
      -- False: Callee is not a function
      (return $ ReturnE $ primCallA inexact_target [])
  return $ ValA (map VarV ret_vars)
  where
    return_value_types = map PrimType return_types
    
    -- Create a local function that performs an inexact call
    define_inexact_call ret_vars cont = do
      inexact_target <- lift $ newAnonymousVar (PrimType PointerType)
      inexact_fun_body <- lift $ execBuild return_value_types $ do
        inexact_call ret_vars
        return cont
      let inexact_fun = primFun [] return_value_types inexact_fun_body
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
      fn <- loadField (funInfoHeaderRecord0 !!: 2) inf_ptr

      -- Get the function's captured variables, then call the function
      bindAtom ret_vars $ primCallA fn (op : args)

-- | Create a dynamic function application
genApply :: Val -> [Val] -> Val -> GenM ()
genApply _ [] _ = internalError "genApply: No arguments"
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
