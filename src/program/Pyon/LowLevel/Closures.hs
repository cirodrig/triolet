{-| Closure conversion.

This pass converts all functions into primitive (non-closure-based)
functions.  Lambda values and letrec expressions are eliminated.

Data structures should be flattened before running closure conversion.
'RecV' values are not allowed.  'PackA' and 'UnpackA' atoms are not allowed.
-}

{-# LANGUAGE FlexibleInstances #-}
module Pyon.LowLevel.Closures(closureConvert)
where

import Control.Monad
import Control.Monad.Trans
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import Data.List
import qualified Data.Set as Set
import Debug.Trace

import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.Label
import Gluon.Common.MonadLogic
import Gluon.Common.Supply
import Pyon.SystemF.Builtins
import Pyon.LowLevel.Syntax
import Pyon.LowLevel.Types
import Pyon.LowLevel.Record
import Pyon.LowLevel.Build
import Pyon.Globals

type BuildBlock a = Gen CC a

-- | During closure conversion, keep track of the set of free variables
type FreeVars = Set.Set Var

deleteList :: [Var] -> FreeVars -> FreeVars
deleteList xs s = foldr Set.delete s xs

-------------------------------------------------------------------------------

type Defs = [([FunDef], [DataDef])]

mkDefs :: [FunDef] -> [DataDef] -> Defs
mkDefs f d = [(f, d)]

noDefs :: Defs
noDefs = []

concatDefs :: Defs -> Defs -> Defs
concatDefs = (++)

-- | The monad used by closure conversion.
--
-- Closure conversion keeps track of the free variables in a scanned statement
-- and the global defintions that were created from it.
newtype CC a = CC (CCEnv -> IO (a, FreeVars, Defs))

data CCEnv =
  CCEnv
  { envVarIDSupply :: {-# UNPACK #-}!(IdentSupply Var)
  , envEntryPoints :: !(IntMap.IntMap EntryPoints)
  }

emptyCCEnv var_ids = CCEnv var_ids IntMap.empty

runCC :: IdentSupply Var -> CC () -> IO ([FunDef], [DataDef])
runCC var_ids (CC f) = do
  ((), _, defs) <- f $ emptyCCEnv var_ids
  return $ accumulate id id defs
  where
    accumulate funs datas ((funs', datas'):defs) =
      accumulate (funs . (funs' ++)) (datas . (datas' ++)) defs
    accumulate funs datas [] = (funs [], datas [])

returnCC :: a -> IO (a, FreeVars, Defs)
returnCC x = return (x, Set.empty, noDefs)

instance Monad CC where
  return x = CC $ \_ -> returnCC x
  CC f >>= k = CC $ \env -> do
    (x, fv1, defs1) <- f env
    case k x of
      CC g -> do
        (y, fv2, defs2) <- g env
        return (y, Set.union fv1 fv2, concatDefs defs1 defs2)

instance Supplies CC (Ident Var) where
  fresh = CC $ \env -> returnCC =<< supplyValue (envVarIDSupply env)

-- | Add a function's entry points to the environment
withEntryPoints :: Var -> EntryPoints -> CC a -> CC a
withEntryPoints fname entry_points (CC m) = CC $ m . insert_entry
  where
    insert_entry env =
      let key = fromIdent $ varID fname
      in env { envEntryPoints = IntMap.insert key entry_points $
               envEntryPoints env}

lookupEntryPoints :: Var -> CC (Maybe EntryPoints)
lookupEntryPoints v = CC $ \env ->
  returnCC $ IntMap.lookup (fromIdent $ varID v) $ envEntryPoints env

lookupEntryPoints' :: Var -> CC EntryPoints
lookupEntryPoints' v = lookupEntryPoints v >>= check
  where
    check (Just x) = return x
    check Nothing  =
      internalError "lookupEntryPoints': No information for variable"

-- | Scan some code over which a variable is locally bound.  The variable
-- will be removed from the free variable set.
withParameter :: ParamVar -> CC a -> CC a
withParameter v (CC m) = CC $ fmap remove_var . m
  where
    remove_var (x, vars, defs) =
      (x, Set.delete v vars, defs)

-- | Scan some code over which some variables are locally bound.  The variables
-- will be removed from the free variable set.
withParameters :: [ParamVar] -> CC a -> CC a
withParameters vs (CC m) = CC $ fmap remove_var . m
  where
    remove_var (x, vars, defs) = (x, deleteList vs vars, defs)

-- | Scan some code over which some functions are defined.  New variables will 
-- be created for the functions' entry points and info tables.  This function 
-- does not create definitions of these variables.
withFunctions :: [FunDef] -> CC a -> CC a
withFunctions defs m = foldr with_function m defs
  where
    with_function (FunDef v fun) m = do
      entry_points <- mkEntryPoints (funType fun) (varName v)
      insert_entry_points (fromIdent $ varID v) entry_points m

    insert_entry_points key entry_points (CC f) = CC $ \env ->
      f $ env { envEntryPoints = IntMap.insert key entry_points $
                                 envEntryPoints env}

-- | Write some global object definitions
writeDefs :: [FunDef] -> [DataDef] -> CC ()
writeDefs fun_defs data_defs = CC $ \_ ->
  return ((), Set.empty, mkDefs fun_defs data_defs) 

-- | Record that a variable has been used
mention :: Var -> CC ()
mention v = CC $ \_ ->
  return ((), Set.singleton v, noDefs)

-- | Record that some variables have been used
mentions :: [Var] -> CC ()
mentions vs = CC $ \_ ->
  return ((), Set.fromList vs, noDefs)

listenFreeVars :: CC a -> CC (a, FreeVars)
listenFreeVars (CC m) = CC $ \env -> do
  (x, free_vars, defs) <- m env
  return ((x, free_vars), free_vars, defs)

-- | Look up a variable used as the operator of a function call.
-- If the variable is a known function and its arity matches the given arity,
-- return a 'Right' value with the direct entry point.  Otherwise, return a
-- 'Left' value with the variable.
lookupCallVar :: Var -> Int -> CC (Either Var Var)
lookupCallVar v arity = lookupEntryPoints v >>= select
  where
    select Nothing = return $ Left v -- Unknown function
    
    select (Just ep)
      | arity == functionArity ep =
          -- Right number of arguments: return the direct call
          return $ Right $ directEntry ep
      | otherwise =
          -- Wrong number of arguments
          return $ Left v

-------------------------------------------------------------------------------

scanBlock :: Block -> [PrimType] -> CC Block
scanBlock (Block stms atom) returns = withMany scanStm stms $ \stms' -> do
  atom' <- scanAtom atom returns
  execBuild $ sequence stms' >> atom'

scanStm :: Stm -> (BuildBlock () -> CC a) -> CC a
scanStm statement k =
  case statement
  of LetE vs atom -> do
       atom' <- scanAtom atom (map varPrimType vs)
       withParameters vs $ k $ bindAtom vs =<< atom'
     LetrecE defs -> 
       withDefGroup defs k

scanAtom :: Atom -> [PrimType] -> CC (BuildBlock Atom)
scanAtom atom returns =
  case atom
  of ValA vs -> do
       vs' <- mapM scanValue vs
       return $ ValA `liftM` sequence vs'

     -- Generate a direct call if possible
     CallA (VarV v) vs -> do
       call_var <- lookupCallVar v (length vs)
       vs' <- mapM scanValue vs
       case call_var of
         Right v' ->
           -- Found direct call entry point
           return $ PrimCallA (VarV v') `liftM` sequence vs'
         Left v' ->
           -- Generate indirect call
           genIndirectCall returns (return $ VarV v') vs'

     -- General case, indirect call
     CallA v vs -> do
       v' <- scanValue v
       vs' <- mapM scanValue vs
       genIndirectCall returns v' vs'
     PrimCallA v vs -> do
       v' <- scanValue v
       vs' <- mapM scanValue vs
       return $ PrimCallA `liftM` v' `ap` sequence vs'
     PrimA prim vs -> do
       vs' <- mapM scanValue vs
       return $ PrimA prim `liftM` sequence vs'
     SwitchA scr alts -> do
       scr' <- scanValue scr
       alts' <- mapM scan_alt alts
       return $ SwitchA `liftM` scr' `ap` return alts'
     PackA {} -> internalError "scanAtom: unexpected 'pack'"
     UnpackA {} -> internalError "scanAtom: unexpected 'unpack'"
  where
    scan_alt (lit, block) = do
      block' <- scanBlock block returns
      return (lit, block')

-- | Perform closure conversion on a value.
-- 
scanValue :: Val -> CC (BuildBlock Val)
scanValue value =
  case value
  of LamV f  -> constructLambdaFunction f
     RecV {} -> internalError "scanValue"
     _       -> return (return value)
  
-- | Get the type of a variable; it must be a primitive type.
varPrimType :: Var -> PrimType
varPrimType v = case varType v
                of PrimType t -> t
                   _ -> internalError "varPrimType"
                     
-- | Get the type of a value.  Since record flattening has been performed, 
-- the type must be a primitive type.
valType :: Val -> PrimType
valType (VarV v) = varPrimType v
valType (RecV {}) = internalError "valType"
valType (ConV c) = trace "valType: Assuming constructor is a function" $ OwnedType
valType (LitV l) = litType l
valType (LamV f) = OwnedType

-- | Perform closure conversion on a data value.
scanDataValue :: Val -> CC Val
scanDataValue value = 
  case value
  of LamV {} -> internalError "scanDataValue"
     RecV {} -> internalError "scanDataValue"
     _       -> return value

withDefGroup :: [FunDef] -> (BuildBlock () -> CC a) -> CC a
withDefGroup defs k =
  -- Add functions to environment
  withFunctions defs $ do
    -- Closure-convert all function bodies
    (funs, captured_vars) <- mapAndUnzipM scanFun [f | FunDef _ f <- defs]
    
    -- Merge captured variables into one set.
    -- Remove the functions from the set.
    let captured_set = deleteList fun_variables $
                       Set.unions $ map Set.fromList captured_vars
        all_captured_vars = Set.toList captured_set
        
    -- Create the captured variables record
    let capvars = capturedVarsRecord all_captured_vars fun_variables
        
    -- Generate global data
    mapM_ (construct_entry_point capvars) $
      zip3 fun_variables captured_vars funs

    capvars_free_fun <- capturedVarsFreeFunction capvars
    capvars_free_fun_var <- hoistFun Nothing capvars_free_fun

    -- Get the info tables of the functions
    info_tables <- forM fun_variables $ \v -> do
      entry_points <- lookupEntryPoints' v
      return $ infoTableEntry entry_points

    -- Generate code to construct closures
    let generate_closures = do
          -- Create captured variables
          capvars_ptr <-
            initializeCapturedVars capvars (VarV capvars_free_fun_var)

          -- Create closures
          closure_ptrs <-
            forM info_tables $ \v -> constructClosure (VarV v) capvars_ptr

          -- Finish initializing captured variables
          finishCapturedVars capvars capvars_ptr closure_ptrs
          
          -- Write closures to their actual variables
          zipWithM_ write_closure_var fun_variables closure_ptrs
          where
            -- Move value from src to dst
            write_closure_var dst src = bindAtom1 dst $ ValA [src]
            
    -- Pass this code to the continuation
    k generate_closures
  where
    fun_variables = [v | FunDef v _ <- defs]
    
    construct_entry_point capvars (v, captured_vars, direct_fun) = do
      entry_points <- lookupEntryPoints' v
      constructEntryPoints capvars captured_vars entry_points direct_fun

-- | Perform closure conversion on a function.  The closure-converted
-- function is returned, along with a list of the captured variables.
--
-- First, closure conversion is performed on the function body.
-- Then the function is converted to one with no free variables that takes
-- an extra argument for each free variable in the original function.
scanFun :: Fun -> CC (Fun, [Var])
scanFun fun = do
  unless (isClosureFun fun) $
    internalError "scanFun: Given function has wrong calling convention"

  -- Do closure conversion in the function body, and get the set of variables
  -- mentioned in the function body
  let return_prim_types = map valueToPrimType $ funReturnTypes fun
        
  (body', free_vars) <-
    listenFreeVars $
    withParameters (funParams fun) $
    scanBlock (funBody fun) return_prim_types

  -- Add the free variables as extra parameters
  let free_var_list = Set.toList free_vars
      new_params = free_var_list ++ funParams fun
      new_fun = primFun new_params (funReturnTypes fun) body'
  return (new_fun, free_var_list)

-- | Perform closure conversion on a data definition.
--
-- Currently we don't allow lambda functions inside static data structures,
-- so this is just a validity check.
scanDataDef :: DataDef -> CC DataDef 
scanDataDef (DataDef v record vals) = do 
  vals' <- mapM scanDataValue vals
  return $ DataDef v record vals'


-- | Perform closure conversion on the set of global functions.  Unlike
-- local functions, closures are not needed because it's only possible to 
-- reference global functions.  A dummy closure object is created for
-- compatibility with the way functions are called.
--
-- Global data definitions aren't allowed to contain lambda functions, so we
-- can ignore them.
scanTopLevel :: [FunDef] -> [DataDef] -> CC ()
scanTopLevel fun_defs data_defs =
  withFunctions fun_defs $
  withParameters data_variables $ do
    -- Closure-convert all function bodies.  Only top-level functions should 
    -- appear as free variables.
    (funs, captured_vars) <- mapAndUnzipM scanFun [f | FunDef _ f <- fun_defs]
    check_captured_vars captured_vars
    
    -- Create a global object to fill the place of the captured variables
    global_capture_var <- newAnonymousVar (PrimType OwnedType)
    let global_capture = [nativeWordV 1, LitV NullL]
        global_capture_def =
          DataDef global_capture_var (staticRecord objectHeader) global_capture
    
    -- Emit all top-level functions
    zipWithM_ (constructGlobalFunction global_capture_var) fun_variables funs

    -- Convert function references appearing in data definitions
    data_defs' <- mapM scanDataDef data_defs
    writeDefs [] (global_capture_def : data_defs)
  where
    fun_variables = [v | FunDef v _ <- fun_defs]
    data_variables = [v | DataDef v _ _ <- data_defs]

    -- If something other than a top-level variable is captured, it means
    -- there's a compiler bug
    check_captured_vars captured_vars =
      let valid_vars = Set.fromList $ fun_variables ++ data_variables
      in if all (`Set.member` valid_vars) $ concat captured_vars
         then return ()
         else internalError "scanTopLevel: Impossible variable capture"

closureConvert :: Module -> IO Module
closureConvert (Module fun_defs data_defs) =
  withTheLLVarIdentSupply $ \var_ids -> do
    (fun_defs', data_defs') <- runCC var_ids $ scanTopLevel fun_defs data_defs
    return $ Module fun_defs' data_defs'

-------------------------------------------------------------------------------

-- | Hoist a function to a top-level
--   definition.  The function variable is returned.
hoistFun :: Maybe Label -> Fun -> CC Var
hoistFun fun_name fun = do
  
  -- Create a new function variabl
  fvar <- newVar fun_name (PrimType PointerType)
  writeDefs [FunDef fvar fun] []
  return fvar

-- | Perform closure conversion on a lambda function; generate entry 
--   points and data structures for it.  As a side effect, global objects
--   are created and statements are emitted in the current block.
constructLambdaFunction :: Fun -> CC (BuildBlock Val)
constructLambdaFunction lambda_fun = do
  -- Closure-convert the function
  (direct_fun, captured_vars) <- scanFun lambda_fun
  
  -- Generate other global data
  let capvars = capturedVarsRecord captured_vars []
      arity = length $ funParams direct_fun
  entry_points <- mkEntryPoints (funType lambda_fun) Nothing
  constructEntryPoints capvars captured_vars entry_points direct_fun
  
  capvars_free_fun <- capturedVarsFreeFunction capvars
  capvars_free_fun_var <- hoistFun Nothing capvars_free_fun
  
  info_table_var <- return $! infoTableEntry entry_points
  
  -- Generate code to construct a closure
  let generate_closure = do
        capvars_ptr <-
          initializeCapturedVars capvars (VarV capvars_free_fun_var)
        closure_ptr <-
          constructClosure (VarV info_table_var) capvars_ptr
        finishCapturedVars capvars capvars_ptr []
        return closure_ptr
  
  return generate_closure

constructInfoTable :: EntryPoints -> DataDef
constructInfoTable entry_points =
  DataDef (infoTableEntry entry_points) infoTableRecord
  [ nativeWordV (functionArity entry_points)
  , VarV (exactEntry entry_points)
  , VarV (inexactEntry entry_points)
  ]

constructEntryPoints capvars captured_vars entry_points direct_fun = do
  let direct_params = funParams direct_fun 
      direct_returns = funReturnTypes direct_fun

  ex_fun <- exactEntryFunction capvars captured_vars direct_params
            direct_returns (directEntry entry_points)
  in_fun <- inexactEntryFunction capvars direct_params direct_returns
            (exactEntry entry_points)
  writeDefs
    [ FunDef (directEntry entry_points) direct_fun
    , FunDef (exactEntry entry_points) ex_fun
    , FunDef (inexactEntry entry_points) in_fun]
    [constructInfoTable entry_points]

-- | Create a global function defintion.
constructGlobalFunction global_capture_var v f = do
  -- Create function entry points
  entry_points <- lookupEntryPoints' v
  constructEntryPoints capvars [] entry_points f
  
  -- Create a static object for the variable closure
  let closure_def =
        DataDef v closureRecord [ nativeWordV 1
                                , LitV NullL
                                , VarV global_capture_var
                                , VarV $ infoTableEntry entry_points
                                ]
  writeDefs [] [closure_def]
  where
    capvars = capturedVarsRecord [] []

-------------------------------------------------------------------------------
-- Data structures and code generation

objectHeaderLength = length objectHeader

-- | A function closure consists of a pointer to the function's info table and
-- an owned reference to the captured variables
closureRecord :: StaticRecord
closureRecord =
  staticRecord (objectHeader ++
                [ PrimField PointerType
                , PrimField OwnedType
                ])

loadClosureCapturedVars, loadClosureInfoTable :: Val -> BuildBlock Val

loadClosureCapturedVars = loadField (toDynamicField $ closureRecord !!: 3)
loadClosureInfoTable = loadField (toDynamicField $ closureRecord !!: 2)

-- | Allocate and initialize a closure with the given info pointer and
-- captured variables pointer
constructClosure :: Val -> Val -> BuildBlock Val
constructClosure info_ptr capt_ptr = do
  -- Adjust the captured variables reference count
  increfHeader capt_ptr

  -- Allocate
  closure_ptr <- allocateHeapObject $ nativeWordV $ recordSize closureRecord
    
  -- Initialize fields
  initializeHeader (ConV $ pyonBuiltin the_prim_free_lambda_closure)
    closure_ptr
  storeField (toDynamicField $ closureRecord !!: 2) closure_ptr info_ptr
  storeField (toDynamicField $ closureRecord !!: 3) closure_ptr capt_ptr
    
  return closure_ptr

-- | A function info table holds the function's arity, its exact entry point, 
-- and its inexact entry point
infoTableRecord :: StaticRecord
infoTableRecord =
  staticRecord [ PrimField nativeWordType
               , PrimField PointerType
               , PrimField PointerType
               ]

loadInfoTableArity, loadInfoTableExactEntry, loadInfoTableInexactEntry ::
  Val -> BuildBlock Val

loadInfoTableArity = loadField (toDynamicField $ infoTableRecord !!: 0)
loadInfoTableExactEntry = loadField (toDynamicField $ infoTableRecord !!: 1)
loadInfoTableInexactEntry = loadField (toDynamicField $ infoTableRecord !!: 2)

data CapturedVars =
  CapturedVars 
  { capturedVars     :: ![Var] 
  , capturedClosures :: ![Var]
  , capturedRecord   :: !StaticRecord
  }

capturedVariableFields :: CapturedVars -> [StaticField]
capturedVariableFields cvars =
  take (length $ capturedVars cvars) $
  drop objectHeaderLength $
  recordFields $ capturedRecord cvars

capturedClosureFields :: CapturedVars -> [StaticField]
capturedClosureFields cvars =
  take (length $ capturedClosures cvars) $
  drop (objectHeaderLength + length (capturedVars cvars)) $
  recordFields $ capturedRecord cvars

-- | Find the record field corresponding to this captured variable
findCapturedField :: Var -> CapturedVars -> Maybe StaticField
findCapturedField v cvars =
  msum
  [ fmap (getField . (objectHeaderLength +)) $
    findIndex (v ==) $ capturedVars cvars
  , fmap (getField . (objectHeaderLength + length (capturedVars cvars) +)) $
    findIndex (v ==) $ capturedClosures cvars
  ]
  where
    getField ix = recordFields (capturedRecord cvars) !! ix

-- | Construct a record type from a list of captured variables and a list of
--   pointers to function closures.
--
-- The record includes non-owned references to the function closures that
-- reference this recore.  These references must be non-owned to avoid
-- reference cycles.
capturedVarsRecord :: [Var] -> [Var] -> CapturedVars
capturedVarsRecord vars fn_closures =
  let field_types = objectHeader ++
                    map (fromPrimType . varType) vars ++
                    replicate (length fn_closures) (PrimField PointerType)
      record = staticRecord field_types
  in CapturedVars vars fn_closures record
  where
    fromPrimType (PrimType t) = PrimField t
    fromPrimType (RecordType _) =
      internalError "referenceCountedClosureRecord: Unexpected record type"
      
-- | Construct a function to free a collection of captured variables
capturedVarsFreeFunction :: CapturedVars -> CC Fun
capturedVarsFreeFunction capvars = do
  object_ptr <- newAnonymousVar (PrimType OwnedType)

  fun_body <- execBuild $ do
    let object = VarV object_ptr

    -- Decref each captured variable that is owned
    mapM_ (decref_field object) $ map toDynamicField $
      capturedVariableFields capvars
  
    -- Deallocate each closure
    mapM_ (dealloc_field object) $ map toDynamicField $
      capturedClosureFields capvars
    return $ ValA []
    
  return $ primFun [object_ptr] [] fun_body
  where
    decref_field object_ptr fld =
      case fieldType fld
      of PrimField OwnedType -> do
           -- Decrement this field's reference count
           decrefHeader =<< loadField fld object_ptr
         PrimField _ -> do
           -- Nothing to do for other fields
           return ()
         _ -> internalError "capturedVarsFreeFunction: Unexpected field type" 

    dealloc_field object_ptr fld = do
      -- Deallocate the object this field points to
      deallocateHeapObject =<< loadField fld object_ptr

-- | Construct and initialize a data structure to hold captured variables. 
-- The data structure is not initialized completely: pointers to captured 
-- closures are left uninitialized, and must be set by 'finishCapturedVars'.
initializeCapturedVars :: CapturedVars -> Val -> BuildBlock Val
initializeCapturedVars capvars free_function = do
  -- Allocate
  cap_ptr <- allocateHeapObject $ nativeWordV $ recordSize $
             capturedRecord capvars
  
  -- Initialize fields
  initializeHeader free_function cap_ptr
  zipWithM_ (initialize_var cap_ptr) (capturedVars capvars)
    (capturedVariableFields capvars)
    
  -- Convert to an owned pointer
  emitAtom1 (PrimType OwnedType) $ PrimA PrimCastToOwned [cap_ptr]
  where
    initialize_var ptr v fld =
      storeField (toDynamicField fld) ptr (VarV v)

finishCapturedVars :: CapturedVars -> Val -> [Val] -> BuildBlock ()
finishCapturedVars capvars cap_ptr closures = do
  -- Initialize remaining fields
  zipWithM_ initialize_fld closures (capturedClosureFields capvars)

  -- Decrement reference count
  decrefHeader cap_ptr
  where
    initialize_fld closure fld = do
      -- Store a non-owned pointer
      closure' <- emitAtom1 (PrimType PointerType) $
                  PrimA PrimCastFromOwned [closure]
      storeField (toDynamicField fld) cap_ptr closure'

-- | Generate the entry point for an exact call.  The entry point takes 
-- a captured variable record along with other arguments, unpacks the
-- captured variables, and passes them to the direct call.
exactEntryFunction :: CapturedVars
                   -> [Var]       -- ^ Captured variables to load 
                   -> [Var]       -- ^ Parameter variables
                   -> [ValueType] -- ^ Return types
                   -> Var         -- ^ Direct entry point
                   -> CC Fun
exactEntryFunction capvars need_vs param_vs return_types direct_entry = do
  closure_ptr <- newAnonymousVar (PrimType OwnedType)
  fun_body <- execBuild $ do
    -- Load each variable needed by the function
    mapM_ (load_var (VarV closure_ptr)) need_vs
    return $ PrimCallA (VarV direct_entry) (map VarV $ need_vs ++ param_vs)
  return $ primFun (closure_ptr : param_vs) return_types fun_body
  where
    load_var closure_ptr v =
      case findCapturedField v capvars
      of Just fld -> loadFieldAs (toDynamicField fld) closure_ptr v
         Nothing -> internalError "exactEntryFunction"

inexactEntryFunction :: CapturedVars
                     -> [Var]       -- ^ Parameter variables
                     -> [ValueType] -- ^ Return types
                     -> Var         -- ^ Exact entry point
                     -> CC Fun
inexactEntryFunction capvars param_vs return_types exact_entry = do
  closure_var <- newAnonymousVar (PrimType OwnedType)
  args_var <- newAnonymousVar (PrimType PointerType)
  return_var <- newAnonymousVar (PrimType PointerType)
  fun_body <- execBuild $ do
    -- Load each argument
    let arg_record = staticRecord $ map type_field $ map varType param_vs
        ret_record = staticRecord $ map type_field return_types
        closure_ptr = VarV closure_var
        args_ptr = VarV args_var
        return_ptr = VarV return_var
    zipWithM_ (load_field args_ptr) param_vs $ recordFields arg_record
    
    -- Call the direct entry point
    return_vs <- emitAtom return_types $
      PrimCallA (VarV exact_entry) (closure_ptr : map VarV param_vs)
      
    -- Store each return value
    zipWithM_ (store_field return_ptr) return_vs $ recordFields ret_record
    return $ ValA []
  return $ primFun [closure_var, args_var, return_var] [] fun_body
  where
    type_field (PrimType pt) = PrimField pt
    type_field _ = internalError "inexactEntryFunction"

    store_field return_ptr v fld =
      storeField (toDynamicField fld) return_ptr v

    load_field args_ptr v fld =
      loadFieldAs (toDynamicField fld) args_ptr v

-- | Produce an indirect call of the given operator
genIndirectCall :: [PrimType]
                -> BuildBlock Val
                -> [BuildBlock Val]
                -> CC (BuildBlock Atom)
genIndirectCall return_types mk_op mk_args = return $ do
  op <- mk_op
  args <- sequence mk_args

  -- Get the function closure and info table 
  inf_ptr <- loadClosureInfoTable op
  clo_ptr <- loadClosureCapturedVars op
  
  -- Check if the number of arguments matches the function's arity
  arity <- loadInfoTableArity inf_ptr
  arity_test <- primCmpZ (PrimType nativeWordType) CmpEQ arity $ nativeWordV $ length args
  
  -- If the arity matches, then perform an exact call.  Otherwise,
  -- perform an inexact call.
  genIf arity_test 
    (exact_call clo_ptr args =<< loadInfoTableExactEntry inf_ptr)
    (inexact_call clo_ptr args =<< loadInfoTableInexactEntry inf_ptr)
  where
    exact_call clo_ptr args fn = return $ PrimCallA fn (clo_ptr : args)

    inexact_call clo_ptr args fn = do
      -- Create temporary storage for return values
      let ret_record = staticRecord $ map PrimField return_types
      ret_ptr <- allocateHeapObject $ nativeWordV $ recordSize ret_record
      
      -- Create a partial application
      pap_ptr <- createPAP fn args
      
      -- Apply
      bindAtom0 $ PrimCallA (ConV $ pyonBuiltin the_prim_apply_pap)
        [pap_ptr, ret_ptr]
        
      -- Extract return values
      ret_vals <- load_ret_values ret_ptr ret_record
      
      -- Free temporary storage
      -- FIXME: reference counts
      deallocateHeapObject ret_ptr
      return $ ValA ret_vals
    
    -- Load each return value out of the heap record
    load_ret_values ret_ptr record = forM (recordFields record) $ \fld ->
      loadField (toDynamicField fld) ret_ptr

-- | Create a PAP record type based on the given argument types.
--
-- Layout of a PAP record:
-- * Object refcount and free function
-- * Indirect entry point (function pointer)
-- * Number of fields (native word)
-- * Field types (one byte per field)
-- * Fields
papRecord :: [PrimType] -> StaticRecord
papRecord types = staticRecord fields
  where
    layout_fields = PrimField nativeWordType :
                    replicate (length types) (PrimField $ IntType Unsigned S8)
    fields = objectHeader ++ [PrimField PointerType] ++
             layout_fields ++ map PrimField types

-- | Create a partial application object containing the given function and
-- argument values
createPAP :: Val -> [Val] -> BuildBlock Val
createPAP fun vals = do
  -- Allocate record
  rec_ptr <- allocateHeapObject $ nativeWordV $ recordSize record
  
  -- Initialize fields
  initializeHeader (ConV $ pyonBuiltin the_prim_free_pap) rec_ptr
  storeField (record' !!: 2) rec_ptr fun
  storeField (record' !!: 3) rec_ptr $ nativeWordV num_args
  store_field_types rec_ptr
  store_fields rec_ptr
  
  -- Convert to an owned pointer
  emitAtom1 (PrimType OwnedType) $ PrimA PrimCastToOwned [rec_ptr]
  where
    num_args = length vals
    types = map valType vals
    record = papRecord types
    record' = toDynamicRecord record
  
    -- Index of first field holding type information
    field_types_index = 4
    
    -- Index of first field holding argument values
    field_vals_index = field_types_index + num_args
    
    -- Store all field types
    store_field_types rec_ptr =
      zipWithM_ store_field_type types [field_types_index ..]
      where
        store_field_type ty ix =
          let flag = LitV $ IntL Unsigned S8 $ fromIntegral $ fieldTypeFlag ty
          in storeField (record' !!: ix) rec_ptr flag
    
    store_fields rec_ptr =
      zipWithM_ store_field vals [field_vals_index ..] 
      where
        store_field val ix =
          storeField (record' !!: ix) rec_ptr val
    
-- | Get the run-time flag used to indicate a primitive type.
--
-- * 1   -- Bool
-- * 2-5 -- Unsigned int
-- * 6-9 -- Signed int
-- * 10  -- Float
-- * 11  -- Double
-- * 12  -- Pointer
-- * 13  -- Owned Pointer
fieldTypeFlag :: PrimType -> Int
fieldTypeFlag BoolType              = 1 
fieldTypeFlag (IntType Unsigned sz) = 2 + fromEnum sz
fieldTypeFlag (IntType Signed sz)   = 6 + fromEnum sz
fieldTypeFlag (FloatType S32)       = 10
fieldTypeFlag (FloatType S64)       = 11
fieldTypeFlag PointerType           = 12
fieldTypeFlag OwnedType             = 13
fieldTypeFlag _                     = internalError "fieldTypeFlag"
               
