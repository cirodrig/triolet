{-| Generation of code and data structures for closure conversion.

* Function closures

A function /closure/ is an object containing a function and its captured
variables.  Closures are implemented one of three different ways:

 * A top-level function closure is implemented as a global, statically
   allocated object.  Top-level functions never capture variables.

 * A nonrecursive function closure is a dynamically allocated object
   containing a reference to the function info table and the captured
   variables.

 * A recursive function closure is a dynamically allocated object containing  
   a reference to the function info table and a group closure.  The group
   closure is a shared record holding all captured variables and referencing
   all functions in the group.

** Memory management

Closures are reference-counted objects.  Global closures have their reference
count initialized to 1 so that they are never deallocated.  Recursive closures
are handled specially because they have cyclic references.

When a recursive closure's reference count falls to zero, the other functions
in the group are inspected.  If all reference counts are zero, then all
members of the group are deallocated along with the shared record.  Otherwise,
the closure is still live and is not finalized or deallocated.

* Partial applications

A /partial application/ structure is a record consisting of a function and
some function arguments.  The number of arguments is stored as a field of 
the PAP.  The arguments stored in a PAP are /promoted/ up to native
register sizes; so, for example, a bool is stored as a native integer.

-}

{-# LANGUAGE FlexibleContexts, FlexibleInstances, RecursiveDo, ViewPatterns #-}
module LowLevel.ClosureCode
       (varPrimType,
        GenM, CC,
        runCC,
        withHoistedVariables,
        withUnhoistedVariables,
        isHoisted,
        withParameter, withParameters,
        withLocalFunctions,
        withGlobalFunctions,
        writeFun, writeData,
        mention, mentions,
        listenFreeVars,
        
        -- * Code generation
        genVarCall,
        genIndirectCall,
        emitLambdaClosure
       )
where

import Control.Monad
import Control.Monad.Fix
import Control.Monad.Trans
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import Data.List
import Data.Maybe
import qualified Data.Set as Set
import Debug.Trace

import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.Supply
import LowLevel.Builtins
import LowLevel.FreshVar
import LowLevel.Print
import LowLevel.Syntax
import LowLevel.Types
import LowLevel.Record
import LowLevel.Records
import LowLevel.RecordFlattening
import LowLevel.Build
import Globals

type GenM a = Gen CC a

-- | During closure conversion, keep track of the set of free variables
type FreeVars = Set.Set Var

-- | Get the type of a variable; it must be a primitive type.
varPrimType :: Var -> PrimType
varPrimType v = case varType v
                of PrimType t -> t
                   _ -> internalError "varPrimType"
                     
-- | Get the type of a value.  Since record flattening has been performed, 
-- the type must be a primitive type.
valPrimType :: Val -> PrimType
valPrimType val =
  case valType val 
  of PrimType pt -> pt
     RecordType _ -> internalError "valPrimType"

-- | Is this the default closure deallocator function?
isDefaultDeallocator v = v == llBuiltin the_prim_pyon_dealloc

-------------------------------------------------------------------------------

type Defs = [([FunDef], [DataDef])]

mkDefs :: [FunDef] -> [DataDef] -> Defs
mkDefs f d = [(f, d)]

noDefs :: Defs
noDefs = []

concatDefs :: Defs -> Defs -> Defs
concatDefs = (++)

-- | The monad used by closure conversion while scanning a program.
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
newtype CC a = CC (CCEnv -> IO (a, FreeVars, Defs))

data CCEnv =
  CCEnv
  { envVarIDSupply :: {-# UNPACK #-}!(IdentSupply Var)
    -- | IDs of letrec-bound functions that should be hoisted to global scope.
  , envHoist :: !IntSet.IntSet
    -- | IDs of global variables.  Global variables are never captured.
  , envGlobals :: !IntSet.IntSet
    -- | Information about how to call functions that are in scope.  If a
    --   function is being transformed into a procedure, then only the direct 
    --   entry is provided.  Otherwise all the closure information is provided.
  , envEntryPoints :: !(IntMap.IntMap (Either Var Closure))
  }

emptyCCEnv var_ids globals =
  let globals_set = IntSet.fromList $ map (fromIdent . varID) globals
      hoisted_set = IntSet.empty
  in CCEnv var_ids hoisted_set globals_set IntMap.empty

-- | Run some closure-conversion code.  All variables are treated as
--   un-hoisted until the hoisted variables are set.
runCC :: IdentSupply Var        -- ^ Variable ID supply
      -> [Var]                  -- ^ Global variables
      -> CC ()                  -- ^ Computation to run
      -> IO ([FunDef], [DataDef]) -- ^ Compute new global definitions 
runCC var_ids globals (CC f) = do
  let env = emptyCCEnv var_ids globals
  ((), _, defs) <- f env
  return $ accumulate id id defs
  where
    accumulate funs datas ((funs', datas'):defs) =
      accumulate (funs . (funs' ++)) (datas . (datas' ++)) defs
    accumulate funs datas [] = (funs [], datas [])

returnCC :: a -> IO (a, FreeVars, Defs)
returnCC x = return (x, Set.empty, noDefs)

instance Functor CC where
  fmap f (CC x) = CC $ \env -> do (y, a, b) <- x env
                                  return (f y, a, b)

instance Monad CC where
  return x = CC $ \_ -> returnCC x
  CC f >>= k = CC $ \env -> do
    (x, fv1, defs1) <- f env
    case k x of
      CC g -> do
        (y, fv2, defs2) <- g env
        return (y, Set.union fv1 fv2, concatDefs defs1 defs2)

instance MonadFix CC where
  mfix f = CC $ \env -> mfix $ \ ~(x, _, _) -> case (f x) of CC f' -> f' env

instance Supplies CC (Ident Var) where
  fresh = CC $ \env -> returnCC =<< supplyValue (envVarIDSupply env)

runFreshVarCC m = CC $ \env ->
  returnCC =<< runFreshVarM (envVarIDSupply env) m

-- | Set the set of hoisted variables.  This replaces whatever was there  
-- before.  This is meant to be set for each top-level function.  
withHoistedVariables :: Set.Set Var -> CC a -> CC a
withHoistedVariables hvars (CC f) = CC $ \env ->
  f (env {envHoist = IntSet.fromList $ map (fromIdent . varID) $
                     Set.toList hvars}) 

isHoisted :: Var -> CC Bool
isHoisted v = CC $ \env ->
  returnCC $ fromIdent (varID v) `IntSet.member` envHoist env

lookupClosure :: Var -> CC (Maybe (Either Var Closure))
lookupClosure v = CC $ \env ->
  returnCC $ IntMap.lookup (fromIdent $ varID v) $ envEntryPoints env

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
    
    deleteList xs s = foldr Set.delete s xs

localClosures xs m = foldr localClosure m xs

-- | Add information about a function's closure-converted form to the
-- environment.
localClosure :: Closure -> CC a -> CC a
localClosure clo (CC f) = CC $ \env -> f (insert_closure env)
  where
    insert_closure env =
      let k = fromIdent $ varID $ closureVar clo
      in env {envEntryPoints = IntMap.insert k (Right clo) $ envEntryPoints env}

-- | Add information about some unhoisted functions to the environment.
--   Any calls to these functions will be translated to procedure calls.
withUnhoistedVariables :: [Var] -> CC a -> CC a
withUnhoistedVariables xs (CC f) = CC $ \env -> f (insert_closures env)
  where
    insert_closures env =
      env {envEntryPoints = foldr (uncurry IntMap.insert) (envEntryPoints env)
                            [(fromIdent $ varID v, Left v) | v <- xs]}

-- | Generate global functions and data from a set of global functions.
withGlobalFunctions :: [Import] -- ^ Imported functions
                    -> [FunDef] -- ^ Functions to process 
                    -> CC [Fun] -- ^ Scanner that creates direct functions
                    -> CC ()    -- ^ Code that may access functions
                    -> CC ()
withGlobalFunctions imports defs scan gen = do
  -- Create closures for imported functions
  let import_closures = [mkGlobalClosure v ep
                        | ImportClosureFun ep _ <- imports
                        , let Just v = globalClosure ep]

  -- Create closures for global functions.  Procedures don't get closures.
  global_closures <- runFreshVarCC $ mapM createGlobalClosure defs
  
  let closures = import_closures ++ catMaybes global_closures
  funs <- localClosures closures scan
  
  -- Generate code of closures
  defs' <- runFreshVarCC $
           forM (zip3 (map definiendum defs) global_closures funs) $ \(d, c, f) ->
           emitGlobalClosure d c f
  writeDefs (concat defs')
    
  -- Run other code
  localClosures closures gen

-- | Create a closure description if the function is a closure function.  
-- Otherwise return Nothing.  No code is generated.
createGlobalClosure :: FunDef -> FreshVarM (Maybe Closure)
createGlobalClosure (Def v fun)
  | isClosureFun fun = do
      entry_points <-
        case varName v
        of Just name -> mkGlobalEntryPoints (funType fun) name v
           Nothing -> mkEntryPoints NeverDeallocate (funType fun) Nothing
      return $ Just $ mkGlobalClosure v entry_points
  | otherwise = return Nothing

withLocalFunctions :: [FunDef]          -- ^ Function definitions
                   -> CC [(Fun, [Var])] -- ^ Generate a direct entry
                                        -- and list of captured
                                        -- variables for each function
                   -> (GenM () -> CC a) -- ^ Incorporate the closure code
                                        -- generator into the program
                   -> CC a
withLocalFunctions defs scan gen = check_functions $ mdo
  -- Create recursive function closures
  clos <- mkRecClosures defs captureds
  
  -- Scan functions
  (unzip -> ~(funs, captureds)) <- localClosures clos scan

  -- Generate closure code
  (defs', gen_code) <- runFreshVarCC $ emitRecClosures clos funs
  writeDefs defs'
  
  -- Generate remaining code
  localClosures clos $ gen gen_code
  where
    check_functions k = foldr check_function k defs

    -- Verify that the argument is a closure function, not a prim function.
    check_function def k =
      if isClosureFun $ definiens def
      then k
      else internalError "withLocalFunctions: Function does not require closure conversion"

-- | Create closure descriptions for a set of recursive functions.
-- No code is generated.
mkRecClosures defs captureds = do
  -- Create entry points structure
  deallocator_fn <- newAnonymousVar (PrimType PointerType)
  entry_points <- forM defs $ \(Def v f) ->
    mkEntryPoints (CustomDeallocator deallocator_fn) (funType f) (varName v)
 
  return $ closureGroup $
    lazyZip3 (map definiendum defs) entry_points captureds
  where
    -- The captured variables are generated lazily; must not be strict
    lazyZip3 (x:xs) (y:ys) ~(z:zs) = (x,y,z):lazyZip3 xs ys zs
    lazyZip3 []     _      _       = []

-- | Write some global object definitions
writeDefs :: Defs -> CC ()
writeDefs defs = CC $ \_ ->
  return ((), Set.empty, defs) 

writeFun f = writeDefs $ mkDefs [f] []
writeData d = writeDefs $ mkDefs [] [d]

-- | Record that a variable has been used.  Global variables are ignored.
mention :: Var -> CC ()
mention v = CC $ \env ->
  let free_vars = if fromIdent (varID v) `IntSet.member` envGlobals env
                  then Set.empty
                  else Set.singleton v
  in free_vars `seq` return ((), free_vars, noDefs)

-- | Record that some variables have been used.  Global variables are ignored.
mentions :: [Var] -> CC ()
mentions vs = CC $ \env ->
  let globals = envGlobals env
      free_vars = Set.fromList $
                  filter (not . (`IntSet.member` globals) . fromIdent . varID) vs
  in free_vars `seq` return ((), free_vars, noDefs)

-- | Get the set of free variables that were used in the computation.
listenFreeVars :: CC a -> CC (a, FreeVars)
listenFreeVars (CC m) = CC $ \env -> do
  (x, free_vars, defs) <- m env
  return ((x, free_vars), free_vars, defs)

-------------------------------------------------------------------------------
-- Closure and record type definitions

-- | Create a record whose fields have the same type as the given values.
valuesRecord :: [Val] -> StaticRecord
valuesRecord vals = staticRecord $ map (PrimField . valPrimType) vals

primTypesRecord :: [PrimType] -> StaticRecord
primTypesRecord tys = staticRecord $ map PrimField tys

promotedPrimTypesRecord :: [PrimType] -> StaticRecord
promotedPrimTypesRecord tys =
  staticRecord $ map (PrimField . promoteType) tys

-- | A recursive group's shared closure record.  The record contains captured
-- variables and pointers to functions in the group.
groupSharedRecord :: StaticRecord -> StaticRecord -> StaticRecord
groupSharedRecord captured_record group_record =
  staticRecord [RecordField captured_record, RecordField group_record]

-- | A description of a function closure.  The description is used to create
--   all the code and static data for the function other than the direct entry
--   point.
data Closure =
  Closure
  { -- | The variable that will point to this closure.  If the function 
    --   originally was bound to a variable, this is the same variable.
    --   If it was a lambda function, this is a new anonymous variable.
    _cVariable :: !Var
    -- | True if the closure is for a global function.  If True, the closure
    -- is not recursive, has no captured variables, and will be generated as 
    -- a statically allocated, global object.
  , _cIsGlobal :: {-# UNPACK #-} !Bool
    -- | The entry points for the function that this closure defines
  , _cEntryPoints :: EntryPoints
    -- | Variables captured by the closure.  In a closure group, the captured
    -- variables are shared by all group members.
  , _cCaptured :: [Var]
    -- | If the closure is part of a recursively defined group,
    --   these are the closures in the group.  All closures in the group  
    --   have the same group.  A closure is part of its own group.
  , _cGroup    :: !(Maybe ClosureGroup)
    -- | The closure's record type
  , _cRecord :: StaticRecord
    -- | The type of a record holding the closure's captured variables
  , _cCapturedRecord :: StaticRecord
    -- | If the closure is part of a recursively defined group,
    -- this is the shared record type.
  , _cSharedRecord :: !(Maybe StaticRecord)
  }

closureType c = entryPointsType $ _cEntryPoints c

closureIsGlobal c = _cIsGlobal c
closureIsRecursive c = isJust (_cGroup c)
closureIsLocal c = not $ closureIsGlobal c || closureIsRecursive c

-- | Get the variable that holds a closure value
closureVar c = _cVariable c

closureEntryPoints c = _cEntryPoints c

closureArity c = functionArity $ _cEntryPoints c

-- | Get the direct entry point of a closure
closureDirectEntry c = directEntry $ _cEntryPoints c
 
-- | Get the exact entry point of a closure
closureExactEntry c = exactEntry $ _cEntryPoints c

-- | Get the ineexact entry point of a closure
closureInexactEntry c = inexactEntry $ _cEntryPoints c

-- | Get the info table variable of a closure
closureInfoTableEntry c = infoTableEntry $ _cEntryPoints c

-- | Get the deallocation entry point of a closure
closureDeallocEntry c = deallocEntry $ _cEntryPoints c

closureCapturedVariables :: Closure -> [Var]
closureCapturedVariables c = _cCaptured c

-- | Get the record type of the closure
closureRecord :: Closure -> StaticRecord
closureRecord clo = _cRecord clo

-- | Get the record type of the closure's captured variables.  Each field of
-- the record holds the corresponding captured variable from the captured
-- variable list.
closureCapturedRecord :: Closure -> StaticRecord
closureCapturedRecord clo = _cCapturedRecord clo

-- | Get the record type of the closure's recursive group pointers.  Only
-- recursive closures have this record.
closureGroupRecord :: Closure -> StaticRecord
closureGroupRecord clo =
  case fieldType $ recordFields (closureSharedRecord clo) !! 1
  of RecordField t -> t
     _ -> internalError "closureGroupRecord"

-- | Get the record type of the closure's group-shared data.  Only recursive 
-- closures have a shared record.
closureSharedRecord :: Closure -> StaticRecord
closureSharedRecord clo =
  case _cSharedRecord clo
  of Just r  -> r
     Nothing -> internalError "closureSharedRecord: Not a recursive closure"

type ClosureGroup = [Closure]

-- | Construct a closure.  The closure's record types and info table 
-- contents are constructed.
--
-- This function is only called from the higher-level closure constructor 
-- functions.  Argument checking is performed there.
closure :: Var                  -- ^ Closure variable name
        -> Bool                 -- ^ True if closure is for a global function
        -> EntryPoints          -- ^ Function entry points
        -> [Var]                -- ^ Captured variables
        -> Maybe ClosureGroup   -- ^ Recursive group
        -> Closure
closure var is_global entry captured recursive = checks $
  Closure { _cVariable       = var
          , _cIsGlobal       = is_global
          , _cEntryPoints    = entry
          , _cCaptured       = captured
          , _cGroup          = recursive
          , _cRecord         = closure_record
          , _cCapturedRecord = captured_record
          , _cSharedRecord   = shared_record
          }
  where
    checks k
      -- Closure variable must be owned
      | varType var /= PrimType OwnedType =
          internalError "closure: Wrong variable type"
      -- If global, captured variables must be empty
      | is_global && not (null captured) =
          internalError "closure: Top-level function cannot capture variables"
      -- If global, must not be recursive
      | is_global && is_recursive_group =
          internalError ("closure: Top-level function cannot be part of " ++
                         "a recursive definition")
      | otherwise = k

    -- True if this closure is part of a recursive closure group
    is_recursive_group = isJust recursive

    -- Captured variables
    captured_record = staticRecord $ map (PrimField . varPrimType) captured
    
    -- If this function is part of a recursive group, the closure contains 
    -- only a reference to the shared record.  If global, it contains only  
    -- the header.  Otherwise, it contains the captured variables.
    closure_record
      | is_global = globalClosureRecord
      | is_recursive_group = recursiveClosureRecord
      | otherwise = localClosureRecord captured_record

    -- The shared record contains the captured variables and the 
    -- functions in the group.
    shared_record =
      case recursive
      of Just closures ->
           let group_record =
                 staticRecord $
                 replicate (length closures) (PrimField PointerType)
           in Just $ groupSharedRecord captured_record group_record
         Nothing -> Nothing

mkNonrecClosure :: Var -> EntryPoints -> [Var] -> Closure
mkNonrecClosure v e cap = closure v False e cap Nothing

mkGlobalClosure :: Var -> EntryPoints -> Closure
mkGlobalClosure v e = closure v True e [] Nothing

closureGroup :: [(Var, EntryPoints, [Var])] -> ClosureGroup
closureGroup xs = group
  where
    group = [closure v False e cap (Just group) | (v, e, cap) <- xs]
  
-------------------------------------------------------------------------------

-- | Initialize a captured variables record
initializeCapturedVariables :: Val -> Closure -> GenM ()
initializeCapturedVariables captured_ptr clo =
  zipWithM_ init_var (recordFields $ closureCapturedRecord clo)
  (closureCapturedVariables clo)
  where
    init_var field var = storeField field captured_ptr (VarV var)

-- | Finalize a captured variables record by explicitly decrementing
-- members' reference counts.
finalizeCapturedVariables :: Val -> Closure -> Gen FreshVarM ()
finalizeCapturedVariables captured_ptr clo =
  mapM_ finalize_field (recordFields $ closureCapturedRecord clo)
  where
    finalize_field field 
      | fieldType field == PrimField OwnedType = do
          decrefObject True =<< loadFieldWithoutOwnership field captured_ptr
      | PrimField _ <- fieldType field = return ()
      | otherwise = internalError "finalizeCapturedVariables"

-- | Allocate, but do not initialize, a closure.
-- The created closure is returned.
allocateClosure :: Closure -> GenM Val
allocateClosure clo =
  allocateHeapMem $ nativeWordV $ recordSize $ closureRecord clo

-- | Initialize a closure.
--
-- The first argument is a pointer to the shared closure record, only used 
-- in recursive groups.
--
-- The initialized closure is assigned to the variable given in
-- the 'cloVariable' field.
initializeClosure :: Val -> Closure -> Val -> GenM ()
initializeClosure group_record clo clo_ptr = do
  initializeObject clo_ptr (VarV $ closureInfoTableEntry clo)
  initialize_specialized_fields
  bindAtom1 (closureVar clo) $ PrimA PrimCastToOwned [clo_ptr]
  where
    initialize_specialized_fields
      -- Recursive closure contains a pointer to the shared record
      | closureIsRecursive clo = do
          storeField (closureRecord clo !!: 1) clo_ptr group_record

      -- Global closure only contains object fields
      | closureIsGlobal clo = return ()
  
      -- Non-global closure contains captured variables
      | otherwise = do
          captured_ptr <- referenceField (closureRecord clo !!: 1) clo_ptr
          initializeCapturedVariables captured_ptr clo

-- | Generate a free function for a non-recursive, non-top-level closure.
-- The free function is added to the set of top-level definitions.
generateClosureFree :: Closure -> FreshVarM Defs
generateClosureFree clo 
  | not $ closureIsLocal clo =
      internalError "generateClosureFree: Not a local closure"

  | Just dealloc_fun <- closureDeallocEntry clo,
    isDefaultDeallocator dealloc_fun =
      -- Using the default deallocator.  Don't define anything.
      return []

  | Nothing <- closureDeallocEntry clo =
      -- Local closures must have a dealloc entry
      internalError "generateClosureFree"

  | Just dealloc_fun <- closureDeallocEntry clo = do
  param <- newAnonymousVar (PrimType PointerType)
  fun_body <- execBuild [] $ do
    -- Free the captured variables
    captured_vars <- referenceField (closureRecord clo !!: 1) (VarV param)
    finalizeCapturedVariables captured_vars clo
    
    -- Deallocate the closure
    deallocateHeapMem (VarV param)
    gen0
  
  -- Write this to the closure's deallocation function entry
  let fun = primFun [param] [] fun_body
  return $ mkDefs [Def dealloc_fun fun] []

-- | Generate a shared closure record value and a function that frees the
-- entire recursive function group.
generateSharedClosureRecord :: ClosureGroup -> [Val] -> GenM Val
generateSharedClosureRecord clos ptrs = do
  -- Create a new record
  shared_ptr <- allocateHeapMem $ nativeWordV $ sizeOf record

  -- Initialize its fields
  captured_vars_ptr <- referenceField (record !!: 0) shared_ptr
  initializeCapturedVariables captured_vars_ptr a_closure
  group_record_ptr <- referenceField (record !!: 1) shared_ptr
  initialize_group_pointers group_record_ptr ptrs
  
  -- Return the record and free function
  return shared_ptr
  where
    a_closure = head clos
    record = closureSharedRecord a_closure
    group_record = closureGroupRecord a_closure

    initialize_group_pointers record_ptr ptrs =
      zipWithM_ init_ptr (recordFields group_record) ptrs
      where
        init_ptr field ptr = storeField field record_ptr ptr

-- | Generate the free function for a shared closure record.
--
-- The free function takes a closure record as a parameter (all recursive
-- closures have a pointer to teh shared record in the same place).
-- It first checks whether all records in the group have a
-- reference count of zero.  If so, then each record is deallocated and the
-- shared closure as a whole is deallocated.
emitSharedClosureRecordFree :: Var -> ClosureGroup -> FreshVarM FunDef
emitSharedClosureRecordFree fun_var clos = do
  param <- newAnonymousVar (PrimType PointerType)
  fun_body <- execBuild [] $ do
    -- Get the shared record
    shared_rec <-
      loadField (recursiveClosureRecord !!: 1) (VarV param)

    -- Check whether all reference counts are 0
    all_reference_counts_zero <-
      foldOverGroup check_reference_count (LitV $ BoolL True) clos shared_rec

    -- If so, then free everything.  Otherwise, do nothing.
    genIf all_reference_counts_zero (free_everything shared_rec) gen0
  
  -- Write the global function
  let fun = primFun [param] [] fun_body
  return $ Def fun_var fun
  where
    -- Check whether reference count is zero and update accumulator.
    -- acc = acc && (closure_ptr->refct == 0)
    check_reference_count acc _ closure_ptr = do
      refct <- loadField (objectHeaderRecord !!: 0) closure_ptr
      refct_zero <- primCmpZ (PrimType nativeIntType) CmpEQ refct (nativeIntV 0)
      primAnd acc refct_zero

    free_everything shared_ptr = do
      -- Deallocate each closure.  The closures do not need finalization.
      () <- foldOverGroup deallocate_closure () clos shared_ptr
      
      -- Release all captured variables
      captured_vars_ptr <-
        referenceField (closureSharedRecord a_closure !!: 0) shared_ptr
      finalizeCapturedVariables captured_vars_ptr a_closure

      -- Deallocate the shared record
      deallocateHeapMem shared_ptr
      gen0

    deallocate_closure () _ closure_ptr = deallocateHeapMem closure_ptr

    a_closure = head clos

-- | Generate code that processes each member of a closure group.
foldOverGroup :: (Monad m, Supplies m (Ident Var)) =>
                 (a -> Closure -> Val -> Gen m a)
              -> a
              -> ClosureGroup
              -> Val            -- ^ Pointer to shared closure record
              -> Gen m a
foldOverGroup f init group shared_ptr = do
  let shared_record = closureSharedRecord $ head group
  let group_record = closureGroupRecord $ head group
  group_ptr <- referenceField (shared_record !!: 1) shared_ptr
  
  -- Worker routine passes 'f' an un-owned pointer to the closure record
  let worker acc (clo, i) = do
        x <- loadField (group_record !!: i) group_ptr
        f acc clo x
        
  foldM worker init $ zip group [0..]

-- | Generate a statically defined closure object for a global function.
generateGlobalClosure :: Closure -> FreshVarM DataDef
generateGlobalClosure clo
  | not $ closureIsGlobal clo =
      internalError "emitGlobalClosure: Wrong closure type"
  | otherwise =
      let closure_values =
            [ RecV objectHeaderRecord $
              objectHeaderData $ VarV $ closureInfoTableEntry clo]
          static_value = StaticData (flattenStaticRecord globalClosureRecord) (flattenGlobalValues closure_values)
      in return $ Def (closureVar clo) static_value
         

-- | Generate code to construct a single closure.
generateLocalClosure :: Closure -> GenM () 
generateLocalClosure clo
  | closureIsRecursive clo || closureIsGlobal clo =
      internalError "emitLocalClosure: Not a local closure"
  | otherwise = do
      ptr <- allocateClosure clo
      initializeClosure invalid clo ptr
  where
    invalid = internalError "emitLocalClosure: Not recursive"
                            
-- | Generate code to construct a group of closures.
generateRecursiveClosures :: ClosureGroup -> GenM () 
generateRecursiveClosures clos = do
  ptrs <- mapM allocateClosure clos
  shared_data <- generateSharedClosureRecord clos ptrs
  zipWithM_ (initializeClosure shared_data) clos ptrs

-- | Emit the exact entry point of a function.
--
-- The entry point takes a closure pointer and the function's direct 
-- parameters.
emitExactEntry :: Closure -> FreshVarM FunDef
emitExactEntry clo = do
  clo_ptr <- newAnonymousVar (PrimType OwnedType)
  params <- mapM newAnonymousVar $ ftParamTypes $ closureType clo
  let return_types = ftReturnTypes $ closureType clo
  fun_body <- execBuild return_types $ do
    -- Load each captured variable
    cap_vars <- load_captured_vars (VarV clo_ptr)
    -- Call the direct entry point
    let direct_entry = VarV $ closureDirectEntry clo
    return $ ReturnE $ primCallA direct_entry (cap_vars ++ map VarV params)

  let fun = primFun (clo_ptr : params) return_types fun_body
  return $ Def (closureExactEntry clo) fun
  where
    load_captured_vars clo_ptr
      | closureIsRecursive clo = do
          -- Captured variables are in the shared record
          shared_record <- loadField (recursiveClosureRecord !!: 1) clo_ptr
          captured_vars <-
            referenceField (closureSharedRecord clo !!: 0) shared_record
          load_captured_vars' captured_vars
      | closureIsLocal clo = do
          -- Captured variables are in the closure
          let field = localClosureRecord (closureCapturedRecord clo) !!: 1
          captured_vars <- referenceField field clo_ptr
          load_captured_vars' captured_vars
      | closureIsGlobal clo =
          -- Global closures don't capture variables
          return []

    -- Load all captured variables out of the record
    load_captured_vars' captured_ptr =
      sequence [loadField fld captured_ptr
               | fld <- recordFields $ closureCapturedRecord clo]


-- | Emit the inexact entry point of a function.
--
-- The inexact entry point takes the closure, a record holding function
-- parameters, and an unitialized record to hold function return values.
emitInexactEntry :: Closure -> FreshVarM FunDef
emitInexactEntry clo = do
  clo_ptr <- newAnonymousVar (PrimType OwnedType)
  params_ptr <- newAnonymousVar (PrimType PointerType)
  returns_ptr <- newAnonymousVar (PrimType PointerType)
  fun_body <- execBuild [] $ do
    -- Load each parameter value from the parameters record
    param_vals <- load_parameters (VarV params_ptr)

    -- Call the exact entry
    let exact_entry = VarV $ closureExactEntry clo
    return_vals <- emitAtom (ftReturnTypes $ closureType clo) $
                   primCallA exact_entry (VarV clo_ptr : param_vals)

    -- Store each return value
    store_parameters (VarV returns_ptr) return_vals
    gen0
  let fun = primFun [clo_ptr, params_ptr, returns_ptr] [] fun_body
  return $ Def (closureInexactEntry clo) fun
  where
    load_parameters params_ptr =
      sequence [loadField fld params_ptr
               | fld <- recordFields param_record]    

    store_parameters returns_ptr return_vals =
      sequence [storeField fld returns_ptr val
               | (fld, val) <- zip (recordFields return_record) return_vals]

    store_field ptr fld return_val = storeField fld ptr return_val

    -- Record type of parameters
    param_record = promotedPrimTypesRecord $
                   map valueToPrimType $
                   ftParamTypes $ closureType clo
  
    -- Record type of returns
    return_record = promotedPrimTypesRecord $
                    map valueToPrimType $
                    ftReturnTypes $ closureType clo

-- | Generate the info table entry for a closure
emitInfoTable :: Closure -> FreshVarM DataDef
emitInfoTable clo =
  let arg_type_fields = replicate (length arg_type_tags) $
                        PrimField (IntType Unsigned S8)
      record_type =
        staticRecord (RecordField funInfoHeaderRecord : arg_type_fields)
      info_table = closureInfoTableEntry clo
      static_value = StaticData (flattenStaticRecord record_type) (flattenGlobalValues fun_info)
  in return $ Def info_table static_value
  where
    -- see 'funInfoHeader'
    info_header =
      [ maybe (LitV NullL) VarV $ closureDeallocEntry clo -- free object
      , uint8V $ fromEnum FunTag                     -- object type tag
      ]
    fun_info_header =
      [ RecV infoTableHeaderRecord info_header
      , uint16V $ closureArity clo
      , VarV $ closureExactEntry clo
      , VarV $ closureInexactEntry clo]
    fun_info =
      RecV funInfoHeaderRecord fun_info_header : arg_type_tags

    arg_type_tags =
      map (uint8V . fromEnum . toBitsTag . promoteType . fromPrimType) $
      ftParamTypes $ closureType clo
      where
        fromPrimType (PrimType t) = t
        fromPrimType _ = internalError "emitInfoTable: Unexpected record type"
    

-- | Generate the code and data of a global function.  For closure functions,
-- an info table, a global closure, and entry points are generated.  For
-- primitive functions, only the global function is generated.
emitGlobalClosure :: Var -> Maybe Closure -> Fun -> FreshVarM Defs

-- Emit a closure function
emitGlobalClosure direct_entry (Just clo) direct = do
  info_def <- emitInfoTable clo
  let direct_def = Def (closureDirectEntry clo) direct
  exact_def <- emitExactEntry clo
  inexact_def <- emitInexactEntry clo
  
  -- Global closures must not use a deallocation function
  when (isJust $ closureDeallocEntry clo) $
    internalError "emitGlobalClosure: Must not have deallocator"
  closure_def <- generateGlobalClosure clo
  
  return $ mkDefs [direct_def, exact_def, inexact_def] [info_def, closure_def]

-- Emit a primitive function
emitGlobalClosure direct_entry Nothing direct = do
  return $ mkDefs [Def direct_entry direct] []

-- | Generate the code and data of a group of recursive closures.
-- An info table and entry points are generated.  The code for dynamically
-- allocating closures is returned.
emitRecClosures :: ClosureGroup -> [Fun] -> FreshVarM (Defs, GenM ())
emitRecClosures grp directs = do
  -- Emit info table and entry points of each function 
  member_defs <- forM (zip grp directs) $ \(clo, direct) -> do
    info_def <- emitInfoTable clo
    let direct_def = Def (closureDirectEntry clo) direct
    exact_def <- emitExactEntry clo
    inexact_def <- emitInexactEntry clo
    return ([direct_def, exact_def, inexact_def], [info_def])
    
  -- Emit the deallocation function.  
  -- All members of the group use the same one.
  let free_var = case closureDeallocEntry $ head grp
                 of Just v -> v
                    Nothing -> internalError "emitRecClosures"
  free_def <- emitSharedClosureRecordFree free_var grp
  
  -- Return code for generating closures
  let defs = mkDefs [free_def] [] ++ member_defs
  return (defs, generateRecursiveClosures grp)

-- | Generate the code and data of a lambda function
emitLambdaClosure :: FunctionType -> Fun -> [Var] -> CC (GenM Val)
emitLambdaClosure lambda_type direct captured_vars = do
  (defs, gen_closure) <-
    runFreshVarCC $ emitLambdaClosure1 lambda_type direct captured_vars
  writeDefs defs
  return gen_closure

emitLambdaClosure1 :: FunctionType -> Fun -> [Var]
                   -> FreshVarM (Defs, GenM Val)
emitLambdaClosure1 lambda_type direct captured_vars = do
  fun_var <- newAnonymousVar (PrimType OwnedType)  

  -- Use the default deallocation function if there are no captured variables
  want_dealloc <-
    if null captured_vars
    then return DefaultDeallocator
    else do v <- newAnonymousVar (PrimType PointerType)
            return $ CustomDeallocator v

  entry_points <- mkEntryPoints want_dealloc lambda_type Nothing
  let clo = mkNonrecClosure fun_var entry_points captured_vars
      
  -- Generate code
  info_def <- emitInfoTable clo
  let direct_def = Def (closureDirectEntry clo) direct
  exact_def <- emitExactEntry clo
  inexact_def <- emitInexactEntry clo
  free_defs <- generateClosureFree clo
  
  -- Create the function variable, then pass it as a parameter to something 
  let gen_closure = do generateLocalClosure clo
                       return $ VarV fun_var
  
  return (free_defs ++ mkDefs [direct_def, exact_def, inexact_def] [info_def],
          gen_closure)

-------------------------------------------------------------------------------

-- | Generate a call to a variable.  If the variable has a known direct entry
-- point and is applied to enough arguments, a direct call is generated.
-- Otherwise, an indirect call is generated.
genVarCall :: [PrimType]        -- ^ Return types
           -> Var               -- ^ Function that is called
           -> [GenM Val]        -- ^ Argument generators
           -> CC (GenM Atom)
genVarCall return_types fun args = lookupClosure fun >>= select
  where
    use_fun = mention fun >> return (return (VarV fun))

    -- Unknown function
    select Nothing = do
      op <- use_fun
      genIndirectCall return_types op args
    
    -- Function converted to local procedure.
    -- All calls are direct primitive calls and no variables are captured.
    select (Just (Left v)) =
      return $ do args' <- sequence args
                  return $ primCallA (VarV v) args'

    -- Function converted to closure-based function.  Check the arity to
    -- decide what kind of call to generate.
    select (Just (Right ep)) =
      case length args `compare` arity
      of LT -> do               -- Undersaturated
           op <- use_fun
           genIndirectCall return_types op args
         EQ -> do               -- Saturated
           return $ directCall captured_vars entry args
         GT -> do
           -- Oversaturated; generate a direct call followed by an
           -- indirect call
           let (direct_args, indir_args) = splitAt arity args
           let direct_call = directCall captured_vars entry direct_args
           let direct_val = emitAtom1 (PrimType OwnedType) =<< direct_call
           genIndirectCall return_types direct_val indir_args
      where
        arity = closureArity ep
        entry = closureDirectEntry ep
        captured_vars = closureCapturedVariables ep

-- | Produce a direct call to the given primitive function.
directCall :: [Var] -> Var -> [GenM Val] -> GenM Atom
directCall captured_vars v args = do
  args' <- sequence args
  let captured_args = map VarV captured_vars
  return $ primCallA (VarV v) (captured_args ++ args')

-- | Produce an indirect call of the given operator
genIndirectCall :: [PrimType]   -- ^ Return types
                -> GenM Val     -- ^ Called function
                -> [GenM Val]   -- ^ Arguments
                -> CC (GenM Atom)

-- No arguments to closure function: Don't call
genIndirectCall return_types mk_op [] = return $ do
  op <- mk_op
  return $ ValA [op]

genIndirectCall return_types mk_op mk_args = return $ do
  op <- mk_op
  args <- sequence mk_args

  -- Get the function info table and captured variables
  inf_ptr <- loadField (objectHeaderRecord !!: 1) op

  -- Can make an exact call if the callee is a function and
  -- the number of arguments matches the function's arity
  inf_tag <- loadField (infoTableHeaderRecord !!: 1) inf_ptr
  inf_tag_test <- primCmpZ (PrimType (IntType Unsigned S8)) CmpEQ inf_tag $
                  uint8V $ fromEnum FunTag

  -- Branch to the code for an exact or an inexact call
  ret_vars <- lift $ mapM newAnonymousVar return_types'
  getContinuation True ret_vars $ \cont -> do
    exact_call <- lift $
                  execBuild return_types' $
                  make_exact_call ret_vars op inf_ptr args cont

    inexact_call_var <- lift $ newAnonymousVar (PrimType PointerType)
    inexact_call <- lift $ fmap (primFun [] return_types') $
                    execBuild return_types' $
                    make_inexact_call ret_vars op args cont
    emitLetrec [Def inexact_call_var inexact_call]
    
    check_arity <-
      lift $ execBuild return_types' $ do
        -- Compare function arity to number of given arguments
        arity <- loadField (funInfoHeaderRecord !!: 1) inf_ptr
        arity_eq <- primCmpZ (PrimType nativeWordType) CmpEQ arity $
                    nativeWordV $ length args
        return $ SwitchE arity_eq [(BoolL True, exact_call),
                                   (BoolL False, ReturnE $ primCallA (VarV inexact_call_var) [])]

    -- Check function tag.  If it's a function tag, then check its arity.
    -- If arity matches, do a direct call.
    return $ SwitchE inf_tag_test [(BoolL True, check_arity),
                                   (BoolL False, ReturnE $ primCallA (VarV inexact_call_var) [])]
  return $ ValA (map VarV ret_vars)
  where
    return_types' = map PrimType return_types

    make_exact_call ret_vars clo_ptr inf_ptr args cont = do
      -- Get the exact entry point
      fn <- loadField (funInfoHeaderRecord !!: 2) inf_ptr

      -- Get the function's captured variables, then call the function
      bindAtom ret_vars $ primCallA fn (clo_ptr : args)
      return cont

    make_inexact_call ret_vars clo_ptr args cont = do
      -- Create temporary storage for return values
      let ret_record = staticRecord $ map PrimField return_types
      ret_ptr <- allocateHeapMem $ nativeWordV $ recordSize ret_record

      -- Apply the function
      genApply clo_ptr args ret_ptr

      -- Extract return values, stealing references
      ret_vals <- mapM (load_ret_value ret_ptr) $ recordFields ret_record

      -- Free temporary storage
      deallocateHeapMem ret_ptr
      bindAtom ret_vars $ ValA ret_vals
      return cont

    -- Load each return value out of the heap record.  Don't increment the
    -- reference count, since the record will be deallocated.
    load_ret_value ptr fld =
      case fieldType fld
      of PrimField OwnedType -> do
           val <- loadFieldWithoutOwnership fld ptr
           emitAtom1 (PrimType OwnedType) $ PrimA PrimCastToOwned [val]
         _ -> loadField fld ptr

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
applyFunctions = [ (Int32Tag, i_node)
                 , (Float32Tag, f_node)
                 , (OwnedRefTag, o_node)]
  where
    i_node = ApplyTrieNode 
             (llBuiltin the_prim_apply_i32_f) 
             (llBuiltin the_prim_apply_i32)
             []
    f_node = ApplyTrieNode
             (llBuiltin the_prim_apply_f32_f)
             (llBuiltin the_prim_apply_f32)
             []
    o_node = ApplyTrieNode
             (llBuiltin the_prim_apply_o_f)
             (llBuiltin the_prim_apply_o)
             []
