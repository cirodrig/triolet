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

{-# LANGUAGE FlexibleInstances, RecursiveDo, ViewPatterns #-}
module LowLevel.ClosureCode
       (varPrimType,
        GenM, CC,
        runCC,
        lookupEntryPoints',
        lookupCallVar,
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
-- set of free variables referenced in that part of the program.  (Globals
-- are not included in the set since they cannot be captured.)
--
-- During scanning, new global definitions are generated.  These definitions
-- comprise the translated module.
newtype CC a = CC (CCEnv -> IO (a, FreeVars, Defs))

data CCEnv =
  CCEnv
  { envVarIDSupply :: {-# UNPACK #-}!(IdentSupply Var)
    -- | IDs of global variables.  Global variables are never captured.
  , envGlobals :: !IntSet.IntSet
    -- | Information about how to construct closures for functions that are
    -- in scope.
  , envEntryPoints :: !(IntMap.IntMap Closure)
  }

emptyCCEnv var_ids globals =
  let globals_set = IntSet.fromList $ map (fromIdent . varID) globals
  in CCEnv var_ids globals_set IntMap.empty

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

{-
-- | Add a function's entry points to the environment
withEntryPoints :: Var -> EntryPoints -> CC a -> CC a
withEntryPoints fname entry_points (CC m) = CC $ m . insert_entry
  where
    insert_entry env =
      let key = fromIdent $ varID fname
      in env { envEntryPoints = IntMap.insert key entry_points $
               envEntryPoints env}
-}

lookupClosure :: Var -> CC (Maybe Closure)
lookupClosure v = CC $ \env ->
  returnCC $ IntMap.lookup (fromIdent $ varID v) $ envEntryPoints env

lookupEntryPoints :: Var -> CC (Maybe EntryPoints)
lookupEntryPoints v = CC $ \env ->
  returnCC $ fmap closureEntryPoints $ IntMap.lookup (fromIdent $ varID v) $
  envEntryPoints env

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
    
    deleteList xs s = foldr Set.delete s xs


{-
-- | Scan some code over which some functions are defined.  New variables will 
-- be created for the functions' entry points and info tables.  This function 
-- does not create definitions of these variables.
--
-- The flag to use the default deallocation function should be true for
-- global functions and false otherwise.
withFunctions :: WantClosureDeallocator
              -> [FunDef]
              -> CC ([Closure], a)
              -> CC a
withFunctions want_dealloc defs m = foldr with_function m defs
  where
    with_function (FunDef v fun) m = do
      entry_points <- mkEntryPoints want_dealloc (funType fun) (varName v)
      insert_entry_points (fromIdent $ varID v) entry_points m

    insert_entry_points key entry_points (CC f) = CC $ \env ->
      f $ env { envEntryPoints = IntMap.insert key entry_points $
                                 envEntryPoints env}
-}

localClosures xs m = foldr localClosure m xs

localClosure :: Closure -> CC a -> CC a
localClosure clo (CC f) = CC $ \env -> f (insert_closure env)
  where
    insert_closure env =
      let k = fromIdent $ varID $ closureVar clo
      in env {envEntryPoints = IntMap.insert k clo $ envEntryPoints env}

-- | Generate global functions and data from a set of global functions.
withGlobalFunctions :: [FunDef] -- ^ Functions to process 
                    -> CC [Fun] -- ^ Scanner that creates direct functions
                    -> CC ()    -- ^ Code that may access functions
                    -> CC ()
withGlobalFunctions defs scan gen = do
  clos <- mapM mkGlobalClosure defs
  funs <- localClosures (catMaybes clos) scan
  forM (zip3 (map funDefiniendum defs) clos funs) $ \(d, c, f) ->
    emitGlobalClosure d c f
  gen

-- | Create a closure description if the function is a closure function.  
-- Otherwise return Nothing.  No code is generated.
mkGlobalClosure (FunDef v fun) 
  | isClosureFun fun = do
      entry_points <- mkEntryPoints NeverDeallocate (funType fun) (varName v)
      return $ Just $ globalClosure v entry_points
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
  gen_code <- emitRecClosures clos funs
  
  -- Generate remaining code
  localClosures clos $ gen gen_code
  where
    check_functions k = foldr check_function k defs

    -- Verify that the argument is a closure function, not a prim function.
    check_function def k =
      if isClosureFun $ funDefiniens def
      then k
      else internalError "withLocalFunctions: Function does not require closure conversion"

-- | Create closure descriptions for a set of recursive functions.
-- No code is generated.
mkRecClosures defs captureds = do
  -- Create entry points structure
  deallocator_fn <- newAnonymousVar (PrimType PointerType)
  entry_points <- forM defs $ \(FunDef v f) ->
    mkEntryPoints (CustomDeallocator deallocator_fn) (funType f) (varName v)
 
  return $ closureGroup $
    lazyZip3 (map funDefiniendum defs) entry_points captureds
  where
    -- The captured variables are generated lazily; must not be strict
    lazyZip3 (x:xs) (y:ys) ~(z:zs) = (x,y,z):lazyZip3 xs ys zs
    lazyZip3 []     _      _       = []

-- | Write some global object definitions
writeDefs :: [FunDef] -> [DataDef] -> CC ()
writeDefs fun_defs data_defs = CC $ \_ ->
  return ((), Set.empty, mkDefs fun_defs data_defs) 

writeFun f = writeDefs [f] []
writeData d = writeDefs [] [d]

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

-- | Get the set of free variables that were used in the computation.  Don't
-- propagate the variables.
listenFreeVars :: CC a -> CC (a, FreeVars)
listenFreeVars (CC m) = CC $ \env -> do
  (x, free_vars, defs) <- m env
  return ((x, free_vars), Set.empty, defs)

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
-- Closure and record type definitions

closureHeaderRecord' = toDynamicRecord papHeaderRecord
funInfoHeaderRecord' = toDynamicRecord funInfoHeaderRecord

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
  { -- | The variable that will point to this closure
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

{- Obsolete code

-- | Get the field that holds a reference to the recursive group's shared data.
-- This field is only present in a recursive closure.
cloRecursiveField :: Closure -> Maybe StaticField
cloRecursiveField clo
  | cloIsRecursive clo = Just $ recordFields (cloRecord clo) !! 1
  | otherwise = Nothing

cloRecursiveFields :: Closure -> [StaticField]
cloRecursiveFields clo =
  case cloGroup clo
  of Just (_, record) -> take (length (cloCaptured clo)) $
                         drop 1 $ recordFields record
     Nothing -> []

cloRecursiveFunctions :: Closure -> [StaticField]
cloRecursiveFunctions clo =
  case cloGroup clo
  of Just (grp, record) -> take (length grp) $
                           drop (1 + length (cloCaptured clo)) $
                           recordFields record
-}

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

nonrecClosure :: Var -> EntryPoints -> [Var] -> Closure
nonrecClosure v e cap = closure v False e cap Nothing

globalClosure :: Var -> EntryPoints -> Closure
globalClosure v e = closure v True e [] Nothing

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
    init_var field var =
      storeField (toDynamicField field) captured_ptr (VarV var)

-- | Finalize a captured variables record by explicitly decrementing
-- members' reference counts.
finalizeCapturedVariables :: Val -> Closure -> GenM ()
finalizeCapturedVariables captured_ptr clo =
  mapM_ finalize_field (recordFields $ closureCapturedRecord clo)
  where
    finalize_field field 
      | fieldType field == PrimField OwnedType = do
          f <- loadFieldWithoutOwnership (toDynamicField field) captured_ptr
          decrefObject f
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
          storeField (toDynamicField $ closureRecord clo !!: 1) clo_ptr group_record

      -- Global closure only contains object fields
      | closureIsGlobal clo = return ()
  
      -- Non-global closure contains captured variables
      | otherwise = do
          captured_ptr <- referenceField (toDynamicField $ closureRecord clo !!: 1) clo_ptr
          initializeCapturedVariables captured_ptr clo

-- | Generate a free function for a non-recursive, non-top-level closure.
-- The free function is added to the set of top-level definitions.
generateClosureFree :: Closure -> CC ()
generateClosureFree clo = do
  when (closureIsRecursive clo || closureIsGlobal clo) $
    internalError "generateClosureFree: Not a local closure"

  let dealloc_fun = case closureDeallocEntry clo
                    of Just x -> x
                       Nothing -> internalError "generateClosureFree"

  param <- newAnonymousVar (PrimType PointerType)
  fun_body <- execBuild $ do
    -- Free the captured variables
    captured_vars <- referenceField (toDynamicField $ closureRecord clo !!: 1) (VarV param)
    finalizeCapturedVariables captured_vars clo
    
    -- Deallocate the closure
    deallocateHeapMem (VarV param)
    gen0
  
  -- Write this to the closure's deallocation function entry
  let fun = primFun [param] [] fun_body
  writeFun $ FunDef dealloc_fun fun

-- | Generate a shared closure record value and a function that frees the
-- entire recursive function group.
generateSharedClosureRecord :: ClosureGroup -> [Val] -> GenM Val
generateSharedClosureRecord clos ptrs = do
  -- Create a new record
  shared_ptr <- allocateHeapMem $ nativeWordV $ sizeOf record

  -- Initialize its fields
  captured_vars_ptr <- referenceField (toDynamicField $ record !!: 0) shared_ptr
  initializeCapturedVariables captured_vars_ptr a_closure
  group_record_ptr <- referenceField (toDynamicField $ record !!: 1) shared_ptr
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
        init_ptr field ptr = storeField (toDynamicField field) record_ptr ptr

-- | Generate the free function for a shared closure record.
--
-- The free function takes a closure record as a parameter (all recursive
-- closures have a pointer to teh shared record in the same place).
-- It first checks whether all records in the group have a
-- reference count of zero.  If so, then each record is deallocated and the
-- shared closure as a whole is deallocated.
emitSharedClosureRecordFree :: Var -> ClosureGroup -> CC ()
emitSharedClosureRecordFree fun_var clos = do
  param <- newAnonymousVar (PrimType PointerType)
  fun_body <- execBuild $ do
    -- Get the shared record
    shared_rec <-
      loadField (toDynamicField $ recursiveClosureRecord !!: 1) (VarV param)

    -- Check whether all reference counts are 0
    all_reference_counts_zero <-
      foldOverGroup check_reference_count (LitV $ BoolL True) clos shared_rec

    -- If so, then free everything.  Otherwise, do nothing.
    genIf all_reference_counts_zero (free_everything shared_rec) gen0
  
  -- Write the global function
  let fun = primFun [param] [] fun_body
  writeFun $ FunDef fun_var fun
  where
    -- Check whether reference count is zero and update accumulator.
    -- acc = acc && (closure_ptr->refct == 0)
    check_reference_count acc _ closure_ptr = do
      refct <- loadField (toDynamicField $ objectHeaderRecord !!: 0) closure_ptr
      refct_zero <- primCmpZ (PrimType nativeIntType) CmpEQ refct (nativeIntV 0)
      primAnd acc refct_zero

    free_everything shared_ptr = do
      -- Deallocate each closure.  The closures do not need finalization.
      () <- foldOverGroup deallocate_closure () clos shared_ptr
      
      -- Release all captured variables
      captured_vars_ptr <-
        referenceField (toDynamicField $ closureSharedRecord a_closure !!: 0) shared_ptr
      finalizeCapturedVariables captured_vars_ptr a_closure

      -- Deallocate the shared record
      deallocateHeapMem shared_ptr
      gen0

    deallocate_closure () _ closure_ptr = deallocateHeapMem closure_ptr

    a_closure = head clos

-- | Generate code that processes each member of a closure group.
foldOverGroup :: (a -> Closure -> Val -> GenM a)
              -> a
              -> ClosureGroup
              -> Val            -- ^ Pointer to shared closure record
              -> GenM a
foldOverGroup f init group shared_ptr = do
  let shared_record = closureSharedRecord $ head group
  let group_record = closureGroupRecord $ head group
  group_ptr <- referenceField (toDynamicField $ shared_record !!: 1) shared_ptr
  
  -- Worker routine passes 'f' an un-owned pointer to the closure record
  let worker acc (clo, i) = do
        x <- loadField (toDynamicField $ group_record !!: i) group_ptr
        f acc clo x
        
  foldM worker init $ zip group [0..]

-- | Generate a statically defined closure object for a global function.
generateGlobalClosure :: Closure -> CC DataDef
generateGlobalClosure clo
  | not $ closureIsGlobal clo =
      internalError "emitGlobalClosure: Wrong closure type"
  | otherwise =
      let closure_values =
            [ RecV objectHeaderRecord $
              objectHeaderData $ VarV $ closureInfoTableEntry clo]
      in return $
         DataDef (closureVar clo) (flattenStaticRecord globalClosureRecord)
         (flattenGlobalValues closure_values)

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

{- Obsolete code
-- | Construct a function to free a non-recursive closure.
--
-- Reference counting is generated explicitly in this function.
-- To ensure that no reference counting is automatically inserted, the
-- generated function manipulates non-owned pointer types.
generateClosureFree :: Closure -> CC ()
generateClosureFree clo 
  | cloIsRecursive clo =
      internalError "generateClosureFree: Closure is part of a recursive group"
      
  | Just dealloc_entry <- deallocEntry $ cloEntryPoints clo,
    not $ isDefaultDeallocator dealloc_entry = do
      -- Generate a custom deallocation function
      clo_ptr <- newAnonymousVar (PrimType PointerType)
      fun_body <- execBuild $ do generateClosureFreeBody clo (VarV clo_ptr)
                                 gen0
      let fun = primFun [clo_ptr] [] fun_body
      writeFun $ FunDef dealloc_entry fun

  | otherwise =
      -- Using the default or no deallocation function
      return ()
      
-- | Construct functions to free a group of mutually recursive closures.
-- These consist of entry points that find all recursive functions in the
-- group, then call a common function to free them.
generateClosureGroupFree :: ClosureGroup -> CC ()
generateClosureGroupFree group = do
  -- Define the real freeing code
  shared_free_fun <- newAnonymousVar (PrimType PointerType)
  sdef <- define_shared_fun shared_free_fun
  
  -- Create entry points for each closure
  edefs <- mapM (define_entry_point shared_free_fun) group
  
  writeDefs (sdef : edefs) []
  where
    -- Define an entry point.  The entry point finds all recursive closures
    -- and then proceeds to free them.
    define_entry_point shared_free_fun clo = do
      param <- newAnonymousVar (PrimType PointerType)
      fun_body <- execBuild $ do
        -- Get pointers to all closures
        closures <- sequence [loadField fld (VarV param)
                             | fld <- map toDynamicField $
                                      cloRecursiveFields clo]
        -- Call the common function
        return $ PrimCallA (VarV shared_free_fun) closures
      let fun = primFun [param] [] fun_body
          
      -- Must be using a custom deallocation function
      let dealloc_entry =
            case deallocEntry (cloEntryPoints clo)
            of Just v | not $ isDefaultDeallocator v -> v 
               _ -> internalError "generateClosureGroupFree: \
                                  \Default deallocation function is disallowed"

      return $ FunDef dealloc_entry fun

    -- Define the shared function.  This function takes all closures as
    -- parameters, and frees each.
    define_shared_fun shared_free_fun = do
      free_params <- replicateM (length group) $
                     newAnonymousVar (PrimType PointerType)
      fun_body <- execBuild $ do
        -- Free each closure
        zipWithM_ generateClosureFreeBody group (map VarV free_params)
        gen0 
      return $ FunDef shared_free_fun (primFun free_params [] fun_body)
  
-- | Generate code to release all captured variables in a closure and free
-- the closure.
generateClosureFreeBody :: Closure -> Val -> GenM ()
generateClosureFreeBody clo object = do
  -- Release references
  forM_ (map toDynamicField $ cloCapturedFields clo) $ \fld ->
    case fieldType fld
    of PrimField OwnedType ->
         decrefObject =<< loadFieldWithoutOwnership fld object
       _ -> return ()

  -- Deallocate
  deallocateHeapMem object
-}

-- | Emit the exact entry point of a function.
--
-- The entry point takes a closure pointer and the function's direct 
-- parameters.
emitExactEntry :: Closure -> CC ()
emitExactEntry clo = do
  clo_ptr <- newAnonymousVar (PrimType OwnedType)
  params <- mapM newAnonymousVar $ ftParamTypes $ closureType clo
  fun_body <- execBuild $ do
    -- Load each captured variable
    cap_vars <- load_captured_vars (VarV clo_ptr)
    -- Call the direct entry point
    let direct_entry = VarV $ closureDirectEntry clo
    return $ PrimCallA direct_entry (cap_vars ++ map VarV params)

  let fun = primFun (clo_ptr : params) (ftReturnTypes $ closureType clo) fun_body
  writeFun $ FunDef (closureExactEntry clo) fun
  where
    load_captured_vars clo_ptr
      | closureIsRecursive clo = do
          -- Captured variables are in the shared record
          shared_record <- loadField (toDynamicField $ recursiveClosureRecord !!: 1) clo_ptr
          captured_vars <-
            referenceField (toDynamicField $ closureSharedRecord clo !!: 0) clo_ptr
          load_captured_vars' captured_vars
      | closureIsLocal clo = do
          -- Captured variables are in the closure
          let field = localClosureRecord (closureCapturedRecord clo) !!: 1
          captured_vars <- referenceField (toDynamicField field) clo_ptr
          load_captured_vars' captured_vars
      | closureIsGlobal clo =
          -- Global closures don't capture variables
          return []

    -- Load all captured variables out of the record
    load_captured_vars' captured_ptr =
      sequence [loadField (toDynamicField fld) captured_ptr
               | fld <- recordFields $ closureCapturedRecord clo]


-- | Emit the inexact entry point of a function.
--
-- The inexact entry point takes the closure, a record holding function
-- parameters, and an unitialized record to hold function return values.
emitInexactEntry :: Closure -> CC ()
emitInexactEntry clo = do
  clo_ptr <- newAnonymousVar (PrimType OwnedType)
  params_ptr <- newAnonymousVar (PrimType PointerType)
  returns_ptr <- newAnonymousVar (PrimType PointerType)
  fun_body <- execBuild $ do
    -- Load each parameter value from the parameters record
    param_vals <- load_parameters (VarV params_ptr)

    -- Call the exact entry
    let exact_entry = VarV $ closureExactEntry clo
    return_vals <- emitAtom (ftReturnTypes $ closureType clo) $
                   PrimCallA exact_entry (VarV clo_ptr : param_vals)

    -- Store each return value
    store_parameters (VarV returns_ptr) return_vals
    gen0
  let fun = primFun [clo_ptr, params_ptr, returns_ptr] [] fun_body
  writeFun $ FunDef (closureInexactEntry clo) fun
  where
    load_parameters params_ptr =
      sequence [loadField (toDynamicField fld) params_ptr
               | fld <- recordFields param_record]    

    store_parameters returns_ptr return_vals =
      sequence [storeField (toDynamicField fld) returns_ptr val
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
emitInfoTable :: Closure -> CC ()
emitInfoTable clo =
  let arg_type_fields = replicate (length arg_type_tags) $
                        PrimField (IntType Unsigned S8)
      record_type =
        staticRecord (RecordField funInfoHeaderRecord : arg_type_fields)
      info_table = closureInfoTableEntry clo
  in writeData $
     DataDef info_table (flattenStaticRecord record_type) (flattenGlobalValues fun_info)
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
      map (uint8V . fromEnum . toTypeTag . promoteType . fromPrimType) $
      ftParamTypes $ closureType clo
      where
        fromPrimType (PrimType t) = t
        fromPrimType _ = internalError "emitInfoTable: Unexpected record type"
    

-- | Generate the code and data of a global function.  For closure functions,
-- an info table, a global closure, and entry points are generated.  For
-- primitive functions, only the global function is generated.
emitGlobalClosure :: Var -> Maybe Closure -> Fun -> CC ()

-- Emit a closure function
emitGlobalClosure direct_entry (Just clo) direct = do
  emitInfoTable clo
  writeFun $ FunDef (closureDirectEntry clo) direct
  emitExactEntry clo
  emitInexactEntry clo
  
  -- Global closures must not use a deallocation function
  when (isJust $ closureDeallocEntry clo) $
    internalError "emitGlobalClosure: Must not have deallocator"
  writeData =<< generateGlobalClosure clo

-- Emit a primitive function
emitGlobalClosure direct_entry Nothing direct = do
  writeFun $ FunDef direct_entry direct

-- | Generate the code and data of a group of recursive closures.
-- An info table and entry points are generated.  The code for dynamically
-- allocating closures is returned.
emitRecClosures :: ClosureGroup -> [Fun] -> CC (GenM ())
emitRecClosures grp directs = do
  -- Emit info table and entry points of each function 
  forM_ (zip grp directs) $ \(clo, direct) -> do 
    emitInfoTable clo
    writeFun $ FunDef (closureDirectEntry clo) direct
    emitExactEntry clo
    emitInexactEntry clo
    
  -- Emit the deallocation function.  
  -- All members of the group use the same one.
  let free_var = case closureDeallocEntry $ head grp
                 of Just v -> v
                    Nothing -> internalError "emitRecClosures"
  emitSharedClosureRecordFree free_var grp
  
  -- Return code for generating closures
  return $ generateRecursiveClosures grp

-- | Generate the code and data of a lambda function
emitLambdaClosure :: FunctionType -> Fun -> [Var] -> CC (GenM Val)
emitLambdaClosure lambda_type direct captured_vars = do
  fun_var <- newAnonymousVar (PrimType OwnedType)  

  -- Use the default deallocation function if there are no captured variables
  want_dealloc <-
    if null captured_vars
    then return DefaultDeallocator
    else do v <- newAnonymousVar (PrimType PointerType)
            return $ CustomDeallocator v

  entry_points <- mkEntryPoints want_dealloc lambda_type Nothing
  let clo = nonrecClosure fun_var entry_points captured_vars
      
  -- Generate code
  emitInfoTable clo
  writeFun $ FunDef (closureDirectEntry clo) direct
  emitExactEntry clo
  emitInexactEntry clo
  generateClosureFree clo
  
  -- Create the function variable, then pass it as a parameter to something 
  return $ do generateLocalClosure clo
              return $ VarV fun_var

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
    select Nothing = do
      op <- use_fun
      genIndirectCall return_types op args -- Unknown function
    
    select (Just ep) =
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
  return $ PrimCallA (VarV v) (captured_args ++ args')

-- | Produce an indirect call of the given operator
genIndirectCall :: [PrimType]
                -> GenM Val
                -> [GenM Val]
                -> CC (GenM Atom)

-- No arguments: Don't call
genIndirectCall return_types mk_op [] = return $ do
  op <- mk_op
  return $ ValA [op]

genIndirectCall return_types mk_op mk_args = return $ do
  op <- mk_op
  args <- sequence mk_args

  -- Get the function info table and captured variables
  inf_ptr <- loadField (toDynamicField $ objectHeaderRecord !!: 1) op

  -- Can make an exact call if the callee is a function and
  -- the number of arguments matches the function's arity
  inf_tag <- loadField (toDynamicField $ infoTableHeaderRecord !!: 1) inf_ptr
  inf_tag_test <- primCmpZ (PrimType (IntType Unsigned S8)) CmpEQ inf_tag $
                  uint8V $ fromEnum FunTag
  let check_arity = do
        arity <- loadField (funInfoHeaderRecord' !!: 1) inf_ptr
        eq <- primCmpZ (PrimType nativeWordType) CmpEQ arity $
          nativeWordV $ length args
        return $ ValA [eq]
  use_exact_call <-
    emitAtom1 (PrimType BoolType) =<<
    genIf inf_tag_test check_arity (return $ ValA [LitV $ BoolL False])

  -- If the arity matches, then perform an exact call.  Otherwise,
  -- perform an inexact call.
  genIf use_exact_call (exact_call op inf_ptr args) (inexact_call op args)
  where
    exact_call clo_ptr inf_ptr args = do
      -- Get the exact entry point
      fn <- loadField (funInfoHeaderRecord' !!: 3) inf_ptr

      -- Get the function's captured variables, then call the function
      return $ PrimCallA fn (clo_ptr : args)

    inexact_call clo_ptr args = do
      -- Create temporary storage for return values
      let ret_record = staticRecord $ map PrimField return_types
      ret_ptr <- allocateHeapMem $ nativeWordV $ recordSize ret_record

      -- Apply the function
      genApply clo_ptr args ret_ptr

      -- Extract return values, stealing references
      ret_vals <- mapM (load_ret_value ret_ptr) $
                  map toDynamicField $ recordFields ret_record

      -- Free temporary storage
      deallocateHeapMem ret_ptr
      return $ ValA ret_vals

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
      emitAtom1 (PrimType OwnedType) $ PrimCallA f (clo : args)

    -- Apply arguments and write result in to the return struct
    finish_apply f clo args =
      emitAtom0 $ PrimCallA f (clo : args ++ [ret_ptr])

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
