{-| Generation of code and data structures for closure conversion.
-}
{-# LANGUAGE FlexibleInstances, RecursiveDo, ViewPatterns #-}
module LowLevel.ClosureCode
       (varPrimType, valType,
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
valType :: Val -> PrimType
valType (VarV v) = varPrimType v
valType (RecV {}) = internalError "valType"
valType (LitV l) = litType l
valType (LamV f) = OwnedType

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
  returnCC $ fmap cloEntryPoints $ IntMap.lookup (fromIdent $ varID v) $ envEntryPoints env

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
      let k = fromIdent $ varID $ cloVariable clo
      in env {envEntryPoints = IntMap.insert k clo $ envEntryPoints env}

withGlobalFunctions :: [FunDef] -> CC [Fun] -> CC () -> CC ()
withGlobalFunctions defs scan gen = do
  clos <- mapM mkGlobalClosure defs
  funs <- localClosures clos scan
  zipWithM emitGlobalClosure clos funs
  gen

-- | Create a closure description.  No code is generated.
mkGlobalClosure (FunDef v fun) = do
  entry_points <- mkEntryPoints CannotDeallocate (funType fun) (varName v)
  return $ nonrecClosure v entry_points []

withLocalFunctions :: [FunDef]          -- ^ Function definitions
                   -> CC [(Fun, [Var])] -- ^ Generate a direct entry
                                        -- and list of captured
                                        -- variables for each function
                   -> (GenM () -> CC a) -- ^ Incorporate the closure code
                                        -- generator into the program
                   -> CC a
withLocalFunctions defs scan gen = mdo
  -- Create recursive function closures
  clos <- mkRecClosures defs captureds
  
  -- Scan functions
  (unzip -> ~(funs, captureds)) <- localClosures clos scan

  -- Generate closure code
  gen_code <- emitRecClosures clos funs
  
  -- Generate remaining code
  localClosures clos $ gen gen_code

-- | Create closure descriptions for a set of recursive functions.
-- No code is generated.
mkRecClosures defs captureds = do
  -- Create entry points structure
  entry_points <- forM defs $ \(FunDef v f) ->
    mkEntryPoints CustomDeallocator (funType f) (varName v)
 
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

objectHeaderLength = length objectHeader
closureHeaderRecord' = toDynamicRecord closureHeaderRecord
funInfoHeaderRecord' = toDynamicRecord funInfoHeaderRecord

-- | Create a record whoe fields have the same type as the given values.
valuesRecord :: [Val] -> StaticRecord
valuesRecord vals = staticRecord $ map (PrimField . valType) vals

-- | A description of a function closure.  The description is used to create
--   all the code and static data for the function other than the direct entry
--   point.
data Closure =
  Closure
  { -- | The variable that will point to this closure
    cloVariable :: !Var
    -- | The entry points for the function that this closure defines
  , cloEntryPoints :: EntryPoints
    -- | Variables captured by the closure
  , cloCaptured :: [Var]
    -- | The closure's record type
  , cloRecord :: StaticRecord
    -- | The contents of the closure's info table
  , cloInfoTable :: [Val]
    -- | If the closure is part of a recursively defined group,
    --   these are the closures in the group.  All closures in the group  
    --   have the same group.  A closure is part of its own group.
  , cloGroup    :: Maybe ClosureGroup
  }

cloType c = entryPointsType $ cloEntryPoints c

cloIsRecursive c = isJust (cloGroup c)

cloCapturedFields :: Closure -> [StaticField]
cloCapturedFields clo =
  take (length $ cloCaptured clo) $ drop objectHeaderLength $
  recordFields $ cloRecord clo
  
cloRecursiveFields :: Closure -> [StaticField]
cloRecursiveFields clo =
  drop (length (cloCaptured clo) + objectHeaderLength) $
  recordFields $ cloRecord clo

type ClosureGroup = [Closure]

closure :: Var -> EntryPoints -> [Var] -> Maybe ClosureGroup -> Closure
closure var entry captured recursive =
  Closure { cloVariable    = var
          , cloEntryPoints = entry
          , cloCaptured    = captured
          , cloRecord      = record
          , cloInfoTable   = info
          , cloGroup       = recursive
          }
  where
    -- Closure contains captured variables 
    record = staticRecord $
             closureHeader ++
             map (PrimField . varPrimType) captured ++
             replicate (maybe 0 length recursive) (PrimField PointerType)
    
    -- see 'funInfoHeader'
    info = [ maybe (LitV NullL) VarV $ deallocEntry entry
           , uint8V $ fromEnum FunTag
           , uint16V $ functionArity entry
           , uint16V $ length captured
           , uint16V $ maybe 0 length recursive
           , VarV $ exactEntry entry
           , VarV $ inexactEntry entry] ++
           arg_type_tags ++ cap_type_tags

    arg_types = map valueToPrimType $ ftParamTypes $ entryPointsType entry
    arg_type_tags = map (uint8V . fromEnum . toTypeTag) arg_types
    
    cap_types = map varPrimType captured
    cap_type_tags = map (uint8V . fromEnum . toTypeTag) cap_types

nonrecClosure :: Var -> EntryPoints -> [Var] -> Closure
nonrecClosure v e cap = closure v e cap Nothing

closureGroup :: [(Var, EntryPoints, [Var])] -> ClosureGroup
closureGroup xs = group
  where
    group = [closure v e cap (Just group) | (v, e, cap) <- xs] 

-- | Allocate, but do not initialize, a closure.
-- The created closure is returned.
allocateClosure :: Closure -> GenM Val
allocateClosure clo =
  allocateHeapMem $ nativeWordV $ recordSize $ cloRecord clo

-- | Initialize a closure.
--
-- The first argument is a list of un-owned pointers to other closures in
-- the recursive group.  This list is ignored for non-recursive function 
-- definitions.
--
-- The initialized closure is assigned to the variable given in
-- the 'cloVariable' field.
initializeClosure group_ptrs clo clo_ptr = do
  initializeObject clo_ptr (VarV $ infoTableEntry $ cloEntryPoints clo)
  zipWithM_ init_captured captured_fields (map VarV $ cloCaptured clo)
  when (cloIsRecursive clo) $ zipWithM_ init_rec group_fields group_ptrs
  -- Cast to an owned pointer
  bindAtom1 (cloVariable clo) $ PrimA PrimCastToOwned [clo_ptr]

  where
    captured_fields = map toDynamicField $ cloCapturedFields clo
    group_fields = map toDynamicField $ cloRecursiveFields clo
    
    -- Write a captured variable
    init_captured fld val = storeField fld clo_ptr val
    
    -- Write a pointer to another closure in the group.  The pointer is
    -- not owned.
    init_rec fld other_clo = storeField fld clo_ptr other_clo

-- | Create a statically defined closure object for a global function.
generateGlobalClosure :: Closure -> CC ()
generateGlobalClosure clo
  | not $ null $ cloCaptured clo =
      internalError "generateGlobalClosure: Global function captures variables"
  | cloIsRecursive clo =
      -- Global functions can refer directly to their global names
      internalError "generateGlobalClosure: Global function is recursively defined"
  | otherwise =
      let closure_values =
            objectHeaderData $ VarV $ infoTableEntry $ cloEntryPoints clo
      in writeData $
         DataDef (cloVariable clo) closureHeaderRecord closure_values

-- | Create a single closure.
generateClosure :: Closure -> GenM () 
generateClosure clo
  | cloIsRecursive clo =
      internalError "generateClosure: Closure is part of a recursive group"
  | otherwise = do
      ptr <- allocateClosure clo
      (initializeClosure invalid) clo ptr
  where
    invalid = internalError "generateClosure: Not recursive"
                            
-- | Create a group of closures.
generateClosures :: ClosureGroup -> GenM () 
generateClosures clos = do
  ptrs <- mapM allocateClosure clos
  zipWithM_ (initializeClosure ptrs) clos ptrs

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
    dealloc_entry /= llBuiltin the_prim_dealloc_global_closure = do
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
            of Just v | v /= llBuiltin the_prim_dealloc_global_closure -> v 
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

generateExactEntry :: Closure -> CC ()
generateExactEntry clo = do
  -- The entry point takes the closure + direct parameters
  clo_ptr <- newAnonymousVar (PrimType OwnedType)
  params <- mapM newAnonymousVar $ ftParamTypes $ cloType clo
  fun_body <- execBuild $ do
    -- Load each captured variable
    cap_vars <- sequence [loadField fld (VarV clo_ptr)
                         | fld <- map toDynamicField $ cloCapturedFields clo]
    -- Call the direct entry point
    let direct_entry = VarV $ directEntry $ cloEntryPoints clo
    return $ PrimCallA direct_entry (cap_vars ++ map VarV params)
  let fun = primFun (clo_ptr : params) (ftReturnTypes $ cloType clo) fun_body
  writeFun $ FunDef (exactEntry $ cloEntryPoints clo) fun

generateInexactEntry :: Closure -> CC ()
generateInexactEntry clo = do                        
  -- The entry point takes the closure + parameters record + returns record
  clo_ptr <- newAnonymousVar (PrimType OwnedType)
  params_ptr <- newAnonymousVar (PrimType PointerType)
  returns_ptr <- newAnonymousVar (PrimType PointerType)
  fun_body <- execBuild $ do
    -- Load each parameter value
    param_vals <- sequence [loadField fld (VarV params_ptr)
                           | fld <- map toDynamicField $ recordFields param_record]
    -- Call the exact entry
    let exact_entry = VarV $ exactEntry $ cloEntryPoints clo
    return_vals <- emitAtom (ftReturnTypes $ cloType clo) $
                   PrimCallA exact_entry (VarV clo_ptr : param_vals)

    -- Store each return value
    zipWithM_ (store_field (VarV returns_ptr))
      (map toDynamicField $ recordFields return_record)
      return_vals
    gen0
  let fun = primFun [clo_ptr, params_ptr, returns_ptr] [] fun_body
  writeFun $ FunDef (inexactEntry $ cloEntryPoints clo) fun
  where
    store_field ptr fld return_val = storeField fld ptr return_val
    -- Record type of parameters
    param_record = staticRecord $ map (PrimField . valueToPrimType) $
                   ftParamTypes $ cloType clo
  
    -- Record type of returns
    return_record = staticRecord $ map (PrimField . valueToPrimType) $
                    ftReturnTypes $ cloType clo

generateInfoTable :: Closure -> CC ()
generateInfoTable clo =
  let record = valuesRecord $ cloInfoTable clo
      info_table = infoTableEntry $ cloEntryPoints clo
  in writeData $ DataDef info_table record $ cloInfoTable clo

-- | Generate the code and data of a global function
emitGlobalClosure :: Closure -> Fun -> CC ()
emitGlobalClosure clo direct = do
  generateInfoTable clo
  writeFun $ FunDef (directEntry $ cloEntryPoints clo) direct
  generateExactEntry clo
  generateInexactEntry clo
  
  -- Global closures must not use a deallocation function
  when (isJust $ deallocEntry (cloEntryPoints clo)) $
    internalError "constructGlobalClosure: Must use default deallocator"
  generateGlobalClosure clo

-- | Generate the code and data of a group of recursive closures
emitRecClosures :: ClosureGroup -> [Fun] -> CC (GenM ())
emitRecClosures grp directs = do
  forM_ (zip grp directs) $ \(clo, direct) -> do 
    generateInfoTable clo
    writeFun $ FunDef (directEntry $ cloEntryPoints clo) direct
    generateExactEntry clo
    generateInexactEntry clo
  generateClosureGroupFree grp
  return $ generateClosures grp

-- | Generate the code and data of a lambda function
emitLambdaClosure :: FunctionType -> Fun -> [Var] -> CC (GenM Val)
emitLambdaClosure lambda_type direct captured_vars = do
  fun_var <- newAnonymousVar (PrimType OwnedType)  
  
  -- Use the default deallocation function if there are no captured variables
  let want_dealloc = if null captured_vars
                     then DefaultDeallocator
                     else CustomDeallocator
  entry_points <- mkEntryPoints want_dealloc lambda_type Nothing
  let clo = nonrecClosure fun_var entry_points captured_vars
      
  -- Generate code
  generateInfoTable clo
  writeFun $ FunDef (directEntry $ cloEntryPoints clo) direct
  generateExactEntry clo
  generateInexactEntry clo
  generateClosureFree clo
  
  -- Create the function variable, then pass it as a parameter to something 
  return $ do generateClosure clo
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
        arity = functionArity $ cloEntryPoints ep
        entry = directEntry $ cloEntryPoints ep
        captured_vars = cloCaptured ep

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
  inf_ptr <- loadField (closureHeaderRecord' !!: 1) op

  -- Check if the number of arguments matches the function's arity
  arity <- loadField (funInfoHeaderRecord' !!: 2) inf_ptr
  arity_test <- primCmpZ (PrimType nativeWordType) CmpEQ arity $ nativeWordV $ length args
  
  -- If the arity matches, then perform an exact call.  Otherwise,
  -- perform an inexact call.
  genIf arity_test (exact_call op inf_ptr args) (inexact_call op args)
  where
    exact_call clo_ptr inf_ptr args = do
      -- Get the direct entry point
      fn <- loadField (funInfoHeaderRecord' !!: 5) inf_ptr
        
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
genApply closure args ret_ptr =
  gen_apply closure args (map (promotedTypeTag . valType) args)
  where
    gen_apply closure args arg_types =
      -- If all arguments are consumed, then call apply_mem
      -- Otherwise, call apply_ret
      if null args'
      then do finish_apply (VarV apply_mem) closure app_args
      else do closure' <- partial_apply (VarV apply_ret) closure app_args
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
applyFunctions = [(Int32Tag, i_node), (Float32Tag, f_node)]
  where
    i_node = ApplyTrieNode (llBuiltin the_prim_apply_i32_f) (llBuiltin the_prim_apply_i32)[]
    f_node = ApplyTrieNode (llBuiltin the_prim_apply_f32_f) (llBuiltin the_prim_apply_f32)[]
