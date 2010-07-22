{-| Reference count insertion.

This pass inserts explicit reference counting around owned variables.
Each function is traversed forward to determine which variables the
current function holds a reference to (owned) and which it references but
does not hold a reference to (borrowed).  Then the function is traversed
backward to determine how to adjust references.  The
following operations on owned variables require reference count adjustment.

* Owned variables are passed to functions as borrowed parameters; their
reference counts are not adjusted, but the callee may need to adjust them.

* When an owned variable is stored, its reference count goes up by 1.  The
store is assumed not to overwrite an existing variable (so we don't need
to change some other reference count).

* When an owned variable is loaded, its reference count goes up by 1.

* When an owned variable is discarded, its reference count goes down by 1
(but if it was a borrowed parameter, it doesn't change).

* When an owned variable is returned, its reference count does not change
(but if it was a borrowed parameter, it goes up by 1).

* Casting to an owned variable produces a new reference (the same as if 
a new reference were returned from a function).

* Casting from an owned variable consumes a reference.  (This is the only  
instance of a parameter not being a borrowed reference).

A use of a pointer derived by performing arithmetic on an owned variable
constitutes a use of the owned variable.  This is becase when we load from
or store to a field of an object, the object must remain live.  Derived
pointers must only be 
used within the block in which they appear, otherwise some uses may be 
missed.  To ensure that this is the case, code motion isn't performed  
between the time low-level code is generated and the time reference counting
is inserted.
-}

{-# LANGUAGE ScopedTypeVariables, FlexibleInstances #-}
module Pyon.LowLevel.ReferenceCounting(insertReferenceCounting)
where

import Control.Monad
import qualified Data.Map as Map
import Data.Maybe
import Debug.Trace

import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.MonadLogic
import Gluon.Common.Supply
import Pyon.LowLevel.FreshVar
import Pyon.LowLevel.Syntax
import Pyon.LowLevel.Types
import Pyon.LowLevel.Record
import Pyon.LowLevel.Build
import Pyon.LowLevel.Print
import Pyon.Globals

type GenM a = Gen FreshVarM a

-- | The ownership of a variable at the time it was introduced.
--
-- An 'Owned' reference starts out as one owned reference that must be 
-- relinquished.
-- A 'Borrowed' reference starts out as a non-owned reference.  Some other
-- piece of code is guaranteed to hold a reference for the duration of the  
-- current function body.
-- A 'Loaded' reference starts out as a non-owned reference.  It must have
-- its reference count incremented immediately.
data Ownership =
    Owned                       -- ^ Introduced as an owned reference
  | Borrowed                    -- ^ Introduced as a borrowed reference
  | Loaded                      -- ^ Loaded from memory
  deriving(Eq)

-- | The set of references held at a program point.
type HeldReferences = Map.Map Var Ownership

getOwnership :: Var -> HeldReferences -> Ownership
getOwnership v m 
  | varIsBuiltin v = Borrowed   -- Builtins are always borrowed references
  | otherwise = case Map.lookup v m
                   of Just o -> o
                      Nothing -> internalError "isOwned"

-- | Reference deficits of \"owned\" variables.  Deficits are computed while
-- traversing code in the backwards direction.  A variable's reference count
-- will be increased to make up the deficit where the variable is bound.
type Deficit = Map.Map Var Int

getDeficit :: Var -> Deficit -> Int
getDeficit v m = fromMaybe 0 $ Map.lookup v m

-- | Remove the variable's deficit from the map.  Return the deficit and
-- restricted map.
extractDeficit :: Var -> Deficit -> (Int, Deficit)
extractDeficit v m = (getDeficit v m, Map.delete v m)

addDeficit :: Deficit -> Deficit -> Deficit
addDeficit = Map.unionWith (+)

maxDeficit :: Deficit -> Deficit -> Deficit
maxDeficit = Map.unionWith max

minusDeficit :: Deficit -> Deficit -> Deficit
x `minusDeficit` y = addDeficit x $ fmap negate y

isBalanced :: Deficit -> Bool
isBalanced deficit = all (0 ==) $ Map.elems deficit

-- | A map associating a pointer variable to the variable it was derived from.
-- Pointers are \"derived\" with pointer arithmetic.
type SourcePointer = Map.Map Var Var

newtype RC a =
  RC {runRC :: HeldReferences -> SourcePointer -> FreshVarM (a, Deficit)}

instance Monad RC where
  return x = RC $ \_ _ -> return (x, Map.empty)
  m >>= k = RC $ \ownership sources -> do
    (x, d1) <- runRC m ownership sources
    (y, d2) <- runRC (k x) ownership sources
    return (y, addDeficit d1 d2)

instance Supplies RC (Ident Var) where
  fresh = RC $ \_ _ -> do x <- fresh
                          return (x, Map.empty)

-- | Add an owned variable to the environment and increase its reference
-- count if required by the code block
withOwnedVariable :: ParamVar -> RC (GenM a) -> RC (GenM a)
withOwnedVariable = withVariable Owned

withOwnedVariables vs m = foldr withOwnedVariable m vs

-- | Add a borrowed variable to the environment and increase its reference
-- count if required by the code block
withBorrowedVariable :: ParamVar -> RC (GenM a) -> RC (GenM a)
withBorrowedVariable = withVariable Borrowed

withBorrowedVariables vs m = foldr withBorrowedVariable m vs

withLoadedVariable :: ParamVar -> RC (GenM a) -> RC (GenM a)
withLoadedVariable = withVariable Loaded

withVariable is_owned v m
  | not (isOwnedVar v) = m -- This variable is not reference counted
  | otherwise = RC $ \ownership src -> do
      -- Add the variable to the table and process the rest of the block
      (blk, deficit) <- runRC m (Map.insert v is_owned ownership) src
  
      -- Correct for the variable's reference deficit
      let (this_deficit, deficit') = extractDeficit v deficit
          delta = case is_owned
                  of Owned -> this_deficit - 1 -- One reference is provided
                     Borrowed -> this_deficit
                     Loaded -> this_deficit
          blk' = increfHeaderBy delta (VarV $ toPointerVar v) >> blk
  
      -- Return the new code.  Stop tracking this variable's deficit.
      return (blk', deficit')

-- | Generate reference count increments to balance out the reference deficits
-- of all global variables.
-- The code generated is the same as for a borrowed variable.
adjustBuiltinVarRefCounts :: RC (GenM a) -> RC (GenM a)
adjustBuiltinVarRefCounts m = RC $ \ownership src -> do
  -- Process the rest of the block
  (blk, deficit) <- runRC m ownership src
  
  -- Correct for each builtin variable's reference count
  let (bi_deficit, other_deficit) =
        Map.partitionWithKey (\k _ -> varIsBuiltin k) deficit
      bi_deficits = Map.toList bi_deficit
      blk' = foldr adjust_references blk bi_deficits

  return (blk', other_deficit)
  where
    adjust_references (v, deficit) blk =
      increfHeaderBy deficit (VarV $ toPointerVar v) >> blk

-- | Consume a reference to a variable.  If it's an owned variable or
-- derived from an owned variable, the variable's reference deficit goes
-- up by 1.  Otherwise, nothing happens.
consumeReference :: Var -> RC ()
consumeReference v
  | isOwnedVar v = RC $ \_ _ -> return ((), Map.singleton v 1)
  | otherwise = do v' <- lookupSourceVar v
                   maybe (return ()) consumeReference v'

-- | Borrow a reference to a variable while generating some code.  Ensure
-- that a reference is held, possibly by inserting a 'decref' to ensure 
-- a reference deficit.  If it's a borrowed variable, we're guaranteed that
-- a reference is held so we don't need to do anything.
borrowReferences :: [Var]
                 -> RC (GenM ())
                 -> RC (GenM b)
                 -> RC (GenM b)
borrowReferences vs borrower rest = RC $ \ownership src -> do
  (m, d1) <- runRC borrower ownership src
  (k, d2) <- runRC rest ownership src
  let (k', d2') = foldr (fix_reference_counts ownership d1) (k, d2) vs
  return (m >> k', d1 `addDeficit` d2')
  where
    -- If the variable is borrowed or the continuation consumes a reference,
    -- there is no need to adjust the reference count.
    -- If the variable is not borrowed, ensure that at least one reference 
    -- is held, by inserting a "decref" if necessary.
    fix_reference_counts ownership d1 v (k, d2)
      | getOwnership v ownership /= Borrowed && getDeficit v d2 == 0 =
          (decrefHeader (VarV $ toPointerVar v) >> k,
           d2 `addDeficit` Map.singleton v 1)
      | otherwise =
          (k, d2)

-- | Ensure that the pieces of code have the same reference deficits at the end
-- by adjusting reference counts in each piece of code.
parallelReferences :: [RC (GenM a)] -> RC [GenM a]
parallelReferences xs = RC $ \ownership src -> do
  -- Run each path
  ys <- sequence [runRC x ownership src | x <- xs]
  
  -- Get the maximum reference deficit for each variable
  let shared_deficit = foldr maxDeficit Map.empty $ map snd ys
  return (map (reconcile_deficit shared_deficit) ys, shared_deficit)
  where
    reconcile_deficit shared_deficit (gen_code, local_deficit) = do
      let extra_deficit = shared_deficit `minusDeficit` local_deficit
          
      -- Modify reference counts
      forM (Map.assocs extra_deficit) $ \(v, n) -> decrefHeaderBy n (VarV $ toPointerVar v)
      
      -- Generate the rest of the code
      gen_code

-- | Find the owned variable corresponding to a variable (if there is one).
lookupSourceVar :: Var -> RC (Maybe Var)
lookupSourceVar v = RC $ \_ src -> return (Map.lookup v src, Map.empty)

withDerivedVar :: Var -> Var -> RC a -> RC a 
withDerivedVar derived_var src_var (RC m) =
  RC $ \ownership src ->
  let src' = Map.insert derived_var src_var src
  in m ownership src'

runBalancedRC :: RC a -> FreshVarM a
runBalancedRC m = do
  (x, deficit) <- runRC m Map.empty Map.empty
  unless (isBalanced deficit) $
    traceShow deficit $
    internalError "runBalancedRC: Found unbalanced reference counts"
  return x

-------------------------------------------------------------------------------

toPointerPrimType :: PrimType -> PrimType
toPointerPrimType OwnedType = PointerType
toPointerPrimType t = t

toPointerType :: ValueType -> ValueType
toPointerType (PrimType pt) = PrimType $ toPointerPrimType pt
toPointerType t = t

-- | Convert all owned pointers to non-owned pointers in the record type
toPointerRecordType :: StaticRecord -> StaticRecord
toPointerRecordType rec =
  staticRecord $ map change_field $ map fieldType $ recordFields rec
  where
    change_field (PrimField t) = PrimField $ toPointerPrimType t
    change_field f = f

isOwnedVar :: Var -> Bool
isOwnedVar v =
  case varType v
  of PrimType OwnedType -> True
     _ -> False

-- | Convert owned variables to pointer variables.  Leave other variables
-- unchanged.
toPointerVar :: Var -> Var
toPointerVar v =
  case varType v
  of PrimType t -> v {varType = PrimType $ toPointerPrimType t}
     _ -> internalError "toPointerVar"

-- | Convert a primitive operating on owned pointer variables to the equivalent
-- one operating on pointer variables.  If the primitive doesn't operate on 
-- owned pointers, leave it unchanged.
toPointerPrim :: Prim -> Prim
toPointerPrim prim =
  case prim
  of PrimLoad (PrimType OwnedType) -> PrimLoad (PrimType PointerType)
     PrimStore (PrimType OwnedType) -> PrimStore (PrimType PointerType)
     PrimCastToOwned -> internalError "toPointerPrim"
     PrimCastFromOwned -> internalError "toPointerPrim"
     _ -> prim

-- | Convert global data from owned to non-owned pointers.
-- Because global data can't contain lambda expressions and can't
-- release their references, only types have to change.
toPointerData :: Val -> Val
toPointerData value =
  case value
  of VarV v -> VarV (toPointerVar v)
     LitV _ -> value
     _ -> internalError "toPointerData"

-- | Perform reference count adjustment on a function.
rcFun :: [Var] -> Fun -> FreshVarM Fun
rcFun globals fun = do
  unless (isPrimFun fun) $ internalError "rcFun"
  body' <- runBalancedRC $
           adjustBuiltinVarRefCounts $
           withBorrowedVariables globals $
           withBorrowedVariables (funParams fun) $
           rcBlock (funReturnTypes fun) (funBody fun)
  body'' <- execBuild body'
  let params  = map toPointerVar $ funParams fun
      returns = map toPointerType $ funReturnTypes fun
  return $ primFun params returns body''

rcBlock :: [ValueType] -> Block -> RC (GenM Atom)
rcBlock return_types (Block stms atom) = foldr rcStm gen_atom stms
  where
    gen_atom =
      case atom
      of ValA vals -> do
           -- No reference borrowing; just return the values
           vals' <- mapM (rcVal False) vals
           return $ ValA `liftM` sequence vals'
         _ -> do
           -- Create a place to adjust reference counts after the last atom.
           -- Assign the last atom's result to temporary variables, then 
           -- return them.
           retvars <- mapM newAnonymousVar (map toPointerType return_types)
           rcAtom return_types (bindAtom retvars) atom $
             return $ return $ ValA $ map (VarV . toPointerVar) retvars

rcStm :: Stm -> RC (GenM a) -> RC (GenM a)
rcStm statement k =
  case statement
  of -- A load must be followed by an incref to ensure that the object is not
     -- subsequently freed.  Identifying the variable as 'Loaded' ensures this 
     -- will happen.
     LetE [param] (PrimA (PrimLoad (PrimType OwnedType)) [arg]) ->
       borrowValues [arg] (generate_load param arg) $
       withLoadedVariable param k

     -- Pointer arithmetic creates a derived pointer, in addition to behaving
     -- like a normal arithmetic instruction.
     LetE params@[param] atom@(PrimA PrimAddP [VarV base, offset]) ->
       if isOwnedVar base
       then refcount_let params atom $ withDerivedVar param base k
       else do msrc <- lookupSourceVar base
               case msrc of
                 Nothing -> refcount_let params atom k
                 Just v  -> refcount_let params atom $ withDerivedVar param v k
         
     LetE params atom -> refcount_let params atom k

     LetrecE {} -> internalError "rcStm"
   where
     refcount_let params atom k =
       rcAtom (map varType params) (bindAtom $ map toPointerVar params) atom $
       withOwnedVariables params k
     
     generate_load param arg = do
       arg' <- rcVal True arg
       return $ do arg'' <- arg'
                   bindAtom1 (toPointerVar param) $
                     PrimA (PrimLoad (PrimType PointerType)) [arg'']


-- | Insert reference counting in an atom and emit a statement.
-- Use the continuation to decide whether to adjust reference counts.
rcAtom :: forall a.
          [ValueType]
       -> (Atom -> GenM ())
       -> Atom
       -> RC (GenM a)
       -> RC (GenM a)
rcAtom return_types emit_atom atom k =
  case atom
  of ValA vals -> do
       vals' <- mapM (rcVal False) vals
       return_atom $ ValA `liftM` sequence vals'

     PrimCallA op args ->
       borrow (op : args) $ do
         op' <- rcVal True op
         args' <- mapM (rcVal True) args
         return $ PrimCallA `liftM` op' `ap` sequence args'

     PrimA PrimCastFromOwned [arg] -> do
       -- Simply assign the parameter to the destination, consuming a
       -- reference.
       arg' <- rcVal False arg
       return_atom $ ValA `liftM` sequence [arg']

     PrimA PrimCastToOwned [arg] -> do
       -- Assign the parameter to the destination.
       arg' <- rcVal False arg
       return_atom $ ValA `liftM` sequence [arg']

     PrimA prim args ->
       borrow args $ do
         adjust_references <- adjustReferencesForPrim prim args
         args' <- mapM (rcVal True) args
         return $ do adjust_references
                     PrimA (toPointerPrim prim) `liftM` sequence args'

     SwitchA val cases -> do
       -- Scrutinee can never be a borrowed value
       val' <- rcVal False val 
       cases' <- parallelReferences $ map rc_alt cases
       return_atom $ SwitchA `liftM` val' `ap` sequence cases'
  where
    rc_alt (lit, block) = do
      block' <- rcBlock return_types block
      return $ do block'' <- getBlock block'
                  return (lit, block'')

    borrow :: [Val] -> RC (GenM Atom) -> RC (GenM a)
    borrow vals m =
      let m' = do x <- m
                  return (x >>= emit_atom)
      in borrowValues vals m' k
    
    return_atom :: GenM Atom -> RC (GenM a)
    return_atom mk_atom = do
      x <- k
      return ((mk_atom >>= emit_atom) >> x)

-- | Generate code to adjust reference counts to reflect what a primitive
--   operation does to its arguments.  The code is emitted immediately after
--   the primitive operation.
adjustReferencesForPrim :: Prim -> [Val] -> RC (GenM ())

-- Storing a value consumes a reference
adjustReferencesForPrim (PrimStore (PrimType OwnedType)) [_, value_arg] =
  case value_arg
  of VarV v -> do consumeReference v
                  return (return ())
     _ -> internalError "adjustReferenceForPrim: Unexpected argument to store"
    
-- Casting from an owned reference consumes a reference
adjustReferencesForPrim (PrimCastFromOwned) [value_arg] =
  case value_arg
  of VarV v -> do consumeReference v
                  return (return ())
     _ -> internalError "recAtom: Cast of a non-variable pointer value"

adjustReferencesForPrim (PrimLoad (PrimType OwnedType)) _ =
  -- Should have been handled in 'rcStm'
  internalError "recAtom: Unhandled pointer load"

-- Other primitives have the default behavior
adjustReferencesForPrim _ _ = return $ return ()

-- | Borrow references to any variables mentioned in the list
borrowValues :: [Val] -> RC (GenM ()) -> RC (GenM b) -> RC (GenM b)
borrowValues vals m k = do
  owned_vars <- mapM get_owned_var vals
  borrowReferences (catMaybes owned_vars) m k
  where
    -- If the value is an owned variable, return it
    -- If the value is derived from an owned variable, return the source var
    get_owned_var (VarV v)
      | isOwnedVar v = return $ Just v
      | otherwise = lookupSourceVar v
    get_owned_var _ = return Nothing

rcVal :: Bool -> Val -> RC (GenM Val)
rcVal is_borrowed value =
  case value
  of VarV v -> do
       -- Consume this reference if it's not being borrowed
       unless is_borrowed $ consumeReference v
       return $ return $ VarV $ toPointerVar v
     LitV l ->
       return $ return value
     _ -> internalError "rcVal"

-- | Insert explicit reference counting in a module.  All owned references
--   are converted to ordinary pointers with reference counting.
insertReferenceCounting :: Module -> IO Module
insertReferenceCounting (Module funs datas) = do
  withTheLLVarIdentSupply $ \id_supply ->
    runFreshVarM id_supply $ do
      -- Insert reference counting into functions
      funs' <- mapM rc_fun funs
      -- Convert owned pointers to ordinary pointers in static data 
      let datas' = map rc_data datas
      return $ Module funs' datas'
  where
    global_vars = [v | FunDef v _ <- funs] ++ [v | DataDef v _ _ <- datas]

    rc_fun (FunDef v f) = do
      f' <- rcFun global_vars f
      return $ FunDef v f'

    rc_data (DataDef v record_type x) =
      DataDef (toPointerVar v) (toPointerRecordType record_type) (map toPointerData x)
