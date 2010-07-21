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
import Pyon.LowLevel.Syntax
import Pyon.LowLevel.Types
import Pyon.LowLevel.Record
import Pyon.LowLevel.Build
import Pyon.LowLevel.Print
import Pyon.Globals

type GenM a = Gen FreshVarM a

-- | Ownership of \"owned\" variables.  Variables labeled 'True' are owned;
-- variables labeled 'False' are borrowed.
type Ownership = Map.Map Var Bool

isOwned :: Var -> Ownership -> Bool
isOwned v m = case Map.lookup v m
              of Just b -> b
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

newtype RC a = RC {runRC :: Ownership -> FreshVarM (a, Deficit)}

instance Monad RC where
  return x = RC $ \_ -> return (x, Map.empty)
  m >>= k = RC $ \ownership -> do
    (x, d1) <- runRC m ownership
    (y, d2) <- runRC (k x) ownership
    return (y, addDeficit d1 d2)

instance Supplies RC (Ident Var) where
  fresh = RC $ \_ -> do x <- fresh
                        return (x, Map.empty)

-- | Add an owned variable to the environment and increase its reference
-- count if required by the code block
withOwnedVariable :: ParamVar -> RC (GenM a) -> RC (GenM a)
withOwnedVariable = withVariable True

withOwnedVariables vs m = foldr withOwnedVariable m vs

-- | Add a borrowed variable to the environment and increase its reference
-- count if required by the code block
withBorrowedVariable :: ParamVar -> RC (GenM a) -> RC (GenM a)
withBorrowedVariable = withVariable False

withBorrowedVariables vs m = foldr withBorrowedVariable m vs


withVariable is_owned v m
  | not (isOwnedVar v) = trace ("withVariable " ++ show v) $ m      -- This variable is not reference counted
  | otherwise = RC $ \ownership -> do
      -- Add the variable to the table and process the rest of the block
      (blk, deficit) <- runRC m $ Map.insert v is_owned ownership
  
      -- Correct for the variable's reference deficit
      let (this_deficit, deficit') = extractDeficit v deficit
          delta = if is_owned then this_deficit - 1 else this_deficit
          blk' = increfHeaderBy delta (VarV $ toPointerVar v) >> blk
  
      -- Return the new code.  Stop tracking this variable's deficit.
      return (blk', deficit')

-- | Consume a reference to a variable.  The variable's reference deficit
-- goes up by 1.
consumeReference :: Var -> RC ()
consumeReference v = RC $ \_ -> return ((), Map.singleton v 1)

-- | Borrow a reference to a variable while generating some code.  Ensure
-- that a reference is held, possibly by inserting a 'decref' to ensure 
-- a reference deficit.  If it's a borrowed variable, we're guaranteed that
-- a reference is held so we don't need to do anything.
borrowReferences :: [Var]
                 -> RC (GenM ())
                 -> RC (GenM b)
                 -> RC (GenM b)
borrowReferences vs borrower rest = RC $ \ownership -> do
  (m, d1) <- runRC borrower ownership
  (k, d2) <- runRC rest ownership
  let (k', d2') = foldr (fix_reference_counts ownership d1) (k, d2) vs
  return (m >> k', d1 `addDeficit` d2')
  where
    -- The object may be freed to early if the variable is owned and there's no
    -- reference deficit in the continuation.  If, on the other hand, the 
    -- variable is borrowed, or the continuation consumes a reference, we're
    -- safe.
    fix_reference_counts ownership d1 v (k, d2)
      | isOwned v ownership && getDeficit v d2 == 0 =
          (decrefHeader (VarV $ toPointerVar v) >> k,
           d2 `addDeficit` Map.singleton v 1)
      | otherwise =
          (k, d2)

-- | Ensure that the pieces of code have the same reference deficits at the end
-- by adjusting reference counts in each piece of code.
parallelReferences :: [RC (GenM a)] -> RC [GenM a]
parallelReferences xs = RC $ \ownership -> do
  -- Run each path
  ys <- sequence [runRC x ownership | x <- xs]
  
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

runBalancedRC :: RC a -> FreshVarM a
runBalancedRC m = do
  (x, deficit) <- runRC m $ Map.empty
  unless (isBalanced deficit) $
    traceShow deficit $
    internalError "runBalancedRC: Found unbalanced reference counts"
  return x

-------------------------------------------------------------------------------

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
  of PrimType OwnedType -> v {varType = PrimType PointerType}
     PrimType _ -> v
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

-- | Perform reference count adjustment on a function.
rcFun :: [Var] -> Fun -> FreshVarM Fun
rcFun globals (Fun params returns body) = do
  body' <- runBalancedRC $
           withBorrowedVariables globals $
           withBorrowedVariables params $
           rcBlock returns body
  body'' <- execBuild body'
  return $ Fun (map toPointerVar params) returns body''

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
           retvars <- mapM newAnonymousVar return_types
           rcAtom return_types (bindAtom retvars) atom $
             return $ return $ ValA $ map (VarV . toPointerVar) retvars

rcStm :: Stm -> RC (GenM a) -> RC (GenM a)
rcStm statement k =
  case statement
  of LetE params atom -> do
       rcAtom (map varType params) (bindAtom $ map toPointerVar params) atom $
         withOwnedVariables params k

     LetrecE {} -> internalError "rcStm"

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
         adjust_references <- prim_adjust_references prim args
         args' <- mapM (rcVal True) args
         return $ do adjust_references
                     PrimA (toPointerPrim prim) `liftM` sequence args'

     SwitchA val cases -> do
       -- Scrutinee can never be a borrowed value
       val' <- rcVal False val 
       cases' <- parallelReferences $ map rc_alt cases
       return_atom $ SwitchA `liftM` val' `ap` sequence cases'
  where
    -- When storing an owned reference into memory, increment its
    -- reference count
    prim_adjust_references (PrimStore (PrimType OwnedType)) [_, value_arg] =
      case value_arg
      of VarV v -> do consumeReference v
                      return (return ())
         ConV c -> -- We don't globally track reference counts on this object.
                   -- Instead, increment the reference count right now.
                   return $ increfHeader (ConV c)
         _ -> traceShow (pprAtom atom) $ internalError "recAtom: Store of a non-variable pointer value"
    
    -- Casting from an owned reference consumes a reference
    prim_adjust_references (PrimCastFromOwned) [value_arg] =
      case value_arg
      of VarV v -> do consumeReference v
                      return (return ())
         _ -> internalError "recAtom: Cast of a non-variable pointer value"
    prim_adjust_references _ _ = return $ return ()
      
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

-- | Borrow references to any variables mentioned in the list
borrowValues :: [Val] -> RC (GenM ()) -> RC (GenM b) -> RC (GenM b)
borrowValues vals m k = borrowReferences owned_vars m k
  where
    owned_vars = mapMaybe get_owned_var vals
    get_owned_var (VarV v) | isOwnedVar v = Just v
    get_owned_var _ = Nothing

rcVal :: Bool -> Val -> RC (GenM Val)
rcVal is_borrowed value =
  case value
  of VarV v -> do
       -- Consume this reference
       when (isOwnedVar v && not is_borrowed) $ consumeReference v
       return $ return $ VarV $ toPointerVar v
     ConV c ->
       trace "rcVal: Assuming constructor is not owned" $
       return $ return value
     LitV l ->
       return $ return value
     _ -> internalError "rcVal"

insertReferenceCounting :: Module -> IO Module
insertReferenceCounting (Module funs datas) = do
  withTheLLVarIdentSupply $ \id_supply ->
    runFreshVarM id_supply $ do
      funs' <- mapM rc_fun funs
      return $ Module funs' datas
  where
    global_vars = [v | FunDef v _ <- funs] ++ [v | DataDef v _ _ <- datas]

    rc_fun (FunDef v f) = do
      f' <- rcFun global_vars f
      return $ FunDef v f'