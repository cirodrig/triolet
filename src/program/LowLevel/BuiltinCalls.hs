{-| Converting builtin function calls to primitive operations.

This stage converts function calls to built-in functions such as \"add\"
to actual primitive operations.
-}

module LowLevel.BuiltinCalls
       (makeBuiltinPrimOps)
where

import Control.Monad
import Control.Monad.Trans
import qualified Data.IntMap as IntMap

import Gluon.Common.Error
import Gluon.Common.Identifier
import LowLevel.Build
import LowLevel.Builtins
import LowLevel.FreshVar
import LowLevel.Syntax
import LowLevel.Types
import Globals

makeBuiltinPrimOps :: Module -> IO Module
makeBuiltinPrimOps (Module funs datas) =
  withTheLLVarIdentSupply $ \var_supply -> runFreshVarM var_supply $ do
    funs' <- mapM inlFunDef funs
    return $ Module funs' datas

type GenM a = Gen FreshVarM a

-- | Perform inlining on a value.  If it's a lambda expression, perform
-- inlining inside the lambda expression.
inlValue :: Val -> GenM Val
inlValue v = lift $ inlValue' v

inlValues :: [Val] -> GenM [Val]
inlValues vs = lift $ mapM inlValue' vs

inlValue' :: Val -> FreshVarM Val
inlValue' (LamV f) = LamV `liftM` inlFun f
inlValue' val = return val

-- | Perform inlining on an atom.  If the atom is a call to a function that
-- can be inlined, try to inline it.
inlAtom :: Atom -> GenM Atom
inlAtom atom =
  case atom
  of ValA vs -> ValA `liftM` inlValues vs
     CallA (VarV op) args -> inlCall op =<< inlValues args
     CallA op args -> CallA `liftM` inlValue op `ap` inlValues args
     PrimCallA op args -> PrimCallA `liftM` inlValue op `ap` inlValues args
     PrimA prim args -> PrimA prim `liftM` inlValues args
     PackA rec args -> PackA rec `liftM` inlValues args
     UnpackA rec arg -> UnpackA rec `liftM` inlValue arg
     SwitchA val alts -> SwitchA `liftM` inlValue val `ap` mapM inlAlt alts
  where
    inlAlt (lit, block) = do
      block' <- getBlock $ inlBlock block
      return (lit, block')

inlStm :: Stm -> GenM ()
inlStm stm =
  case stm
  of LetE params atom -> bindAtom params =<< inlAtom atom
     LetrecE defs -> emitLetrec =<< lift (mapM inlFunDef defs)

-- | Perform inlining on a block, and return the block.
inlBlock :: Block -> GenM Atom
inlBlock (Block stms atom) = mapM inlStm stms >> inlAtom atom

inlFun :: Fun -> FreshVarM Fun
inlFun f = rebuild_fun =<< execBuild (inlBlock $ funBody f)
  where
    rebuild_fun body
      | isPrimFun f =
          return $ primFun (funParams f) (funReturnTypes f) body
      | isClosureFun f =
          return $ closureFun (funParams f) (funReturnTypes f) body

inlFunDef :: FunDef -> FreshVarM FunDef
inlFunDef (FunDef vs f) = FunDef vs `liftM` inlFun f


-- | Attempt to inline a function call.
inlCall :: Var -> [Val] -> GenM Atom
inlCall op args = 
  case IntMap.lookup (fromIdent $ varID op) inliningRules 
  of Just f -> f args
     Nothing -> return $ CallA (VarV op) args

-- | Generate a primitive operation that takes two parameters and one return 
-- value, all of the same type.
binaryPrimOp :: Prim -> Val -> [Val] -> GenM Atom
binaryPrimOp prim op args = 
  case args
  of [arg1, arg2] ->
       -- Saturated application
       return $ PrimA prim [arg1, arg2]
     arg1 : arg2 : args' -> do
       -- Oversaturated application.  Perform the primitive operation.
       -- Then call the return value (which must be an OwnedType) with
       -- the remaining arguments.
       tmpvar <- emitAtom1 (PrimType OwnedType) $ PrimA prim [arg1, arg2]
       return $ CallA tmpvar args'
     _ -> do
       -- Undersaturated application.  Don't replace it.
       return $ CallA op args

-- Load and store functions are inserted by the compiler, and will always have
-- the right number of arguments.
--
-- Note that the arguments to stores are swapped: In Core, the address is last,
-- but here, the address is first.
loadOp ty _ args =
  case args
  of [addr] -> return $ PrimA (PrimLoad ty) [addr, nativeIntV 0]
     [] -> internalError "loadOp: Expecting exactly one argument"

storeOp ty _ args =
  case args
  of [val, addr] -> return $ PrimA (PrimStore ty) [addr, nativeIntV 0, val]
     [] -> internalError "storeOp: Expecting exactly two arguments"

-- Loading and storing "None" is actually a no-op. 
loadNone _ args =
  case args
  of [addr] -> return $ ValA [LitV UnitL]
     [] -> internalError "loadNone: Expecting exactly one argument"

storeNone _ args =
  case args
  of [val, addr] -> return $ ValA []
     [] -> internalError "storeNone: Expecting exactly two arguments"

inliningRules :: IntMap.IntMap ([Val] -> GenM Atom)
inliningRules =
  IntMap.fromList [ (fromIdent $ varID $ llBuiltin v, f (VarV $ llBuiltin v))
                  | (v, f) <- tbl]
  where
    tbl =
      [ (the_fun_load_int, loadOp (PrimType pyonIntType))
      , (the_fun_store_int, storeOp (PrimType pyonIntType))
      , (the_fun_load_float, loadOp (PrimType pyonFloatType))
      , (the_fun_store_float, storeOp (PrimType pyonFloatType))
      , (the_fun_load_NoneType, loadNone)
      , (the_fun_store_NoneType, storeNone)
      , (the_fun_add_int,
         binaryPrimOp $ PrimAddZ Signed pyonIntSize)
      , (the_fun_sub_int,
         binaryPrimOp $ PrimSubZ Signed pyonIntSize)
      , (the_fun_add_float,
         binaryPrimOp $ PrimAddF pyonFloatSize)
      , (the_fun_sub_float,
         binaryPrimOp $ PrimSubF pyonFloatSize)
      ]
