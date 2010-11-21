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
makeBuiltinPrimOps mod =
  withTheLLVarIdentSupply $ \var_supply -> runFreshVarM var_supply $ do
    funs' <- mapM inlFunDef $ moduleFunctions mod
    return $ mod {moduleFunctions = funs'}

type GenM a = FreshVarM a

-- | Perform inlining on a value.  If it's a lambda expression, perform
-- inlining inside the lambda expression.
inlValue :: Val -> GenM Val
inlValue (LamV f) = LamV `liftM` inlFun f
inlValue val = return val

inlValues :: [Val] -> GenM [Val]
inlValues vs = mapM inlValue vs

-- | Perform inlining on an atom.  If the atom is a call to a function that
-- can be inlined, try to inline it.
inlAtom :: Atom -> (Atom -> Stm) -> GenM Stm
inlAtom atom k =
  case atom
  of CallA ClosureCall (VarV op) args -> do args' <- inlValues args
                                            inlCall op args' k
     _ -> inline_subexpressions >>= return . k
  where
    inline_subexpressions =
      case atom
      of ValA vs ->  ValA `liftM` inlValues vs
         CallA conv op args -> CallA conv `liftM` inlValue op `ap` inlValues args
         PrimA prim args -> PrimA prim `liftM` inlValues args
         PackA rec args -> PackA rec `liftM` inlValues args
         UnpackA rec arg -> UnpackA rec `liftM` inlValue arg

inlStm :: Stm -> GenM Stm
inlStm stm =
  case stm
  of LetE params atom body -> do
       body' <- inlStm body
       inlAtom atom $ \atom' -> LetE params atom' body'
     LetrecE defs body -> do
       liftM2 LetrecE (mapM inlFunDef defs) (inlStm body)
     SwitchE val alts -> do
       liftM2 SwitchE (inlValue val) (mapM inl_alt alts)
     ReturnE atom ->
       inlAtom atom ReturnE
  where
    inl_alt (lit, stm) = do
      stm' <- inlStm stm
      return (lit, stm')


inlFun :: Fun -> FreshVarM Fun
inlFun f = do
  body' <- inlStm $ funBody f
  return $ f {funBody = body'}
{-  where
    rebuild_fun body
      | isPrimFun f =
          return $ primFun (funParams f) (funReturnTypes f) body
      | isClosureFun f =
          return $ closureFun (funParams f) (funReturnTypes f) body-}

inlFunDef :: FunDef -> FreshVarM FunDef
inlFunDef (FunDef vs f) = FunDef vs `liftM` inlFun f


-- | Attempt to inline a function call.
inlCall :: Var -> [Val] -> (Atom -> Stm) -> GenM Stm
inlCall op args k = 
  case IntMap.lookup (fromIdent $ varID op) inliningRules 
  of Just f -> f args k
     Nothing -> return $ k $ closureCallA (VarV op) args

-- | Generate a primitive operation that takes two parameters and one return 
-- value, all of the same type.
binaryPrimOp :: Prim -> Val -> [Val] -> (Atom -> Stm) -> GenM Stm
binaryPrimOp prim op args k =
  case args
  of [arg1, arg2] ->
       -- Saturated application
       return $ k $ PrimA prim [arg1, arg2]
     arg1 : arg2 : args' -> do
       -- Oversaturated application.  Perform the primitive operation.
       -- Then call the return value (which must be an OwnedType) with
       -- the remaining arguments.
       tmpvar <- newAnonymousVar $ PrimType OwnedType
       -- Pass the primop to the continuation
       let use_result = k $ closureCallA (VarV tmpvar) args'
       -- Perform the primop before the continuation
       return $ LetE [tmpvar] (PrimA prim [arg1, arg2]) use_result
     _ -> do
       -- Undersaturated application.  Don't replace it.
       return $ k $ closureCallA op args

-- | Generate a negation operation by generating a subtract primitive.
negateOp :: Lit -> Prim -> Val -> [Val] -> (Atom -> Stm) -> GenM Stm
negateOp zero prim op args k =
  case args
  of [arg] ->
       -- Saturated application
       return $ k $ PrimA prim [LitV zero, arg]
     args -> do
       -- Wrong number of operands
       return $ k $ closureCallA op args

-- Load and store functions are inserted by the compiler, and will always have
-- the right number of arguments.
--
-- Note that the arguments to stores are swapped: In Core, the address is last,
-- but here, the address is first.
loadOp ty _ args k =
  case args
  of [addr] -> return $ k $ PrimA (PrimLoad ty) [addr, nativeIntV 0]
     [] -> internalError "loadOp: Expecting exactly one argument"

storeOp ty _ args k =
  case args
  of [val, addr] -> return $ k $ PrimA (PrimStore ty) [addr, nativeIntV 0, val]
     [] -> internalError "storeOp: Expecting exactly two arguments"

-- Loading and storing "None" is actually a no-op. 
loadNone _ args k =
  case args
  of [addr] -> return $ k $ ValA [LitV UnitL]
     [] -> internalError "loadNone: Expecting exactly one argument"

storeNone _ args k =
  case args
  of [val, addr] -> return $ k $ ValA []
     [] -> internalError "storeNone: Expecting exactly two arguments"

inliningRules :: IntMap.IntMap ([Val] -> (Atom -> Stm) -> GenM Stm)
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
      , (the_fun_negate_int,
         negateOp (IntL Signed pyonIntSize 0) (PrimSubZ Signed pyonIntSize))
      , (the_fun_add_float,
         binaryPrimOp $ PrimAddF pyonFloatSize)
      , (the_fun_sub_float,
         binaryPrimOp $ PrimSubF pyonFloatSize)
      , (the_fun_negate_float,
         negateOp (FloatL pyonFloatSize 0) (PrimSubF pyonFloatSize))
      , (the_fun_mul_int,
         binaryPrimOp $ PrimMulZ Signed pyonIntSize)
      , (the_fun_mul_float,
         binaryPrimOp $ PrimMulF pyonFloatSize)
      ]
