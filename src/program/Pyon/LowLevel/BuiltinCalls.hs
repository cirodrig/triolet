{-| Converting builtin function calls to primitive operations.

This stage converts function calls to built-in functions such as \"add\"
to actual primitive operations.
-}

module Pyon.LowLevel.BuiltinCalls
       (makeBuiltinPrimOps)
where

import Control.Monad
import Control.Monad.Trans
import qualified Data.IntMap as IntMap

import Gluon.Common.Identifier
import Pyon.LowLevel.Build
import Pyon.LowLevel.Builtins
import Pyon.LowLevel.FreshVar
import Pyon.LowLevel.Syntax
import Pyon.LowLevel.Types
import Pyon.Globals

makeBuiltinPrimOps :: Module -> IO Module
makeBuiltinPrimOps (Module funs datas) =
  withTheLLVarIdentSupply $ \var_supply -> runFreshVarM var_supply $ do
    funs' <- mapM inlFunDef funs
    return $ Module funs' datas

type GenM a = Gen FreshVarM a

-- | Perform inlining on an atom.  If the atom is a call to a function that
-- can be inlined, try to inline it.
inlAtom :: Atom -> GenM Atom
inlAtom atom =
  case atom
  of CallA (VarV op) args -> inlCall op args
     _ -> return atom

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

inliningRules :: IntMap.IntMap ([Val] -> GenM Atom)
inliningRules =
  IntMap.fromList [ (fromIdent $ varID $ llBuiltin v, f (VarV $ llBuiltin v))
                  | (v, f) <- tbl]
  where
    tbl =
      [ (the_fun_add_int,
         binaryPrimOp $ PrimAddZ Signed pyonIntSize)
      , (the_fun_sub_int,
         binaryPrimOp $ PrimSubZ Signed pyonIntSize)
      , (the_fun_add_float,
         binaryPrimOp $ PrimAddF pyonFloatSize)
      , (the_fun_sub_float,
         binaryPrimOp $ PrimSubF pyonFloatSize)
      ]
