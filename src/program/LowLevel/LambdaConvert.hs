{-| Local transformations to enable closure conversion.

The main transformation is to convert lambda expressions to
local function definitions, which can subsequently be closure-converted.
Lambda-conversion also increases the success rate of value numbering,
since it turns lambdas (which can't be value numbered) into local functions
(which can).

Also, expressions that are not quite tail calls, of the form
@let x = foo(1,2) in x@, are fixed up into tail calls of the form 
@foo(1,2)@ where possible.
-}

module LowLevel.LambdaConvert(lambdaConvert)
where

import Prelude hiding(mapM) 
import Control.Applicative
import Control.Monad.Writer hiding(mapM)
import Data.Traversable
  
import LowLevel.CodeTypes
import LowLevel.FreshVar
import LowLevel.Syntax
import Globals

-- | Fix up a statement into a tail call using a form of backward
--   copy propagation.
fixupTailCalls :: Stm -> Stm
fixupTailCalls (LetE params rhs (ReturnE (ValA values)))
  | length params == length values &&
    and (zipWith isVarValue params values) = ReturnE rhs
  where
    isVarValue v1 (VarV v2) = v1 == v2
    isVarValue _ _ = False

fixupTailCalls s = s

emitLetrec :: L Stm -> FreshVarM Stm
emitLetrec m = do
  (stm, defs) <- runWriterT m
  return $ if null defs then stm else LetrecE (Rec defs) stm

-- | During lambda conversion, function definitions are floated to the 
--   nearest valid location.
type L a = WriterT [FunDef] FreshVarM a

cvtVal :: Val -> L Val
cvtVal value =
  case value
  of VarV _ -> return value
     RecV sr vals -> RecV sr <$> cvtVals vals
     LitV _ -> return value

cvtVals = traverse cvtVal

cvtAtom :: Atom -> L Atom
cvtAtom atom =
  case atom
  of ValA vals -> ValA <$> cvtVals vals
     CallA cc op args -> CallA cc <$> cvtVal op <*> cvtVals args
     PrimA op args -> PrimA op <$> cvtVals args
     PackA rec args -> PackA rec <$> cvtVals args
     UnpackA rec arg -> UnpackA rec <$> cvtVal arg

cvtStm :: Stm -> FreshVarM Stm
cvtStm statement =
  case fixupTailCalls statement
  of LetE params rhs body ->
       emitLetrec $ LetE params <$> cvtAtom rhs <*> lift (cvtStm body)
     LetrecE defs body ->
       LetrecE <$> traverse cvtFunDef defs <*> cvtStm body
     SwitchE scr alts ->
       emitLetrec $ SwitchE <$> cvtVal scr <*> lift (mapM cvtAlt alts)
     ReturnE atom ->
       emitLetrec $ ReturnE <$> cvtAtom atom
     ThrowE val ->
       emitLetrec $ ThrowE <$> cvtVal val
  where
    cvtAlt (lit, stm) = (,) lit <$> cvtStm stm
       
cvtFun :: Fun -> FreshVarM Fun
cvtFun f = mkFun (funConvention f) (funInlineRequest f) (funFrameSize f) (funParams f)
           (funReturnTypes f) <$> cvtStm (funBody f)

cvtFunDef = cvtDef cvtFun

cvtData :: StaticData -> L StaticData
cvtData (StaticData val) = StaticData <$> cvtVal val

cvtDef :: (Applicative m) => (a -> m a) -> Def a -> m (Def a)
cvtDef f (Def v x) = Def v <$> f x

cvtGlobalDef :: GlobalDef -> FreshVarM [GlobalDef]
cvtGlobalDef (GlobalFunDef fdef) = do
  fdef' <- cvtFunDef fdef
  return [GlobalFunDef fdef']

cvtGlobalDef (GlobalDataDef ddef) = do
  (ddef', new_defs) <- runWriterT $ cvtDef cvtData ddef
  return (map GlobalFunDef new_defs ++ [GlobalDataDef ddef'])

-- | Everything is smushed into a single recursive group.
--   DCE can sort it out later.
cvtGlobalDefGroup :: Group GlobalDef -> FreshVarM (Group GlobalDef)
cvtGlobalDefGroup group =
  Rec . concat <$> mapM cvtGlobalDef (groupMembers group)

lambdaConvert :: Module -> IO Module
lambdaConvert mod =
  withTheLLVarIdentSupply $ \var_ids -> do
    global_defs <- runFreshVarM var_ids $
                   mapM cvtGlobalDefGroup $ moduleGlobals mod
    return $ mod {moduleGlobals = global_defs}
