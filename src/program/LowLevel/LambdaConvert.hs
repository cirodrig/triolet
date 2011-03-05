{-| Conversion of lambda expressions to letrec expressions. 

This is performed just before closure conversion.  Moving lambda 
expressions into separate statements simplifies closure conversion because 
now it doesn't have to deal with values containing functions.
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
     LamV f -> do
       f' <- lift $ cvtFun f
       lam_var <- lift $ newAnonymousVar (PrimType OwnedType)
       tell [Def lam_var f']
       return (VarV lam_var)

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
  case statement
  of LetE params rhs body ->
       emitLetrec $ LetE params <$> cvtAtom rhs <*> lift (cvtStm body)
     LetrecE defs body ->
       LetrecE <$> traverse cvtFunDef defs <*> cvtStm body
     SwitchE scr alts ->
       emitLetrec $ SwitchE <$> cvtVal scr <*> lift (mapM cvtAlt alts)
     ReturnE atom ->
       emitLetrec $ ReturnE <$> cvtAtom atom
  where
    cvtAlt (lit, stm) = (,) lit <$> cvtStm stm
       
cvtFun :: Fun -> FreshVarM Fun
cvtFun f = mkFun (funConvention f) (funInlineRequest f) (funFrameSize f) (funParams f)
           (funReturnTypes f) <$> cvtStm (funBody f)

cvtFunDef = cvtDef cvtFun

cvtData :: StaticData -> L StaticData
cvtData (StaticData rec vals) = StaticData rec <$> traverse cvtVal vals

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
