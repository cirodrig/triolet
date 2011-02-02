
{-# LANGUAGE TypeSynonymInstances #-}
module SystemF.LocalExprRewrite (rewriteLocalExpr)
where

import SystemF.MemoryIR
import SystemF.Syntax
import SystemF.Rename
import qualified SystemF.PrintMemoryIR

import Common.Identifier
import Common.Supply
import qualified SystemF.DictEnv as DictEnv
import Type.Type
import Type.Environment

import Globals
import GlobalVar
import Control.Monad
import Debug.Trace

import Data.List as List

newtype LR a = LR {runLR :: Supply VarID -> IO a}

instance Monad LR where
  return x = LR (\_ -> return x)
  m >>= k = LR $ \env -> do
    x <- runLR m env
    runLR (k x) env
    
instance Supplies LR VarID where
  fresh = LR (\sup -> supplyValue sup)
  supplyToST = undefined    

data LetPart s = LetPart { lpInfo :: ExpInfo
                         , lpBinder :: Pat s
                         , lpValue :: Exp s
                         -- lpBody :: Exp s
                         }
                  
type LetPartM = LetPart Mem              
                                                   

shapeLet :: ExpM -> LetPartM -> LR ExpM
shapeLet body (LetPart lpInf lpBind lpVal) = do
  let reshaped = ExpM $ LetE lpInf lpBind lpVal body
  renamed <- freshen reshaped
  return renamed
  
constructLet :: ExpM -> [LetPartM] -> LR ExpM
constructLet body [] = return body
constructLet body parts = do
  result <- foldM shapeLet body parts
  return result

rwAlt :: AltM -> LR AltM
rwAlt (AltM (Alt const tyArgs exTypes params body)) = do
  body' <- rwExp body
  return $ AltM $ Alt const tyArgs exTypes params body'
     
delveExp :: ExpM -> LR ([LetPartM], ExpM)
delveExp (ExpM ex) = do
  case ex of
    LetE inf bind val body -> do
      body' <- rwExp body
      (letPs, replaceExp) <- delveExp val
      case bind of
        MemVarP var ptype -> do
          let letPart = LetPart inf bind replaceExp
          return ( letPart:letPs , body')
        _ -> do
          let result = ExpM $ LetE inf bind replaceExp body'
          return (letPs, result)
    AppE inf oper tyArgs args -> do
      tupList <- mapM delveExp args
      let (letParts, toReplaceArgs) = unzip tupList
      let letParts' = concat letParts
      let replacedApp = ExpM $ AppE inf oper tyArgs toReplaceArgs
      return (letParts', replacedApp)
    _ -> do
      ex' <- rwExp (ExpM ex)
      return ([], ex')    

{-
topExp :: ExpM -> LR ExpM
topExp (ExpM ex) = do
  case ex of
    LetE inf bind val body -> do
      body' <- {-trace "Top Checking body of a Let"-} topExp body
      (letPs, casePs, val') <- {-trace "Done with body, moving to Val"-} delveExp val
      let replaced = ExpM $ LetE inf bind val' body'
      postLet <- {-trace ("For the val on LetE:: "++(show (List.length letPs))++" lets, "++(show (List.length casePs))++" cases")-} constructLet replaced letPs
--      postCase <- constructCase postLet casePs
      return postLet
    CaseE inf scrut alts -> do scrut' <- topExp scrut
                               alts' <- mapM rwAlt alts
                               return $ ExpM $ CaseE inf scrut' alts'
    AppE inf oper tyArgs args -> do
      tupList <- mapM delveExp args
      let (letParts, caseParts, toReplaceArgs) = unzip3 tupList
      let letParts' = concat letParts
--      let caseParts' = concat caseParts
      let replacedApp = ExpM $ AppE inf oper tyArgs toReplaceArgs
      afterLetParts <- constructLet replacedApp letParts'
--      afterLetAndCaseParts <- constructCase afterLetParts caseParts'
      return afterLetParts
    LetrecE inf defs body -> do defs' <- mapM rwDef defs
                                body' <- topExp body
                                return $ ExpM $ LetrecE inf defs' body'
    LamE inf fun -> do fun' <- rwFun fun
                       return $ ExpM $ LamE inf fun'
    _ -> return $ ExpM ex -- Var and Lit
    -}
    
restructureExp :: ExpM -> LR ExpM
restructureExp (ExpM ex) = do
  case ex of
    LetE inf bind val body -> do
      body' <- rwExp body
      (letPs, val') <- {-trace "Done with body, moving to Val"-} delveExp val
      let replaced = ExpM $ LetE inf bind val' body'
      postLet <- constructLet replaced letPs
      return postLet
    AppE inf oper tyArgs args -> do
      oper' <- rwExp oper
      tupList <- mapM delveExp args
      let (letParts, toReplaceArgs) = unzip tupList
      let letParts' = concat letParts
      let replacedApp = ExpM $ AppE inf oper' tyArgs toReplaceArgs
      afterLetParts <- constructLet replacedApp letParts'
      return afterLetParts
    _ -> return $ ExpM ex
    
rwExp :: ExpM -> LR ExpM
rwExp (ExpM ex) = do
  case ex of
    LetE inf bind val body -> do
      ex' <- restructureExp (ExpM ex)
      return $ ex'
    CaseE inf scrut alts -> do scrut' <- rwExp scrut
                               alts' <- mapM rwAlt alts
                               return $ ExpM $ CaseE inf scrut' alts'
    AppE inf oper tyArgs args -> do
      ex' <- restructureExp (ExpM ex)
      return $ ex'
    LetrecE inf defs body -> do defs' <- mapM rwDef defs
                                body' <- rwExp body
                                return $ ExpM $ LetrecE inf defs' body'
    LamE inf fun -> do fun' <- rwFun fun
                       return $ ExpM $ LamE inf fun'
    _ -> return $ ExpM ex -- Var and Lit
    
    
rwFun :: FunM -> LR FunM
rwFun (FunM f) = do
  body' <- rwExp (funBody f)
  return $ FunM $ Fun { funInfo = funInfo f
                      , funTyParams = funTyParams f
                      , funParams = funParams f
                      , funReturn = funReturn f
                      , funBody = body'}
    
rwDef :: Def Mem -> LR (Def Mem)
rwDef (Def v f) = do
  f' <- rwFun f
  return (Def v f')

rwExport :: Export Mem -> LR (Export Mem)
rwExport (Export pos spec f) = do
  f' <- rwFun f
  return (Export pos spec f')

rwModule :: Module Mem -> LR (Module Mem)
rwModule (Module mod_name defs exports) = do
  defs' <- mapM (mapM rwDef) defs
  exports' <- mapM rwExport exports
  return $ Module mod_name defs' exports'

rewriteLocalExpr :: Module Mem -> IO (Module Mem)
rewriteLocalExpr mod = do
  withTheNewVarIdentSupply $ \var_supply -> do
    runLR (rwModule mod) var_supply


