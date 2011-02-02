
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

data AltPart s = AltPart
                 { altpConstructor :: !Var
                 , altpTyArgs      :: [Typ s]
                 , altpExTypes     :: [TyPat s]
                 , altpParams      :: [Pat s]
                 -- altpBody        :: Exp s
                 }            
                         
data CasePart s = CasePart 
                  { cpInfo :: ExpInfo
                  , cpScrutinee :: Exp s
                  , cpAltPart :: AltPart s
                  }
                  
type LetPartM = LetPart Mem
type CasePartM = CasePart Mem                  
                                                   

shapeLet :: ExpM -> LetPartM -> LR ExpM
shapeLet body (LetPart lpInf lpBind lpVal) = do
  let reshaped = ExpM $ LetE lpInf lpBind lpVal body
  renamed <- freshen reshaped
  return renamed
  
  {-
shapeCase :: ExpM -> CasePartM -> LR ExpM
shapeCase body (CasePart cpInf cpScrut cpAltPart) = do
  case cpAltPart of
    AltPart const tyArgs exTypes params -> do
      let fullAlt = AltM $ Alt const tyArgs exTypes params body
 --     renamed <- freshen fullAlt
      return $ ExpM $ CaseE cpInf cpScrut [fullAlt]
  -}
constructLet :: ExpM -> [LetPartM] -> LR ExpM
constructLet body [] = return body
constructLet body parts = do
  result <- foldM shapeLet body parts
  return result
  
  {-
constructCase :: ExpM -> [CasePartM] -> LR ExpM
constructCase body [] = return body
constructCase body parts = do
  result <- foldM shapeCase body parts
  return result
-}


rwAlt :: AltM -> LR AltM
rwAlt (AltM (Alt const tyArgs exTypes params body)) = do
  body' <- topExp body
  return $ AltM $ Alt const tyArgs exTypes params body'
     
delveExp :: ExpM -> LR ([LetPartM], [CasePartM], ExpM)
delveExp (ExpM ex) = do
  case ex of
    LetE inf bind val body -> do
      body' <- topExp body
      (letPs, casePs, replaceExp) <- delveExp val
      case bind of
        MemVarP var ptype -> do
          let letPart = LetPart inf bind replaceExp
          {-trace "Found a Let MemVar, lifting..."-} 
          return ( letPart:letPs , casePs, body')
        _ -> do
          let result = ExpM $ LetE inf bind replaceExp body'
          {-trace "Found a Let LocalVar, returning..."-} 
          return (letPs, casePs, result)
 {-   CaseE inf scrut ((AltM alt):[]) -> do
      scrut' <- topExp scrut
      case alt of
        Alt const tyArgs exTypes params body -> do
          (letPs, casePs, replaceExp) <- delveExp body
          let altPart = AltPart const tyArgs exTypes params
          let casePart = CasePart inf scrut' altPart
          {-trace ("Lifting Case, to return: "++(show (List.length letPs))++" lets, "++(show (1+(List.length casePs)))++" cases")-} 
          return (letPs, casePart:casePs, replaceExp)
          -}
    AppE inf oper tyArgs args -> do
      tupList <- mapM delveExp args
      let (letParts, caseParts, toReplaceArgs) = unzip3 tupList
      let letParts' = concat letParts
      let caseParts' = concat caseParts
      let replacedApp = ExpM $ AppE inf oper tyArgs toReplaceArgs
      return (letParts', caseParts', replacedApp)
    _ -> do -- includes multiple alternative cases
      ex' <- {-trace "Other type in delveExp, returning..."-} topExp (ExpM ex)
      return ([], [], ex')    

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
    
rwFun :: FunM -> LR FunM
rwFun (FunM f) = do
  body' <- {-trace "in rwFun"-} topExp (funBody f)
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


