
{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts #-}
module Pyon.NewCore.Rename
       (PyonSubst(..),
        freshenVar,
        renameValFully,
        renameValHead, freshenValHead,
        renameStmFully,
        renameStmHead, freshenStmHead)
where

import Control.Monad
import Data.Map(Map)
import qualified Data.Map as Map
import Data.Maybe

import Gluon.Common.SourcePos
import Gluon.Common.Identifier
import Gluon.Common.MonadLogic
import Gluon.Common.Supply
import Gluon.Core.Level
import Gluon.Core(Core, mkVar)
import Gluon.Core.Rename hiding(freshenBinder, freshenBinder')
import Gluon.Core.RenameBase hiding(freshenVar)
import Pyon.NewCore.Syntax

{-
-- | Pyon variables may only be renamed (not substituted).
-- Pyon types may be substituted in the manner of Gluon types.
data PyonSubst =
  PyonSubst
  { pyonRenaming :: Map Var Var
  , gluonSubst :: Subst Core
  }
-}
type PyonSubst = Subst Core

instance PyonSyntax (SubstitutingT Core) where
  type ValOf (SubstitutingT Core) = SubstitutingSyntax Core Val
  type StmOf (SubstitutingT Core) = SubstitutingSyntax Core Stm

-- renameVariable :: PyonSubst -> Var -> Var
-- renameVariable subst v = fromMaybe v $ Map.lookup v (pyonRenaming subst)

suspendPyon :: PyonSubst -> t Core 
            -> SubstitutingSyntax Core t (SubstitutingT Core)
suspendPyon subst x = SubstitutingSyntax (subst :@ x)

suspendGluon :: PyonSubst -> t Core 
             -> SubstitutingSyntax Core t (SubstitutingT Core)
suspendGluon subst x = SubstitutingSyntax (subst :@ x)

renameValFully :: RecVal (SubstitutingT Core) -> Val Core
renameValFully v = mapVal renameValFully renameStmFully renameFully $
                   renameValHead v

renameValHead :: RecVal (SubstitutingT Core) -> Val (SubstitutingT Core)
renameValHead (SubstitutingSyntax (sub :@ value)) =
  let r = suspendPyon sub
  in case value
     of VarV info v -> case substituteForVar (substSubstituter sub) info v
                       of Nothing -> VarV info v
                          Just e  -> GluonV info (verbatim e)
        _ -> mapVal (suspendPyon sub) (suspendPyon sub) (suspendGluon sub)
             value

freshenValHead :: (Monad m, Supplies m VarID) =>
                  RecVal (SubstitutingT Core) -> m (Val (SubstitutingT Core))
freshenValHead subst_value@(SubstitutingSyntax (sub :@ value)) =
  case value
  of ALamV info afun ->
       liftM (ALamV info) $ freshenActionFunHead sub afun
     SLamV info sfun ->
       liftM (SLamV info) $ freshenStreamFunHead sub sfun
     -- Other terms do not bind variables
     _ -> return $ renameValHead subst_value

freshenActionFunHead :: (Monad m, Supplies m VarID) =>
                        PyonSubst -> ActionFun Core
                     -> m (ActionFun (SubstitutingT Core))
freshenActionFunHead = freshenFunHead suspendPyon
freshenStreamFunHead :: (Monad m, Supplies m VarID) =>
                        PyonSubst -> StreamFun Core
                     -> m (StreamFun (SubstitutingT Core))
freshenStreamFunHead = freshenFunHead suspendPyon

freshenFunHead :: (Monad m, Supplies m VarID) =>
                  (PyonSubst -> a -> b)
               -> PyonSubst -> Fun Core a
               -> m (Fun (SubstitutingT Core) b)
freshenFunHead suspendBody sub fun = do
  (sub', params') <- mapAccumM freshenBinder sub (funParams fun)
  let rt = suspendGluon sub' $ funReturnType fun
      et = suspendGluon sub' $ funEffectType fun
      body = suspendBody sub' $ funBody fun
  return $ Fun params' rt et body

freshenDefiniensHead :: (Monad m, Supplies m VarID) =>
                        PyonSubst -> Definiens Core 
                     -> m (Definiens (SubstitutingT Core))
freshenDefiniensHead sub (ActionFunDef f) = 
  liftM ActionFunDef $ freshenActionFunHead sub f
freshenDefiniensHead sub (StreamFunDef f) = 
  liftM StreamFunDef $ freshenStreamFunHead sub f

freshenBinder :: (Monad m, Supplies m VarID) =>
                 PyonSubst -> Binder Core () 
              -> m (PyonSubst, Binder (SubstitutingT Core) ())
freshenBinder sub (Binder v ty ()) = do
  let ty' = suspendGluon sub ty
  (sub', v') <- freshenVar sub v
  return (sub', Binder v' ty' ())

freshenBinder' :: (Monad m, Supplies m VarID) =>
                  PyonSubst -> Binder' Core () 
               -> m (PyonSubst, Binder' (SubstitutingT Core) ())
freshenBinder' sub (Binder' mv ty ()) = do
  let ty' = suspendGluon sub ty
  (sub', mv') <- case mv
                 of Nothing -> return (sub, Nothing)
                    Just v -> do (sub, v') <- freshenVar sub v
                                 return (sub, Just v')
  return (sub', Binder' mv' ty' ())

freshenVar :: (Monad m, Supplies m VarID) =>
              PyonSubst -> Var -> m (PyonSubst, Var)
freshenVar sub v = do
  newID <- fresh
  let lv = getLevel v
      v' = mkVar newID (varName v) lv
      sub' = extend v (VarRep v') sub {-if lv == ObjectLevel
             -- Object-level variables go into the Pyon map
             then sub {pyonRenaming = Map.insert v v' $ pyonRenaming sub}
             -- Type-level variables go into the Gluon substitution
             else sub {gluonSubst = extend v (VarRep v') $ gluonSubst sub} -}
  return (sub', v')

renameStmFully :: RecStm (SubstitutingT Core) -> Stm Core
renameStmFully s = mapStm renameValFully renameStmFully renameFully $
                   renameStmHead s

renameStmHead :: RecStm (SubstitutingT Core) -> Stm (SubstitutingT Core)
renameStmHead (SubstitutingSyntax (sub :@ statement)) =
  mapStm (suspendPyon sub) (suspendPyon sub) (suspendGluon sub) statement

freshenStmHead :: (Monad m, Supplies m VarID) =>
                  RecStm (SubstitutingT Core) 
               -> m (Stm (SubstitutingT Core))
freshenStmHead sub_statement@(SubstitutingSyntax (sub :@ statement)) =
  case statement
  of LetS {stmInfo = inf, stmVar = mv, stmStm = rhs, stmBody = body} -> do
       let rhs' = suspendPyon sub rhs
       (body', mv') <-
         case mv
         of Nothing -> do let body' = suspendPyon sub body
                          return (body', Nothing)
            Just v  -> do (sub', v') <- freshenVar sub v
                          let body' = suspendPyon sub' body
                          return (body', Just v')
       return $ LetS inf mv' rhs' body'
     
     LetrecS {stmInfo = inf, stmDefs = defs, stmBody = body} -> do
       -- Create new definitions of local variables
       (sub', newLocalVars) <- mapAccumM freshenVar sub $ map definiendum defs
       
       -- Visit subexpressions 
       functions <- mapM (freshenDefiniensHead sub') $ map definiens defs
       let defs' = zipWith3 Def (map defInfo defs) newLocalVars functions
       let body' = suspendPyon sub' body
       
       -- Rebuild expression
       return $ LetrecS inf defs' body'
     
     CaseS {stmInfo = inf, stmScrutinee = val, stmAlts = alts} -> do 
       let val' = suspendPyon sub val
       alts' <- mapM (freshenAlt sub) alts
       return $ CaseS inf val' alts'
       
     -- Other forms don't bind variables
     _ -> return $ renameStmHead sub_statement
  
  where
    freshenAlt sub (Alt info pat body) = do
      (sub', pat') <- freshenPat sub pat
      let body' = suspendPyon sub' body
      return $ Alt info pat' body'
      
    freshenPat sub (ConP con params) = do
      (sub', params') <- mapAccumM freshenConParamPat sub params
      return (sub', ConP con params')
    
    freshenConParamPat sub RigidP = return (sub, RigidP)
    freshenConParamPat sub (FlexibleP v) = do
      (sub', v') <- freshenVar sub v
      return (sub', FlexibleP v')
      