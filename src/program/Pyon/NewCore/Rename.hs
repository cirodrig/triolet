
{-# LANGUAGE TypeFamilies, Rank2Types, FlexibleInstances, FlexibleContexts #-}
module Pyon.NewCore.Rename
       (SRVal, SRStm,
        freshenActionFun,
        freshenActionFunFully,
        verbatimActionFun,
        freshenStreamFun,
        freshenModuleHead) {-freshenVar,
        renameValFully,
        renameValHead, freshenValHead,
        renameStmFully,
        renameStmHead, freshenStmHead,
        freshenActionFunHead,
        freshenActionFunFully,
        freshenStreamFunHead,
        freshenDefGroupHead,
        freshenModuleHead) -}
where

import Control.Monad
import Data.Monoid
import Data.Map(Map)
import qualified Data.Map as Map
import Data.Maybe

import Gluon.Common.SourcePos
import Gluon.Common.Identifier
import Gluon.Common.MonadLogic
import Gluon.Common.Supply
import Gluon.Core.Level
import Gluon.Core(Rec, mkVar)
import Gluon.Core.Rename
import Gluon.Core.RenameBase
import Pyon.NewCore.Syntax

withMany :: Monad m =>
            (a -> (b -> m c) -> m c) -> [a] -> ([b] -> m c) -> m c
withMany f (x:xs) k = f x $ \y -> withMany f xs $ \ys -> k (y:ys)
withMany _ []     k = k []

freshenMany :: Monad m =>
               (forall b. a -> m b -> m (a, b)) -> [a] -> m b -> m ([a], b)
freshenMany f (x:xs) m = do
  (y, (ys, z)) <- f x $ freshenMany f xs m
  return (y:ys, z)

freshenMany _ [] m = do
  z <- m
  return ([], z)

newtype instance ValOf (Subst s) (Subst s) = SVal (SubstWrapped ValOf)
newtype instance StmOf (Subst s) (Subst s) = SStm (SubstWrapped StmOf)

type SRVal = RecVal SubstRec
type SRStm = RecStm SubstRec

instance HasSourcePos (ValOf SubstRec SubstRec) where
  getSourcePos (SVal x) = getSourcePos x
  setSourcePos (SVal x) p = SVal (setSourcePos x p)

instance Substitutable ValOf where
  asSubst = SVal
  fromSubst (SVal s) = s
  mapSubstitutable f = mapVal f f f
  applySubstitution sub val =
    mapVal (joinSubst sub) (joinSubst sub) (joinSubst sub) val

instance Substitutable StmOf where
  asSubst = SStm
  fromSubst (SStm s) = s
  mapSubstitutable f = mapStm f f f
  applySubstitution sub stm =
    mapStm (joinSubst sub) (joinSubst sub) (joinSubst sub) stm

instance Renameable ValOf where
  freshenHead x = withSubstitutable x f
    where
      f value =
        case value
        of GluonV info t -> GluonV info `liftM` joinSubstitution t
           AppV info op args -> AppV info `liftM`
                                joinSubstitution op `ap`
                                mapM joinSubstitution args
           ALamV info f -> ALamV info `liftM` freshenActionFun f
           SLamV info f -> SLamV info `liftM` freshenStreamFun f
           SDoV info s -> SDoV info `liftM` joinSubstitution s
  
  freshenFully v = traverseVal freshenFully freshenFully freshenFully =<<
                   freshenHead v

instance Renameable StmOf where
  freshenHead x = withSubstitutable x f
    where
      f statement =
        case statement
        of ReturnS info val -> ReturnS info `liftM` joinSubstitution val
           CallS info val -> CallS info `liftM` joinSubstitution val
           LetS info mv s1 s2 -> do
             s1' <- joinSubstitution s1
             (mv', s2') <- withFreshVarMaybe mv $ joinSubstitution s2
             return $ LetS info mv' s1' s2'
           LetrecS info defs body -> do
             (defs', body') <- withDefinitions defs $ joinSubstitution body
             return $ LetrecS info defs' body'
           CaseS info scr alts ->
             CaseS info `liftM` joinSubstitution scr `ap` mapM freshenAlt alts

  freshenFully s = traverseStm freshenFully freshenFully freshenFully =<<
                   freshenHead s

withFreshVarMaybe Nothing m = do
  x <- m
  return (Nothing, x)

withFreshVarMaybe (Just v) m = do
  (v', x) <- withFreshVar v m
  return (Just v', x)

freshenBinders :: [Binder SubstRec ()]
               -> WithSubstitution a
               -> WithSubstitution ([Binder SubstRec ()], a)
freshenBinders = freshenMany freshenBinder

withFreshVars :: [Var] 
              -> WithSubstitution a 
              -> WithSubstitution ([Var], a)
withFreshVars = freshenMany withFreshVar

withDefinitions :: [Def SubstRec]
                -> WithSubstitution a
                -> WithSubstitution ([Def SubstRec], a)
withDefinitions defs m = do
  -- Create new definitions of local variables
  (definienda, (definientia, x)) <- withFreshVars (map definiendum defs) $ do
    -- Apply the renaming to definientia
    definientia <- mapM (substituteInDefiniens . definiens) defs
    x <- m
    return (definientia, x)
  let defs' = zipWith3 Def (map defInfo defs) definienda definientia
  return (defs', x)
  where
    substituteInDefiniens (ActionFunDef f) =
      ActionFunDef `liftM` freshenActionFun f
    substituteInDefiniens (StreamFunDef f) =
      StreamFunDef `liftM` freshenStreamFun f

freshenActionFun f = do
  (params, (rt, et, b)) <- freshenBinders (funParams f) $ do
    rt <- joinSubstitution $ funReturnType f
    et <- joinSubstitution $ funEffectType f
    b <- joinSubstitution $ funBody f
    return (rt, et, b)
  return $ Fun params rt et b

freshenStreamFun f = do             
  (params, (rt, et, b)) <- freshenBinders (funParams f) $ do
    rt <- joinSubstitution $ funReturnType f
    -- Effect type is ignored
    let et = funEffectType f
    b <- joinSubstitution $ funBody f
    return (rt, et, b)
  return $ Fun params rt et b

freshenActionFunFully :: ActionFun SubstRec 
                      -> WithSubstitution (ActionFun Rec)
freshenActionFunFully f = do
  (params, (rt, et, b)) <- freshenBinders (funParams f) $ do
    rt <- joinAndFreshenFully $ funReturnType f
    et <- joinAndFreshenFully $ funEffectType f
    b <- joinAndFreshenFully $ funBody f
    return (rt, et, b)
  params' <- mapM (traverseBinder return freshenFully) params
  return $ Fun params' rt et b

verbatimActionFun :: ActionFun Rec -> ActionFun SubstRec
verbatimActionFun f =
  let params = map (mapBinder id verbatim) $ funParams f
      rt = verbatim $ funReturnType f
      et = verbatim $ funEffectType f
      b = verbatim $ funBody f
  in Fun params rt et b

substActionFun :: ActionFun SubstRec -> ActionFun Rec
substActionFun f =
  let params = map (mapBinder id substFully) $ funParams f
      rt = substFully $ funReturnType f
      et = substFully $ funEffectType f
      body = substFully $ funBody f
  in Fun params rt et body

substStreamFun :: StreamFun SubstRec -> StreamFun Rec
substStreamFun f =
  let params = map (mapBinder id substFully) $ funParams f
      rt = substFully $ funReturnType f
      et = substFully $ funEffectType f
      body = substFully $ funBody f
  in Fun params rt et body


freshenAlt alt = do
  (pat, body) <- withFreshPattern (altPat alt) $ joinSubstitution (altBody alt)
  return $ Alt (altInfo alt) pat body

withFreshPattern (ConP con params) m = do
  (params', x) <- freshenMany freshenConParam params m
  return (ConP con params', x)
  where
    freshenConParam RigidP m = do x <- m 
                                  return (RigidP, x)
    freshenConParam (FlexibleP v) m = do (v', x) <- withFreshVar v m
                                         return (FlexibleP v', x)

freshenModuleHead :: (Monad m, Supplies m VarID) =>
                     Module Rec -> m (Module SubstRec)
freshenModuleHead (Module defs) = do
  (rn_defs, _) <- withEmptySubstitution $
                  withDefinitions (map toVerbatim defs) $
                  return ()
  return $ Module rn_defs
  where
    toVerbatim (Def info name definiens) = 
      let new_definiens =
            case definiens
            of ActionFunDef f -> ActionFunDef $ toVerbatimA f
               StreamFunDef f -> StreamFunDef $ toVerbatimS f
      in Def info name new_definiens
    
    toVerbatimA (Fun params rt et body) =
      Fun (map (mapBinder id verbatim) params)
          (verbatim rt) (verbatim et) (verbatim body)
    
    toVerbatimS (Fun params rt et body) =
      Fun (map (mapBinder id verbatim) params)
          (verbatim rt) (verbatim et) (verbatim body)
