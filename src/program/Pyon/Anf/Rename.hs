
{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts, Rank2Types #-}
module Pyon.Anf.Rename
       (SRStm, SRVal, SRProc)
where

import Control.Monad

import Gluon.Common.Supply
import Gluon.Common.SourcePos
import Gluon.Core
import Gluon.Core.RenameBase
import Gluon.Core.Level
import Pyon.Anf.Syntax

-------------------------------------------------------------------------------
-- Substitution

newtype instance ValOf (Subst s) (Subst s) = SVal (SubstWrapped ValOf)
newtype instance StmOf (Subst s) (Subst s) = SStm (SubstWrapped StmOf)
newtype instance ProcOf (Subst s) (Subst s) = SProc (SubstWrapped ProcOf)

type SRStm = RecStm SubstRec
type SRVal = RecVal SubstRec
type SRProc = RecProc SubstRec

instance Substitutable ValOf where
  asSubst e = SVal e
  
  fromSubst (SVal e) = e
  
  mapSubstitutable f value =
    case value
    of GluonV {valGluonTerm = e} ->
         value {valGluonTerm = f e}
       AppV {valOper = op, valArgs = args} ->
         value {valOper = f op, valArgs = map f args}
       LamV {valProc = proc} ->
         value {valProc = f proc}

  applySubstitution subst value =
    mapSubstitutable (joinSubst subst) value

instance Substitutable StmOf where
  asSubst e = SStm e
  
  fromSubst (SStm e) = e
  
  mapSubstitutable f statement =
    case statement
    of ReturnS {stmVal = val} ->
         statement {stmVal = f val}
       CallS {stmVal = val} ->
         statement {stmVal = f val}
       LetS {stmBinder = b, stmStm = s1, stmBody = s2} -> 
         statement { stmBinder = mapBinder id f b
                   , stmStm = f s1
                   , stmBody = f s2}
       LetrecS {stmDefs = dg, stmBody = body} ->
         statement { stmDefs = map (mapSubstitutableProcDef f) dg
                   , stmBody = f body
                   }
       CaseS {stmScrutinee = val, stmAlts = alts} ->
         statement { stmScrutinee = f val
                   , stmAlts = map (mapSubstitutableAlt f) alts}

  applySubstitution subst value =
    mapSubstitutable (joinSubst subst) value

instance Substitutable ProcOf where
  asSubst p = SProc p
  
  fromSubst (SProc p) = p
  
  mapSubstitutable f (Proc { procInfo = inf
                           , procParams = params
                           , procReturnType = rt
                           , procEffectType = et
                           , procBody = body}) =
    Proc { procInfo = inf
         , procParams = map (mapBinder id f) params
         , procReturnType = f rt
         , procEffectType = f et
         , procBody = f body
         }

  applySubstitution subst proc =
    mapSubstitutable (joinSubst subst) proc

mapSubstitutableProcDef :: (Structure a, Structure b) =>
                           (forall u. (Substitutable u) => u a a -> u b b)
                        -> ProcDef a -> ProcDef b
mapSubstitutableProcDef f (ProcDef v p) = ProcDef v (f p)


mapSubstitutableAlt :: (Structure a, Structure b) =>
                       (forall u. (Substitutable u) => u a a -> u b b)
                    -> Alt a -> Alt b
mapSubstitutableAlt f (Alt { altConstructor = con
                           , altParams = bs
                           , altBody = body}) =
  Alt { altConstructor = con
      , altParams = map (mapBinder id f) bs
      , altBody = f body
      }

-------------------------------------------------------------------------------
-- Renaming

instance Renameable ValOf where
  freshenHead x =
    withSubstitutable x $
    traverseVal joinSubstitution joinSubstitution joinSubstitution

  freshenFully x =
    freshenHead x >>=
    traverseVal freshenFully freshenFully freshenFully

instance Renameable ProcOf where
  freshenHead x = withSubstitutable x freshen
    where
      freshen proc = do
        (params, (rt, et, body)) <-
          freshenBinders (procParams proc) $ do
            rt <- joinSubstitution $ procReturnType proc
            et <- joinSubstitution $ procEffectType proc
            body <- joinSubstitution $ procBody proc
            return (rt, et :: SRExp, body)
        return $! Proc { procInfo = procInfo proc
                       , procParams = params
                       , procReturnType = rt
                       , procEffectType = et
                       , procBody = body                   
                         }

  freshenFully x =
    freshenHead x >>=
    traverseProc freshenFully freshenFully

instance Renameable StmOf where
  freshenHead x = withSubstitutable x freshen
    where
      freshen statement =
        case statement
        of ReturnS info val ->
             ReturnS info `liftM` joinSubstitution val
           CallS info val ->
             CallS info `liftM` joinSubstitution val
           LetS info binder rhs body -> do
             rhs' <- joinSubstitution rhs
             (binder', body') <- freshenBinder binder $ joinSubstitution body
             return $ LetS info binder' rhs' body'
           LetrecS info defs body -> do
             (vs', (procs', body')) <-
               -- Freshen the procedure names
               rename_defs defs $ do
                 -- Freshen procedure bodies and the main statement
                 procs' <- mapM freshen_def defs
                 body' <- joinSubstitution body
                 return (procs', body')

             -- Rebuild the LetrecS expression
             let defs' = zipWith ProcDef vs' procs'
             return $ LetrecS info defs' body'
           CaseS info scr alts ->
             CaseS info `liftM` joinSubstitution scr `ap` mapM freshen_alt alts
      
      freshen_def (ProcDef _ p) = joinSubstitution p
      
      rename_defs (ProcDef v _ : defs) k = do 
        (v', (vs', x)) <- withFreshVar v $ rename_defs defs k
        return (v' : vs', x)
        
      rename_defs [] k = do
        x <- k
        return ([], x)
             
      freshen_alt (Alt con params body) = do
        (params', body') <- freshenBinders params $ joinSubstitution body
        return $ Alt con params' body'
  
  freshenFully x =
    freshenHead x >>=
    traverseStm freshenFully freshenFully freshenFully freshenFully

freshenBinders :: [Binder SubstRec ()]
               -> WithSubstitution a
               -> WithSubstitution ([Binder SubstRec ()], a)
freshenBinders (b:bs) m = do
  (b', (bs', x)) <- freshenBinder b $ freshenBinders bs m
  return (b' : bs', x)

freshenBinders [] m = do
  x <- m
  return ([], x)
  
             
             
