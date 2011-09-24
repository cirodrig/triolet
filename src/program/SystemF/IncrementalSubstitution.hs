
{-# LANGUAGE FlexibleInstances #-}
module SystemF.IncrementalSubstitution
       (SM,
        Typ(..), CInst(..), DeCInst(..), TyPat(..), Pat(..), Alt(..), Fun(..),
        TypSM, PatSM, ExpSM, AltSM, FunSM, CInstSM, DeCInstSM,
        deferSubstitution,
        deferEmptySubstitution,
        addDeferredSubstitution,
        freshenHead,
        freshenFun,
        freshenAlt,
        discardSubstitution,
        applySubstitution,
        applySubstitutionFun,
        applySubstitutionAlt
       )
where

import Control.Monad
import SystemF.Syntax
import SystemF.MemoryIR
import SystemF.Rename
import Type.Type
import Type.Environment
import qualified Type.Rename as Rename
import qualified Type.Substitute as Substitute
import Type.Substitute(substitute, freshen, Substitutable(..))

-- | Type index for a 'Mem' expression wrapped in a substitution
data SM

type TypSM = Typ SM
type PatSM = Pat SM
type ExpSM = Exp SM
type AltSM = Alt SM
type FunSM = Fun SM
type CInstSM = CInst SM
type DeCInstSM = DeCInst SM

-- Types, patterns, and constructor instances are eagerly substituted
newtype instance Typ SM = TypSM {fromTypSM :: Type}
newtype instance CInst SM = CInstSM {fromCInstSM :: ConInst}
newtype instance DeCInst SM = DeCInstSM {fromDeCInstSM :: DeConInst}
newtype instance TyPat SM = TyPatSM {fromTyPatSM :: TyPatM}
newtype instance Pat SM = PatSM {fromPatSM :: PatM}

-- Functions and case alternatives contain un-substituted expressions
newtype instance Alt SM = AltSM {fromAltSM :: BaseAlt SM}
newtype instance Fun SM = FunSM {fromFunSM :: BaseFun SM}

-- | An expression wrapped in a substitution.
--   The substitution should be applied to the expression before 
--   inspecting the expression.
data instance Exp SM = ExpSM !Subst ExpM

instance Substitutable (Exp SM) where
  type Substitution (Exp SM) = Subst
  emptySubstitution _ = emptySubst
  isEmptySubstitution _ s = isEmptySubst s
  substituteWorker = addDeferredSubstitution

-- | Apply a substitution to an 'ExpM'.  The actual substitution is
--   performed later.
deferSubstitution :: Subst -> ExpM -> ExpSM
deferSubstitution = ExpSM

deferEmptySubstitution :: ExpM -> ExpSM
deferEmptySubstitution = deferSubstitution emptySubst

deferExp :: ExpM -> ExpSM
deferExp e = ExpSM emptySubst e

castType :: TypM -> TypSM
castType (TypM t) = TypSM t

castPat :: PatM -> PatSM
castPat = PatSM

castPats = map castPat

castTyPat :: TyPatM -> TyPat SM
castTyPat = TyPatSM

castTyPats = map castTyPat

deferFun :: FunM -> FunSM
deferFun (FunM (Fun inf ty_args args ret body)) =
  FunSM $
  Fun inf (castTyPats ty_args) (castPats args) (castType ret) (deferExp body)

deferAlt :: AltM -> AltSM
deferAlt (AltM (Alt (DeCInstM decon) params body)) =
  AltSM $ Alt (DeCInstSM decon) (castPats params) (deferExp body)

-- | Apply a substitution to an 'ExpSM'.  The actual substitution is
--   performed later.
addDeferredSubstitution :: EvalMonad m => Subst -> ExpSM -> m ExpSM
addDeferredSubstitution subst (ExpSM s e) = do
  s' <- subst `composeSubst` s
  return $ ExpSM s' e

-- | Freshen the outermost term, then convert the expression by
--   inserting empty substitutions
freshenAndDeferInnerTerms :: ExpM -> TypeEvalM (BaseExp SM)
freshenAndDeferInnerTerms e = liftM deferInnerTerms $ freshen e

-- | Convert the expression by inserting empty substitutions
deferInnerTerms :: ExpM -> BaseExp SM
deferInnerTerms (ExpM expression) =
  case expression
  of VarE inf v -> VarE inf v
     LitE inf l -> LitE inf l
     ConE inf (CInstM con) args ->
       ConE inf (CInstSM con) (map deferExp args)
     AppE inf op ts es ->
       AppE inf (deferExp op) (map castType ts) (map deferExp es)
     LamE inf f ->
       LamE inf (deferFun f)
     LetE inf p val body ->
       LetE inf (castPat p) (deferExp val) (deferExp body)
     LetfunE inf defs body ->
       LetfunE inf (fmap (mapDefiniens deferFun) defs) (deferExp body)
     CaseE inf scr alts ->
       CaseE inf (deferExp scr) (map deferAlt alts)
     ExceptE inf ty ->
       ExceptE inf ty
     CoerceE inf t1 t2 e ->
       CoerceE inf (castType t1) (castType t2) (deferExp e)

-- | Substitute the head term
freshenHead :: EvalMonad m => ExpSM -> m (BaseExp SM)
freshenHead (ExpSM s (ExpM expression)) = liftTypeEvalM $
  -- This is basically a copy of 'substituteWorker' for expressions,
  -- except that subexpressions are turned into 'ExpSM' terms.
  case expression
    of VarE inf v ->
         case lookupV v $ valueSubst s
         of Just (RenamedVar v')    -> return (VarE inf v')
            Just (SubstitutedVar e) -> freshenAndDeferInnerTerms e
            Nothing                 -> freshenAndDeferInnerTerms (ExpM expression)
       LitE inf l -> return $ LitE inf l
       ConE inf (CInstM con) args -> do
         con' <- substitute (typeSubst s) con
         let args' = map (deferSubstitution s) args
         return $ ConE inf (CInstSM con') args'
       AppE inf op ts es -> do
         ts' <- substitute (typeSubst s) ts
         let op' = deferSubstitution s op
         let es' = map (deferSubstitution s) es
         return $ AppE inf op' (map castType ts') es'
       LamE inf f -> do
         f' <- freshenFun s f
         return $ LamE inf f'
       LetE inf p val body -> do
         let val' = deferSubstitution s val
         substitutePatM s p $ \s' p' -> do
           let body' = deferSubstitution s' body
           return $ LetE inf (castPat p') val' body'
       LetfunE inf defs body ->
         substituteDefGroup freshenFun s defs $ \s' defs' -> do
           let body' = deferSubstitution s' body
           return $ LetfunE inf defs' body'
       CaseE inf scr alts -> do
         let scr' = deferSubstitution s scr
         alts' <- mapM (freshenAlt s) alts
         return $ CaseE inf scr' alts'
       ExceptE inf ty -> do
         ty' <- substitute (typeSubst s) ty
         return $ ExceptE inf ty'
       CoerceE inf (TypM t1) (TypM t2) e -> do
         t1' <- substitute (typeSubst s) t1
         t2' <- substitute (typeSubst s) t2
         let e' = deferSubstitution s e
         return $ CoerceE inf (TypSM t1') (TypSM t2') e'

freshenFun :: EvalMonad m => Subst -> FunM -> m FunSM
freshenFun s (FunM fun) = liftTypeEvalM $
  substituteTyPatMs s (funTyParams fun) $ \s' ty_params ->
  substitutePatMs s' (funParams fun) $ \s'' params -> do
    ret <- substitute (typeSubst s'') $ funReturn fun
    return $ FunSM $ Fun { funInfo = funInfo fun
                         , funTyParams = castTyPats ty_params
                         , funParams = castPats params
                         , funReturn = castType ret
                         , funBody = deferSubstitution s'' $ funBody fun}

freshenAlt :: EvalMonad m => Subst -> AltM -> m AltSM
freshenAlt s (AltM (Alt (DeCInstM decon) params body)) =
  substituteDeConInst (typeSubst s) decon $ \ts' decon' ->
  substitutePatMs (setTypeSubst ts' s) params $ \s' params' ->
  return $ AltSM $ Alt { altCon = DeCInstSM decon'
                       , altParams = castPats params'
                       , altBody = deferSubstitution s' body}

-- | Discard the substitution without applying it.
--
--   This leaves the expression in an undefined state with respect to
--   substitution and renaming.  In most cases, it's not a good idea.
discardSubstitution :: ExpSM -> ExpM
discardSubstitution (ExpSM _ e) = e

applySubstitution :: EvalMonad m => ExpSM -> m ExpM
applySubstitution (ExpSM s e) = substitute s e

applySubstitutionFun :: EvalMonad m => FunSM -> m FunM
applySubstitutionFun (FunSM (Fun inf ty_params params ret body)) = do
  body' <- applySubstitution body
  return $ FunM $ Fun inf (map fromTyPatSM ty_params) (map fromPatSM params) (TypM $ fromTypSM ret) body'

applySubstitutionAlt :: EvalMonad m => AltSM -> m AltM
applySubstitutionAlt (AltSM (Alt (DeCInstSM decon) params body)) = do
  body' <- applySubstitution body
  return $ AltM $ Alt (DeCInstM decon) (map fromPatSM params) body'
  
