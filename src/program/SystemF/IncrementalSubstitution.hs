
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
module SystemF.IncrementalSubstitution
       (SM,
        Pat(..), Alt(..), Fun(..),
        PatSM, ExpSM, AltSM, FunSM,
        substitutePatSM, substitutePatSMs,
        deferSubstitution,
        deferEmptySubstitution,
        addDeferredSubstitution,
        freshenHead,
        freshenFun,
        freshenAlt,
        freshenEnt,
        discardSubstitution,
        transformUnderSubstitution,
        applySubstitution,
        applySubstitutionFun,
        applySubstitutionAlt,
        freshenFullyExp
       )
where

import Prelude hiding(mapM)
import Control.Applicative
import Control.Monad hiding(mapM)
import Data.Traversable(mapM)

import Common.Identifier
import Common.Supply
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

type PatSM = Pat SM
type ExpSM = Exp SM
type AltSM = Alt SM
type FunSM = Fun SM

-- Types, patterns, and constructor instances are eagerly substituted
newtype instance Pat SM = PatSM {fromPatSM :: PatM}

-- Functions and case alternatives contain un-substituted expressions
newtype instance Alt SM = AltSM {fromAltSM :: BaseAlt SM}
newtype instance Fun SM = FunSM {fromFunSM :: BaseFun SM}

-- | An expression wrapped in a substitution.
--   The substitution should be applied to the expression before 
--   inspecting the expression.
data instance Exp SM = ExpSM !Subst ExpM

-- | 'PatSM' behaves like 'PatM'
substitutePatSM :: EvalMonad m =>
                   Subst -> PatSM -> (Subst -> PatSM -> m a) -> m a
substitutePatSM s pat k =
  substitutePatM s (fromPatSM pat) $ \s' p' -> k s' (PatSM p')

substitutePatSMs :: EvalMonad m =>
                    Subst -> [PatSM] -> (Subst -> [PatSM] -> m a) -> m a
substitutePatSMs = renameMany substitutePatSM

substituteMaybePatSM s Nothing k = k s Nothing
substituteMaybePatSM s (Just p) k = substitutePatSM s p $ \s' p' -> k s (Just p')


instance Substitutable (Exp SM) where
  type Substitution (Exp SM) = Subst
  substituteWorker = addDeferredSubstitution

instance Substitutable (Fun SM) where
  type Substitution (Fun SM) = Subst
  substituteWorker s (FunSM fun) = 
    -- Push the substitution down to the body of the function.  Defer further
    -- processing.
    substituteTyPats s (funTyParams fun) $ \s' ty_params ->
    substitutePatSMs s' (funParams fun) $ \s'' params -> do
      ret <- substitute (typeSubst s'') $ funReturn fun
      body <- substitute s'' $ funBody fun
      return $ FunSM $ Fun { funInfo = funInfo fun
                           , funTyParams = ty_params
                           , funParams = params
                           , funReturn = ret
                           , funBody = body}

instance Substitutable (Alt SM) where
  type Substitution (Alt SM) = Subst
  substituteWorker s (AltSM (Alt decon ty_ob params body)) =
    substituteDeConInst (typeSubst s) decon $ \type_subst decon' ->
    let s' = setTypeSubst type_subst s
    in substituteMaybePatSM s' ty_ob $ \s'' ty_ob' ->
       substitutePatSMs s'' params $ \s''' params' -> do
         body' <- substitute s''' body
         return $ AltSM $ Alt decon' ty_ob' params' body'

-- | Apply a substitution to an 'ExpM'.  The actual substitution is
--   performed later.
deferSubstitution :: Subst -> ExpM -> ExpSM
deferSubstitution = ExpSM

deferEmptySubstitution :: ExpM -> ExpSM
deferEmptySubstitution = deferSubstitution emptySubst

deferExp :: ExpM -> ExpSM
deferExp e = ExpSM emptySubst e

castPat :: PatM -> PatSM
castPat = PatSM

castPats = map castPat

deferFun :: FunM -> FunSM
deferFun (FunM (Fun inf ty_args args ret body)) =
  FunSM $ Fun inf ty_args (castPats args) ret (deferExp body)

deferAlt :: AltM -> AltSM
deferAlt (AltM (Alt decon ty_ob params body)) =
  AltSM $ Alt decon (fmap castPat ty_ob) (castPats params) (deferExp body)

-- | Apply a substitution to an 'ExpSM'.  The actual substitution is
--   performed later.
addDeferredSubstitution :: EvalMonad m =>
                           Subst -> ExpSM -> m ExpSM
addDeferredSubstitution subst (ExpSM s e) = do
  s' <- subst `composeSubst` s
  return $ ExpSM s' e

-- | Freshen the outermost term, then convert the expression by
--   inserting empty substitutions
freshenAndDeferInnerTerms :: BoxingMode b => ExpM -> TypeEvalM b (BaseExp SM)
freshenAndDeferInnerTerms e = liftM deferInnerTerms $ freshen e

-- | Convert the expression by inserting empty substitutions
deferInnerTerms :: ExpM -> BaseExp SM
deferInnerTerms (ExpM expression) =
  case expression
  of VarE inf v -> VarE inf v
     LitE inf l -> LitE inf l
     ConE inf con sps ty_ob args ->
       ConE inf con (map deferExp sps) (fmap deferExp ty_ob) (map deferExp args)
     AppE inf op ts es ->
       AppE inf (deferExp op) ts (map deferExp es)
     LamE inf f ->
       LamE inf (deferFun f)
     LetE inf p val body ->
       LetE inf (castPat p) (deferExp val) (deferExp body)
     LetfunE inf defs body ->
       LetfunE inf (fmap (mapDefiniens deferFun) defs) (deferExp body)
     CaseE inf scr sps alts ->
       CaseE inf (deferExp scr) (map deferExp sps) (map deferAlt alts)
     ExceptE inf ty ->
       ExceptE inf ty
     CoerceE inf t1 t2 e ->
       CoerceE inf t1 t2 (deferExp e)
     ArrayE inf ty es ->
       ArrayE inf ty (map deferExp es)

-- | Substitute the head term
freshenHead :: EvalMonad m => ExpSM -> m (BaseExp SM)
freshenHead (ExpSM s (ExpM expression)) = liftTypeEvalM $
  -- This is basically a copy of 'substituteWorker' for expressions,
  -- except that subexpressions are turned into 'ExpSM' terms.
  case expression
    of VarE inf v -> {-# SCC "freshenHead.VarE" #-}
         case lookupV v $ valueSubst s
         of Just (RenamedVar v')    -> return (VarE inf v')
            Just (SubstitutedVar e) -> freshenAndDeferInnerTerms e
            Nothing                 -> freshenAndDeferInnerTerms (ExpM expression)
       LitE inf l -> return $ LitE inf l
       ConE inf con ty_ob sps args -> do
         con' <- substitute (typeSubst s) con
         let ty_ob' = fmap (deferSubstitution s) ty_ob
         let sps' = fmap (deferSubstitution s) sps
         let args' = map (deferSubstitution s) args
         return $ ConE inf con' ty_ob' sps' args'
       AppE inf op ts es -> do
         ts' <- substitute (typeSubst s) ts
         let op' = deferSubstitution s op
         let es' = map (deferSubstitution s) es
         return $ AppE inf op' ts' es'
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
       CaseE inf scr sps alts -> do
         let scr' = deferSubstitution s scr
         let sps' = map (deferSubstitution s) sps
         alts' <- mapM (freshenAlt s) alts
         return $ CaseE inf scr' sps' alts'
       ExceptE inf ty -> do
         ty' <- substitute (typeSubst s) ty
         return $ ExceptE inf ty'
       CoerceE inf t1 t2 e -> do
         t1' <- substitute (typeSubst s) t1
         t2' <- substitute (typeSubst s) t2
         let e' = deferSubstitution s e
         return $ CoerceE inf t1' t2' e'
       ArrayE inf ty es -> do
         ty' <- substitute (typeSubst s) ty
         let es' = map (deferSubstitution s) es
         return $ ArrayE inf ty' es'

freshenFun :: EvalMonad m => Subst -> FunM -> m FunSM
freshenFun s (FunM fun) = liftTypeEvalM $
  substituteTyPats s (funTyParams fun) $ \s' ty_params ->
  substitutePatMs s' (funParams fun) $ \s'' params -> do
    ret <- substitute (typeSubst s'') $ funReturn fun
    return $ FunSM $ Fun { funInfo = funInfo fun
                         , funTyParams = ty_params
                         , funParams = castPats params
                         , funReturn = ret
                         , funBody = deferSubstitution s'' $ funBody fun}

freshenAlt :: EvalMonad m => Subst -> AltM -> m AltSM
freshenAlt s (AltM (Alt decon ty_ob params body)) =
  substituteDeConInst (typeSubst s) decon $ \ts' decon' ->
  substituteMaybePatM (setTypeSubst ts' s) ty_ob $ \s' ty_ob' ->
  substitutePatMs s' params $ \s'' params' ->
  return $ AltSM $ Alt { altCon = decon'
                       , altTyObject = fmap castPat ty_ob'
                       , altParams = castPats params'
                       , altBody = deferSubstitution s'' body}

freshenConstant :: EvalMonad m => Subst -> Constant Mem -> m (Constant SM)
freshenConstant s (Constant inf ty e) = do
  ty' <- substitute (typeSubst s) ty
  let e' = deferSubstitution s e
  return $ Constant inf ty' e'

freshenEnt :: EvalMonad m => Subst -> Ent Mem -> m (Ent SM)
freshenEnt s (FunEnt f) = FunEnt `liftM` freshenFun s f
freshenEnt s (DataEnt c) = DataEnt `liftM` freshenConstant s c

-- | Discard the substitution without applying it.
--
--   This leaves the expression in an undefined state with respect to
--   substitution and renaming.  In most cases, it's not a good idea.
discardSubstitution :: ExpSM -> ExpM
discardSubstitution (ExpSM _ e) = e

-- | Apply a transformation to an expression without substituting in it. 
--
--   The transformation should ignore variable names and should not alter
--   variable scopes; otherwise the results will be unpredictable.
transformUnderSubstitution :: (ExpM -> ExpM) -> ExpSM -> ExpSM
transformUnderSubstitution f (ExpSM subst e) = ExpSM subst (f e)

applySubstitution :: EvalMonad m => ExpSM -> m ExpM
applySubstitution (ExpSM s e) = substitute s e

applySubstitutionFun :: EvalMonad m => FunSM -> m FunM
applySubstitutionFun (FunSM (Fun inf ty_params params ret body)) = do
  body' <- applySubstitution body
  return $ FunM $ Fun inf ty_params (map fromPatSM params) ret body'

applySubstitutionAlt :: EvalMonad m => AltSM -> m AltM
applySubstitutionAlt (AltSM (Alt decon ty_ob params body)) = do
  body' <- applySubstitution body
  return $ AltM $ Alt decon (fmap fromPatSM ty_ob) (map fromPatSM params) body'
  
-- | Eliminate name shadowing in an expression.  The expression is traversed, 
--   and any shadowed names are renamed.
--
--   Since this function inspects every subexpression, it should be used
--   sparingly.
freshenFullyExp :: EvalMonad m => ExpSM -> m ExpM
freshenFullyExp e = liftTypeEvalM $ freshenFullyExp' e

freshenFullyExp' :: forall b. BoxingMode b => ExpSM -> TypeEvalM b ExpM
freshenFullyExp' expression = do
  expression' <- freshenHead expression
  case expression' of
    VarE inf v -> return $ ExpM $ VarE inf v
    LitE inf l -> return $ ExpM $ LitE inf l
    ConE inf con ty_ob sps args ->
      ExpM <$> (ConE inf con <$> mapM recurse ty_ob <*> mapM recurse sps <*> mapM recurse args)
    AppE inf op ts es ->
      ExpM <$> (AppE inf <$> recurse op <*> pure ts <*> mapM recurse es)
    LamE inf f ->
      ExpM <$> (LamE inf <$> freshenFullyFun' f)
    LetE inf p val body ->
      let p' = fromPatSM p
      in ExpM <$> (LetE inf p' <$> recurse val <*> assumePatM p' (recurse body))
    LetfunE inf defs body -> do
      let freshen_defs = mapM (mapMDefiniens freshenFullyFun') defs
          freshen_body = recurse body
          assume_defs :: forall a. TypeEvalM b a -> TypeEvalM b a
          assume_defs m = foldr assume_def m (defGroupMembers defs)
            where
              assume_def def m =
                let FunSM f = definiens def
                    ty = forallType [b | TyPat b <- funTyParams f] $
                         funType (map (patMType . fromPatSM) $ funParams f) (funReturn f)
                in assume (definiendum def) ty m

      defs' <- case defs
               of NonRec _ -> freshen_defs
                  Rec _    -> assume_defs freshen_defs
      body' <- assume_defs freshen_body
      return $ ExpM $ LetfunE inf defs' body'
    CaseE inf scr sps alts ->
      ExpM <$> (CaseE inf <$> recurse scr <*> mapM recurse sps <*> mapM freshenFullyAlt' alts)
    ExceptE inf ty -> return $ ExpM $ ExceptE inf ty
    CoerceE inf t1 t2 e ->
      ExpM <$> (CoerceE inf t1 t2 <$> freshenFullyExp' e)
    ArrayE inf t es ->
      ExpM <$> (ArrayE inf t <$> mapM freshenFullyExp' es)
  where
    recurse e = freshenFullyExp' e

-- | Eliminate name shadowing in a function body.  The function parameters
--   have already been renamed.
freshenFullyFun' :: forall b. BoxingMode b => FunSM -> TypeEvalM b FunM
freshenFullyFun' (FunSM f) =
  assumeTyPats (funTyParams f) $ assumePatMs (map fromPatSM $ funParams f) $ do
    body <- freshenFullyExp' $ funBody f
    return $ FunM $ Fun { funInfo = funInfo f
                        , funTyParams = funTyParams f
                        , funParams = map fromPatSM $ funParams f
                        , funReturn = funReturn f
                        , funBody = body}

freshenFullyAlt' :: forall b. BoxingMode b => AltSM -> TypeEvalM b AltM
freshenFullyAlt' (AltSM alt) =
  assumeBinders (deConExTypes $ altCon alt) $
  assumeMaybePatM (fmap fromPatSM $ altTyObject alt) $ do
  assumePatMs (map fromPatSM $ altParams alt) $ do
    body <- freshenFullyExp' $ altBody alt
    return $ AltM $ Alt { altCon = altCon alt
                        , altTyObject = fmap fromPatSM $ altTyObject alt
                        , altParams = map fromPatSM $ altParams alt
                        , altBody = body}