
{-# LANGUAGE FlexibleInstances, FlexibleContexts, StandaloneDeriving, GeneralizedNewtypeDeriving #-}
module SystemF.Rename
       (freshen,
        renamePatM,
        renamePatMs,
        substitutePatM,
        substitutePatMs,
        freshenPatM,
        freshenPatMs,
        freshenFunValueParams,
        renameTyPatM,
        renameTyPatMs,
        substituteTyPatM,
        substituteTyPatMs,
        freshenTyPatM,
        freshenTyPatMs,
        renameDeConInst,
        freshenDeConInst,
        renameDefM,
        renameDefGroup,
        freshenModuleFully,
        checkForShadowingExp,
        checkForShadowingExpSet,
        checkForShadowingExpHere,
        checkForShadowingModule)
where

import Prelude hiding(mapM)
import Control.Applicative
import Control.Monad hiding(mapM)
import Control.Monad.Reader hiding(mapM)
import qualified Data.IntSet as IntSet
import Data.List
import Data.Maybe
import Data.Monoid
import qualified Data.IntMap as IntMap
import qualified Data.Set as Set
import Data.Traversable
import Debug.Trace

import Common.Error
import Common.Identifier
import Common.MonadLogic
import Common.Supply
import SystemF.Syntax
import SystemF.MemoryIR
import SystemF.PrintMemoryIR
import Type.Environment
import Type.Type
import Type.Rename

type VarPredicate m = Var -> m Bool

renameMany :: (st -> a -> (st -> a -> b) -> b)
           -> st -> [a] -> (st -> [a] -> b) -> b
renameMany f rn (x:xs) k =
  f rn x $ \rn' x' -> renameMany f rn' xs $ \rn'' xs' -> k rn'' (x':xs')

renameMany _ rn [] k = k rn []

-- | Apply a renaming to a type pattern. If necessary, rename the pattern
--   variable to avoid name shadowing.
renameTyPatM :: Renaming -> TyPatM -> (Renaming -> TyPatM -> a) -> a
renameTyPatM rn (TyPatM binder) k =
  renameBinding rn binder $ \rn' binder' ->
  k rn' (TyPatM binder')

renameTyPatMs = renameMany renameTyPatM

-- | Apply a renaming to a pattern.  If necessary, rename the pattern
--   variable to avoid name shadowing.
renamePatM :: Renaming -> PatM -> (Renaming -> PatM -> a) -> a
renamePatM rn (PatM binding uses) k =
  renameBinding rn binding $ \rn' binding' ->
  k rn' (PatM binding' (rename rn uses))

renamePatMs :: Renaming -> [PatM] -> (Renaming -> [PatM] -> a) -> a
renamePatMs = renameMany renamePatM

renameDeConInst :: Renaming -> DeCInstM -> (Renaming -> DeCInstM -> a) -> a
renameDeConInst rn (DeCInstM decon) k =
  case decon
  of VarDeCon op ty_args ex_types ->
       let ty_args' = rename rn ty_args
       in renameBindings rn ex_types $ \rn' ex_types' ->
          k rn' (DeCInstM (VarDeCon op ty_args' ex_types'))
     TupleDeCon ty_args ->
       let ty_args' = rename rn ty_args
       in k rn (DeCInstM (TupleDeCon ty_args'))

-- | Freshen a type variable binding
freshenTyPatM :: (Monad m, Supplies m VarID) =>
                 VarPredicate m -> TyPatM -> m (TyPatM, Renaming)
freshenTyPatM p pat@(TyPatM (v ::: ty)) = do
  should_freshen <- p v
  if should_freshen
    then do
      v' <- newClonedVar v
      return (TyPatM (v' ::: ty), singletonRenaming v v')
    else return (pat, mempty)

-- | Freshen a list of type variable bindings.  None of the bindings refer to
--   a variable bound by another member of the list.
freshenTyPatMs :: (Monad m, Supplies m VarID) =>
                  VarPredicate m -> [TyPatM] -> m ([TyPatM], Renaming)
freshenTyPatMs p pats = do
  (pats', assocs) <- mapAndUnzipM freshen_pattern pats
  return (pats', renaming $ catMaybes assocs)
  where
    freshen_pattern pat@(TyPatM (v ::: ty)) = do
      should_freshen <- p v
      if should_freshen
        then do
          v' <- newClonedVar v
          return (TyPatM (v' ::: ty), Just (v, v'))
        else return (pat, Nothing)

-- | Freshen a variable binding that is /not/ a local variable binding.
freshenPatM :: (Monad m, Supplies m VarID) =>
               VarPredicate m -> PatM -> m (PatM, Renaming)
freshenPatM p pat = do 
  (pat', assocs) <- freshenPattern p pat
  return (pat', maybe mempty (uncurry singletonRenaming) assocs)

-- | Freshen a list of variable bindings. 
--   There must not be any local variable bindings in the list.
--   None of the bindings may refer to a variable bound by another member of
--   the list. 
freshenPatMs :: (Monad m, Supplies m VarID) =>
                VarPredicate m -> [PatM] -> m ([PatM], Renaming)
freshenPatMs p pats = do
  (pats', assocs) <- mapAndUnzipM (freshenPattern p) pats
  return (pats', renaming $ catMaybes assocs)

freshenPattern p pat@(PatM (v ::: param_ty) uses) = do
  should_freshen <- p v
  if should_freshen
    then do
      v' <- newClonedVar v
      return (PatM (v' ::: param_ty) uses, Just (v, v'))
    else return (pat, Nothing)

freshenDeConInst :: (Monad m, Supplies m VarID) =>
                    VarPredicate m -> DeCInstM -> m (DeCInstM, Renaming)
freshenDeConInst p (DeCInstM decon) =
  case decon
  of VarDeCon op ty_args ex_types -> do
       let old_vars = [v | v ::: _ <- ex_types]
       new_vars <- mapM newClonedVar old_vars
       let new_ex_types = [v ::: t | (v, _ ::: t) <- zip new_vars ex_types]
           rn = renaming $ zip old_vars new_vars
       return (DeCInstM (VarDeCon op ty_args new_ex_types), rn)
     TupleDeCon ty_args ->
       -- No bound variables
       return (DeCInstM decon, mempty)

-- | Apply a substitution to a type pattern
substituteTyPatM :: EvalMonad m =>
                    Substitution -> TyPatM
                 -> (Substitution -> TyPatM -> m a)
                 -> m a
substituteTyPatM s (TyPatM binder) k =
  substituteBinding s binder $ \s' binder' -> k s' (TyPatM binder')

substituteTyPatMs :: EvalMonad m =>
                     Substitution -> [TyPatM]
                  -> (Substitution -> [TyPatM] -> m a)
                  -> m a
substituteTyPatMs = renameMany substituteTyPatM
  
-- | Apply a substitution to a pattern.
--   Substitutions only operate on type variables, so the pattern-bound
--   variable is unchanged.  Also, since no type variables are bound, the 
--   substitution is unchanged.
substitutePatM :: EvalMonad m =>
                  Substitution -> PatM -> m PatM
substitutePatM s (PatM (v ::: t) uses) = do
  t' <- substitute s t
  uses' <- substitute s uses
  return $ PatM (v ::: t') uses'

-- | An interface to 'substitutePatM' that resembles the interface to
--   'renamePatM'.
substitutePatM' :: EvalMonad m =>
                  Substitution -> PatM -> (Substitution -> PatM -> m a) -> m a
substitutePatM' s p k = do  
  p' <- substitutePatM s p
  k s p'

substitutePatMs :: EvalMonad m =>
                   Substitution -> [PatM] -> m [PatM]
substitutePatMs s ps = mapM (substitutePatM s) ps

substitutePatMs' :: EvalMonad m =>
                    Substitution -> [PatM]
                 -> (Substitution -> [PatM] -> m a)
                 -> m a
substitutePatMs' = renameMany substitutePatM'

substituteDeConInst :: EvalMonad m =>
                       Substitution -> DeCInstM
                    -> (Substitution -> DeCInstM -> m a)
                    -> m a 
substituteDeConInst s (DeCInstM decon) k =
  case decon
  of VarDeCon con ty_args ex_types -> do
       ty_args' <- mapM (substitute s) ty_args
       renameMany substituteBinding s ex_types $ \s' ex_types' ->
         k s' (DeCInstM $ VarDeCon con ty_args' ex_types')
     TupleDeCon ty_args -> do
       ty_args' <- mapM (substitute s) ty_args
       k s (DeCInstM $ TupleDeCon ty_args')
       
instance Renameable (Typ Mem) where
  rename rn (TypM t) = TypM $ rename rn t
  freshen p (TypM t) = liftM TypM $ freshen p t
  freeVariables (TypM t) = freeVariables t

deriving instance Renameable (CInst Mem)

instance Renameable ConInst where
  rename rn (VarCon con ty_args ex_types) =
    let ty_args' = rename rn ty_args
        ex_types' = rename rn ex_types
    in VarCon con ty_args' ex_types'
  rename rn (TupleCon ty_args) =
    let ty_args' = rename rn ty_args
    in TupleCon ty_args'

  -- No variables bound here
  freshen p e = return e
  
  freeVariables (VarCon _ ty_args ex_types) =
    freeVariables (ty_args ++ ex_types)

  freeVariables (TupleCon ty_args) =
    freeVariables ty_args

instance Renameable (Exp Mem) where
  rename rn (ExpM expression) = ExpM $
    case expression
    of VarE inf v ->
         case renameVar v rn
         of Just v' -> VarE inf v'
            Nothing -> expression
       LitE {} -> expression
       ConE inf op args ->
         ConE inf (rename rn op) (rename rn args)
       AppE inf op ts es ->
         AppE inf (rename rn op) (map (rename rn) ts) (map (rename rn) es)
       LamE inf f ->
         LamE inf (rename rn f)
       LetE inf p val body ->
         renamePatM rn p $ \rn' p' ->
         LetE inf p' (rename rn val) (rename rn' body)
       LetfunE inf defs body ->
         renameDefGroup rn defs $ \rn' defs' ->
         LetfunE inf defs' (rename rn' body)
       CaseE inf scr alts ->
         CaseE inf (rename rn scr) (map (rename rn) alts)
       ExceptE inf rty ->
         ExceptE inf (rename rn rty)
       CoerceE inf t1 t2 e ->
         CoerceE inf (rename rn t1) (rename rn t2) (rename rn e)

  freshen p (ExpM expression) =
    case expression
    of LetE inf pat rhs body -> do
         (pat', rn) <- freshenPatM p pat
         let body' = rename rn body
         return $ ExpM $ LetE inf pat' rhs body'

       LetfunE inf (NonRec def) body -> do
         let v = definiendum def
         should_freshen <- p v
         (body', def') <-
           if should_freshen
           then do
             v' <- newClonedVar v
             return (rename (singletonRenaming v v') body,
                     def {definiendum = v'})
           else return (body, def)
         return $ ExpM $ LetfunE inf (NonRec def') body'

       LetfunE inf (Rec defs) body -> do
         let def_vars = map definiendum defs
         renamed_vars <- mapM newClonedVar def_vars
         
         -- Rename everything
         let rn = renaming $ zip def_vars renamed_vars
             defs' = [d {definiendum = v, definiens = rename rn $ definiens d}
                     | (v, d) <- zip renamed_vars defs]
             body' = rename rn body
         return $ ExpM $ LetfunE inf (Rec defs') body'

       _ -> return (ExpM expression)

  freeVariables (ExpM expression) =
    case expression
    of VarE _ v -> Set.singleton v
       LitE _ _ -> Set.empty
       ConE _ op args -> freeVariables op `Set.union` freeVariables args
       AppE _ op ty_args args -> Set.union (freeVariables op) $
                                 Set.union (freeVariables ty_args) $
                                 freeVariables args
       LamE _ f -> freeVariables f
       LetE _ pat rhs body ->
         let ty_fv = freeVariables $ patMType pat
             rhs_fv = freeVariables rhs
             body_fv = Set.delete (patMVar pat) $ freeVariables body
         in ty_fv `Set.union` rhs_fv `Set.union` body_fv
       LetfunE _ (NonRec def) body ->
         let body_fv = freeVariables body
             fn_fv = freeVariables $ definiens def
         in Set.union (Set.delete (definiendum def) body_fv) fn_fv
       LetfunE _ (Rec defs) body ->
         let local_functions = map definiendum defs
             fn_fv = Set.unions $ map (freeVariables . definiens) defs
             body_fv = freeVariables body
         in foldr Set.delete (Set.union fn_fv body_fv) local_functions
       CaseE _ scr alts ->
         freeVariables scr `Set.union` freeVariables alts
       ExceptE _ rty ->
         freeVariables rty
       CoerceE _ t1 t2 e ->
         freeVariables t1 `Set.union` freeVariables t2 `Set.union` freeVariables e

instance Renameable (Alt Mem) where
  rename rn (AltM (Alt con params body)) =
    renameDeConInst rn con $ \rn' con' ->
    renamePatMs rn' params $ \rn'' params' ->
    AltM $ Alt con' params' (rename rn'' body)

  freshen p (AltM (Alt con params body)) = do
    (con', rn1) <- freshenDeConInst p con
    renamePatMs rn1 params $ \rn2 params' -> do
      (params'', params_renaming) <- freshenPatMs p params'
      let rn3 = params_renaming `mappend` rn2
      let body' = rename rn3 body
      return $ AltM $ Alt con' params'' body'

  freeVariables (AltM (Alt (DeCInstM decon) params body)) = let
    -- Get free variables from body; remove pattern variables
    pattern_bound = map patMVar params
    body_fv = foldr Set.delete (freeVariables body) pattern_bound
    pattern_fv = freeVariables (map patMType params)
    
    -- Add free variables from pattern types; remove existential variables
    exvars = [v | v ::: _ <- deConExTypes decon]
    body_pattern_fv =
      foldr Set.delete (Set.union body_fv pattern_fv) exvars
    
    -- Add free variables from type parameters
    in freeVariables (deConTyArgs decon) `Set.union` body_pattern_fv

instance Renameable (Fun Mem) where
  rename rn (FunM fun) =
    renameTyPatMs rn (funTyParams fun) $ \rn' ty_params -> 
    renamePatMs rn' (funParams fun) $ \rn'' params ->
    let ret = rename rn'' $ funReturn fun
        body = rename rn'' $ funBody fun
    in FunM $ Fun { funInfo = funInfo fun
                  , funTyParams = ty_params
                  , funParams = params
                  , funReturn = ret
                  , funBody = body}
  
  freshen p (FunM fun) = do
    (ty_params, ty_renaming) <- freshenTyPatMs p $ funTyParams fun
    renamePatMs ty_renaming (funParams fun) $ \ty_renaming' params -> do
      (rn_params, param_renaming) <- freshenPatMs p params
      let renaming = param_renaming `mappend` ty_renaming'
      let ret = rename renaming $ funReturn fun
          body = rename renaming $ funBody fun
      return $ FunM $ Fun { funInfo = funInfo fun
                          , funTyParams = ty_params
                          , funParams = rn_params
                          , funReturn = ret
                          , funBody = body}

  freeVariables (FunM fun) = do
    let typat_fv = Set.unions $
                   map freeVariables [t | TyPatM (_ ::: t) <- funTyParams fun]
        typat_vars = [v | TyPatM (v ::: _) <- funTyParams fun]
          
        -- Get free variables from patterns; remove type parameter variables
        pat_fv1 = Set.unions $
                  map (freeVariables . patMType) $ funParams fun
        pat_fv = foldr Set.delete pat_fv1 typat_vars

        pat_vars = map patMVar $ funParams fun
        
        -- Get free variables from body and return type;
        -- remove existential variables and fields
        return_fv = freeVariables $ funReturn fun
        body_fv = freeVariables $ funBody fun
        return_and_body_fv = foldr Set.delete (Set.union return_fv body_fv)
                             (typat_vars ++ pat_vars)
      in typat_fv `Set.union` pat_fv `Set.union` return_and_body_fv

renameDefM rn def = def {definiens = rename rn $ definiens def}

renameDefGroup r (NonRec d) k = 
  let group = NonRec $ renameDefM r d
      r' = R $ IntMap.delete (fromIdent $ varID $ definiendum d) $ unR r
  in k r' group

renameDefGroup r (Rec defs) k =
  let local_names = map definiendum defs
      r' = R $ foldr (IntMap.delete . fromIdent . varID) (unR r) local_names
  in k r' (Rec $ map (mapDefiniens (rename r')) defs)

instance Substitutable (Typ Mem) where
  substitute s (TypM t) = TypM `liftM` substitute s t

deriving instance Substitutable (CInst Mem)

instance Substitutable ConInst where
  substitute s (VarCon op ty_args ex_types) =
    VarCon op `liftM` mapM (substitute s) ty_args `ap` mapM (substitute s) ex_types

  substitute s (TupleCon ty_args) =
    TupleCon `liftM` mapM (substitute s) ty_args

instance Substitutable (Exp Mem) where
  substitute s (ExpM expression) =
    case expression
    of VarE inf v ->
         case substituteVar v s
         of Just _ ->
              internalError "Exp Mem.substitute: type substituted for variable"
            Nothing -> return (ExpM expression)
       LitE {} -> return (ExpM expression)
       ConE inf con args -> do
         con' <- substitute s con
         args' <- mapM (substitute s) args
         return $ ExpM $ ConE inf con' args'
       AppE inf op ts es -> do
         op' <- substitute s op
         ts' <- mapM (substitute s) ts
         es' <- mapM (substitute s) es
         return $ ExpM $ AppE inf op' ts' es'
       LamE inf f -> do
         f' <- substitute s f
         return $ ExpM $ LamE inf f'
       LetE inf p val body -> do
         val' <- substitute s val
         substitutePatM' s p $ \s' p' -> do
           body' <- substitute s' body
           return $ ExpM $ LetE inf p' val' body'
       LetfunE inf defs body -> do
         -- For simplicity, always rename the definition group 
         ExpM (LetfunE inf defs' body') <-
           freshenPure (const True) (ExpM expression)
         defs'' <- mapM (mapMDefiniens (substitute s)) defs'
         body'' <- substitute s body'
         return $ ExpM $ LetfunE inf defs'' body''
       CaseE inf scr alts -> do
         scr' <- substitute s scr
         alts' <- mapM (substitute s) alts
         return $ ExpM $ CaseE inf scr' alts'
       ExceptE inf ty -> do
         ty' <- substitute s ty
         return $ ExpM $ ExceptE inf ty'
       CoerceE inf (TypM t1) (TypM t2) e -> do
         t1' <- substitute s t1
         t2' <- substitute s t2
         e' <- substitute s e
         return $ ExpM $ CoerceE inf (TypM t1') (TypM t2') e'

instance Substitutable (Alt Mem) where
  substitute s (AltM (Alt con params body)) =
    substituteDeConInst s con $ \s' con' ->
    substitutePatMs' s' params $ \s'' params' -> do
      body' <- substitute s'' body
      return $ AltM $ Alt con' params' body'

instance Substitutable (Fun Mem) where
  substitute s (FunM fun) =
    substituteTyPatMs s (funTyParams fun) $ \s' ty_params ->
    substitutePatMs' s' (funParams fun) $ \s'' params -> do
      body <- substitute s'' $ funBody fun
      ret <- substitute s'' $ funReturn fun
      return $ FunM $ Fun { funInfo = funInfo fun
                          , funTyParams = ty_params
                          , funParams = params
                          , funReturn = ret
                          , funBody = body}

-- | Rename value-level function parameters if they conflict with names that 
--   are already present in the environment.  Ignore type-level variables.
freshenFunValueParams :: (Supplies m VarID, TypeEnvMonad m) => FunM -> m FunM
freshenFunValueParams (FunM f) =
  renameMany freshen_if_bound mempty (funParams f) $ \rn params ->
  let (body, ret) =
        if isIdRenaming rn
        then (funBody f, funReturn f)
        else (rename rn $ funBody f, rename rn $ funReturn f)
  in return $ FunM $ Fun { funInfo     = funInfo f
                         , funTyParams = funTyParams f
                         , funParams   = params
                         , funReturn   = ret
                         , funBody     = body}
  where
    freshen_if_bound rn pat@(PatM (v ::: t) u) k = do
      tenv <- getTypeEnv
      case lookupType v tenv of
        Nothing -> k rn pat
        Just _ -> do
          v' <- newClonedVar v
          let rn' = insertRenaming v v' rn 
          k rn' (PatM (v' ::: t) u)

-------------------------------------------------------------------------------
-- Recursive renaming.  All names bound in an expression are renamed to fresh
-- names.

type Freshen a = ReaderT Renaming FreshVarM a

freshenVar :: Var -> (Var -> Freshen a) -> Freshen a
freshenVar v k = do
  v' <- lift $ newClonedVar v
  local (insertRenaming v v') $ k v'

lookupVar :: Var -> Freshen Var
lookupVar v = asks (flip rename v)

-- | Apply the current renaming to the type.  It's unnecessary to rename
--   variables bound inside the type.
freshenType ty = ReaderT $ \rn -> return $ rename rn ty

freshenDmd dmd = ReaderT $ \rn -> return $ rename rn dmd

freshenBinder (v ::: ty) k = do
  ty' <- freshenType ty
  freshenVar v $ \v' -> k (v' ::: ty')

freshenTyParam (TyPatM b) k = freshenBinder b $ \b' -> k (TyPatM b')

freshenParam (PatM (v ::: ty) dmd) k = do
  ty' <- freshenType ty
  dmd' <- freshenDmd dmd
  freshenVar v $ \v' -> k (PatM (v' ::: ty') dmd')

freshenConInst con = ReaderT $ \rn -> return $ rename rn con

freshenExp (ExpM expression) = ExpM <$>
  case expression
  of VarE inf v -> VarE inf <$> lookupVar v
     LitE _ _ -> return expression
     ConE inf con args ->
       ConE inf <$> freshenConInst con <*> mapM freshenExp args
     AppE inf op ty_args args ->
       AppE inf <$>
       freshenExp op <*>
       mapM freshenType ty_args <*>
       mapM freshenExp args
     LamE inf f -> LamE inf <$> freshenFun f
     LetE inf binder rhs body -> do
       rhs' <- freshenExp rhs
       freshenParam binder $ \binder' -> do
         body' <- freshenExp body
         return $ LetE inf binder' rhs' body'
     
     LetfunE inf defs body ->
       freshenDefGroup defs $ \defs' -> LetfunE inf defs' <$> freshenExp body

     CaseE inf scr alts ->
       CaseE inf <$> freshenExp scr <*> mapM freshenAlt alts

     ExceptE inf ty -> ExceptE inf <$> freshenType ty
     
     CoerceE inf t1 t2 e ->
       CoerceE inf <$> freshenType t1 <*> freshenType t2 <*> freshenExp e

freshenAlt (AltM (Alt decon params body)) =
  freshen_decon $ \decon' -> do
    withMany freshenParam params $ \params' -> do
      body' <- freshenExp body
      return $ AltM (Alt decon' params' body')
  where
    freshen_decon k =
      case decon
      of DeCInstM (VarDeCon con ty_args ex_types) -> do
           ty_args' <- mapM freshenType ty_args
           withMany freshenBinder ex_types $ \ex_types' ->
             k (DeCInstM (VarDeCon con ty_args' ex_types'))
         DeCInstM (TupleDeCon ty_args) -> do
           ty_args' <- mapM freshenType ty_args
           k (DeCInstM (TupleDeCon ty_args'))

freshenFun (FunM fun) = do
  withMany freshenTyParam (funTyParams fun) $ \ty_params ->
    withMany freshenParam (funParams fun) $ \params -> do
      body <- freshenExp $ funBody fun
      ret <- freshenType $ funReturn fun
      return $ FunM $ fun { funTyParams = ty_params
                          , funParams = params
                          , funReturn = ret
                          , funBody = body}

freshenDefGroup :: DefGroup (Def Mem)
                -> (DefGroup (Def Mem) -> Freshen a) -> Freshen a
freshenDefGroup (NonRec def) k = do
  f' <- freshenFun $ definiens def
  freshenVar (definiendum def) $ \v' ->
    let def' = def {definiendum = v', definiens = f'}
    in k (NonRec def')

freshenDefGroup (Rec defs) k = do
  withMany freshenVar (map definiendum defs) $ \vs' -> do
    defs' <- zipWithM freshen_def vs' defs 
    k (Rec defs')
  where
    freshen_def new_v def = do
      f' <- freshenFun $ definiens def
      return $ def {definiendum = new_v, definiens = f'}

-- | Rename all bound variables in a module
--   (except those bound inside types or demand annotations).
freshenModuleFully :: Module Mem -> FreshVarM (Module Mem)
freshenModuleFully (Module modname imports groups exports) =
  runReaderT freshen_module mempty
  where
    freshen_module = do
      (groups', exports') <- freshen_defs id groups
      return $ Module modname imports groups' exports'

    freshen_defs hd (g:gs) =
      freshenDefGroup g $ \g' -> freshen_defs (hd . (g':)) gs

    freshen_defs hd [] = do
      exports' <- mapM freshen_export exports
      return (hd [], exports')
    
    freshen_export e = do
      f <- freshenFun $ exportFunction e
      return $ e {exportFunction = f}

-------------------------------------------------------------------------------

-- | Search for instances of name shadowing in the expression.
--   If found, raise an exception.
checkForShadowingExp :: TypeEnv -> ExpM -> ()
checkForShadowingExp tenv e =
  checkForShadowingExpSet (IntMap.keysSet $ getAllTypes tenv) e

checkForShadowingExpSet :: CheckForShadowing ExpM
checkForShadowingExpSet in_scope e =
  case fromExpM e
  of VarE {} -> ()
     LitE {} -> ()
     ConE _ (CInstM con) args ->
       checkForShadowingConSet in_scope con `seq`
       continues args
     AppE _ op ty_args args ->
       continue op `seq`
       (foldr seq () $ map (checkForShadowingSet in_scope . fromTypM) ty_args) `seq`
       continues args
     LamE _ f ->
       checkForShadowingFunSet in_scope f
     LetE _ pat rhs body ->
       assertVarIsUndefined in_scope (patMVar pat) `seq`
       continue rhs `seq`
       checkForShadowingSet in_scope (patMType pat) `seq`
       checkForShadowingExpSet (insert (patMVar pat) in_scope) body
     LetfunE _ defs body ->
       checkForShadowingGroupSet checkForShadowingExpSet body in_scope defs
     CaseE _ scr alts ->
       continue scr `seq`
       (foldr seq () $ map (checkForShadowingAltSet in_scope) alts)
     ExceptE _ ty ->
       checkForShadowingSet in_scope ty
     CoerceE _ t1 t2 body ->
       checkForShadowingSet in_scope (fromTypM t1) `seq`
       checkForShadowingSet in_scope (fromTypM t2) `seq`
       continue body
  where
    continue e = checkForShadowingExpSet in_scope e
    continues es = foldr seq () $ map continue es
    insert v scope = IntSet.insert (fromIdent $ varID v) scope

checkForShadowingGroupSet :: CheckForShadowing a -> a
                          -> CheckForShadowing (DefGroup (Def Mem))
checkForShadowingGroupSet check body in_scope defs =
  let definienda = map definiendum $ defGroupMembers defs
      definientia = map definiens $ defGroupMembers defs
      augmented_scope = inserts definienda in_scope
      
      -- Determine which variables are in scope over the function
      -- definitions 
      local_scope =
        case defs
        of NonRec _ -> in_scope
           Rec _    -> augmented_scope
  in assertVarsAreUndefined in_scope definienda `seq`
     (foldr seq (check augmented_scope body) $
      map (checkForShadowingFunSet local_scope) definientia)
  where
    insert v scope = IntSet.insert (fromIdent $ varID v) scope
    inserts vs scope = foldr insert scope vs


checkForShadowingConSet :: CheckForShadowing ConInst
checkForShadowingConSet in_scope con =
  foldr seq () $ map (checkForShadowingSet in_scope) (conTypes con)

checkForShadowingDeConSet :: CheckForShadowing DeConInst
checkForShadowingDeConSet in_scope con =
  assertVarsAreUndefined in_scope [v | v ::: _ <- deConExTypes con] `seq`
  (foldr seq () $ map (checkForShadowingSet in_scope) types)
  where
    types = deConTyArgs con ++ [k | _ ::: k <- deConExTypes con]

checkForShadowingFunSet :: CheckForShadowing FunM
checkForShadowingFunSet in_scope (FunM (Fun _ typarams params return body)) =
  let ty_vars = [a | TyPatM (a ::: _) <- typarams]
      kinds = [k | TyPatM (_ ::: k) <- typarams]
      ty_scope = inserts ty_vars in_scope
      param_vars = map patMVar params
      param_types = map patMType params
      body_scope = inserts param_vars ty_scope
  in (foldr seq () $ map (checkForShadowingSet in_scope) kinds) `seq`
     assertVarsAreUndefined in_scope ty_vars `seq`
     (foldr seq () $ map (checkForShadowingSet ty_scope) param_types) `seq` 
     assertVarsAreUndefined ty_scope param_vars `seq`
     checkForShadowingSet body_scope (fromTypM return) `seq`
     checkForShadowingExpSet body_scope body
  where
    insert v scope = IntSet.insert (fromIdent $ varID v) scope
    inserts vs scope = foldr insert scope vs

checkForShadowingAltSet :: CheckForShadowing AltM
checkForShadowingAltSet in_scope (AltM (Alt (DeCInstM decon) params body)) =
  let ex_vars = [a | a ::: _ <- deConExTypes decon]
      kinds = deConTyArgs decon ++ [t | _ ::: t <- deConExTypes decon]
      ty_scope = inserts ex_vars in_scope
      param_vars = map patMVar params
      param_types = map patMType params
      body_scope = inserts param_vars ty_scope
  in (foldr seq () $ map (checkForShadowingSet in_scope) kinds) `seq`
     assertVarsAreUndefined in_scope ex_vars `seq`
     (foldr seq () $ map (checkForShadowingSet ty_scope) param_types) `seq` 
     assertVarsAreUndefined ty_scope param_vars `seq`
     checkForShadowingExpSet body_scope body
  where
    insert v scope = IntSet.insert (fromIdent $ varID v) scope
    inserts vs scope = foldr insert scope vs

-- | Check whether any variables from the current type environment
--   are shadowed in the expression
checkForShadowingExpHere :: TypeEnvMonad m => ExpM -> m ()
checkForShadowingExpHere e =
  askTypeEnv (\tenv -> checkForShadowingExp tenv e)

checkForShadowingModule :: Module Mem -> ()
checkForShadowingModule (Module _ imports defss exports) =
  checkForShadowingGroupSet check_globals defss IntSet.empty (Rec imports)
  where
    check_globals env (defs : defss) =
      checkForShadowingGroupSet check_globals defss env defs
    
    check_globals env [] =
      foldr seq () $ map (checkForShadowingFunSet env . exportFunction) exports