
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
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
        renameDefM,
        renameDefGroup,
        freshenModuleFully)
where

import Prelude hiding(mapM)
import Control.Applicative
import Control.Monad hiding(mapM)
import Control.Monad.Reader hiding(mapM)
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

instance Renameable (Typ Mem) where
  rename rn (TypM t) = TypM $ rename rn t
  freshen p (TypM t) = liftM TypM $ freshen p t
  freeVariables (TypM t) = freeVariables t

instance Renameable (Exp Mem) where
  rename rn (ExpM expression) = ExpM $
    case expression
    of VarE inf v ->
         case renameVar v rn
         of Just v' -> VarE inf v'
            Nothing -> expression
       LitE {} -> expression
       UTupleE inf fields ->
         UTupleE inf (map (rename rn) fields)
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
       UTupleE _ es -> Set.unions $ map freeVariables es
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

instance Renameable (Alt Mem) where
  rename rn (AltM alt) =
    case alt
    of DeCon con ty_args ex_types params body ->
         let ty_args' = rename rn ty_args
         in renameTyPatMs rn ex_types $ \rn' ex_types' ->
            renamePatMs rn' params $ \rn'' params' ->
            AltM $ DeCon { altConstructor = con
                         , altTyArgs = ty_args'
                         , altExTypes = ex_types'
                         , altParams = params'
                         , altBody = rename rn'' body}
       DeTuple params body ->
            renamePatMs rn params $ \rn' params' ->
            AltM $ DeTuple { altParams = params'
                           , altBody = rename rn' body}
         

  freshen p (AltM alt) =
    case alt
    of DeCon con ty_args ex_types params body -> do
         (ex_types', ex_renaming) <- freshenTyPatMs p ex_types
         renamePatMs ex_renaming params $ \ex_renaming' params' -> do
           (rn_params, param_renaming) <- freshenPatMs p params'
           let renaming = param_renaming `mappend` ex_renaming'
           let body' = rename renaming body
           return $ AltM $ DeCon { altConstructor = con
                                 , altTyArgs = ty_args
                                 , altExTypes = ex_types'
                                 , altParams = rn_params
                                 , altBody = body'}

       DeTuple params body -> do
           (rn_params, param_renaming) <- freshenPatMs p params
           let body' = rename param_renaming body
           return $ AltM $ DeTuple { altParams = rn_params
                                   , altBody = body'}
         

  freeVariables (AltM alt) =
    case alt
    of DeCon _ ty_args ex_types params body ->
         let ty_fv = Set.unions $ map freeVariables ty_args
             typat_fv = Set.unions $
                        map freeVariables [t | TyPatM (_ ::: t) <- ex_types]
             typat_vars = [v | TyPatM (v ::: _) <- ex_types]

             -- Get free variables from patterns; remove existential variables
             pat_fv1 = Set.unions $ map (freeVariables . patMType) params
             pat_fv = foldr Set.delete pat_fv1 typat_vars

             pat_vars = map patMVar params
        
             -- Get free variables from body;
             -- remove existential variables and fields
             body_fv = foldr Set.delete (freeVariables body)
                       (typat_vars ++ pat_vars)
         in ty_fv `Set.union` typat_fv `Set.union` pat_fv `Set.union` body_fv
       DeTuple params body ->
         let pat_fv = Set.unions $ map (freeVariables . patMType) params
             pat_vars = map patMVar params

             -- Get free variables from body;
             -- remove existential variables and fields
             body_fv = foldr Set.delete (freeVariables body) pat_vars
         in pat_fv `Set.union` body_fv

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

instance Substitutable (Exp Mem) where
  substitute s (ExpM expression) =
    case expression
    of VarE inf v ->
         case substituteVar v s
         of Just _ ->
              internalError "Exp Mem.substitute: type substituted for variable"
            Nothing -> return (ExpM expression)
       LitE {} -> return (ExpM expression)
       UTupleE inf fields -> do
         fields' <- mapM (substitute s) fields
         return $ ExpM $ UTupleE inf fields
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

instance Substitutable (Alt Mem) where
  substitute s (AltM alt) =
    case alt
    of DeCon con ty_args ex_types params body -> do
         ty_args' <- mapM (substitute s) ty_args
         substituteTyPatMs s ex_types $ \s' ex_types' ->
           substitutePatMs' s' params $ \s'' params' -> do
             body' <- substitute s'' body
             return $ AltM $ DeCon { altConstructor = con
                                   , altTyArgs = ty_args'
                                   , altExTypes = ex_types'
                                   , altParams = params'
                                   , altBody = body'}
       DeTuple params body -> do
         substitutePatMs' s params $ \s' params' -> do
           body' <- substitute s' body
           return $ AltM $ DeTuple { altParams = params'
                                   , altBody = body'}

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

freshenTyParam (TyPatM (v ::: ty)) k = do
  ty' <- freshenType ty
  freshenVar v $ \v' -> k (TyPatM (v' ::: ty'))

freshenParam (PatM (v ::: ty) dmd) k = do
  ty' <- freshenType ty
  dmd' <- freshenDmd dmd
  freshenVar v $ \v' -> k (PatM (v' ::: ty') dmd')

freshenExp (ExpM expression) = ExpM <$>
  case expression
  of VarE inf v -> VarE inf <$> lookupVar v
     LitE _ _ -> return expression
     UTupleE inf args ->
       UTupleE inf <$> mapM freshenExp args
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

freshenAlt (AltM alt) = 
  case alt
  of DeCon con ty_args ex_types params body -> do
       ty_args' <- mapM freshenType ty_args
       withMany freshenTyParam ex_types $ \ex_types' ->
         withMany freshenParam params $ \params' -> do
           body' <- freshenExp body
           return $ AltM $ DeCon { altConstructor = con
                                 , altTyArgs = ty_args'
                                 , altExTypes = ex_types'
                                 , altParams = params'
                                 , altBody = body'}
     DeTuple params body ->
       withMany freshenParam params $ \params' -> do
         body' <- freshenExp body
         return $ AltM $ DeTuple { altParams = params'
                                 , altBody = body'}

freshenFun (FunM f) =
  withMany freshenTyParam (funTyParams f) $ \ty_params ->
  withMany freshenParam (funParams f) $ \params -> do
    body <- freshenExp $ funBody f
    ret <- freshenType $ funReturn f
    return $ FunM $ f { funTyParams = ty_params
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