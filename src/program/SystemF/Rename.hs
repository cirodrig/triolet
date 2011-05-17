
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
module SystemF.Rename
       (freshen,
        renamePatM,
        substitutePatM,
        freshenPatM,
        freshenPatMs,
        renameTyPatM,
        substituteTyPatM,
        freshenTyPatM,
        freshenTyPatMs,
        renameDefM,
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
import Type.Environment
import Type.Type
import Type.Rename

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
renamePatM rn pattern k =
  case pattern
  of MemVarP binding uses ->
       renameBinding rn binding $ \rn' binding' ->
       k rn' (MemVarP binding' (rename rn uses))
     MemWildP ty -> k rn (MemWildP (rename rn ty))

renamePatMs :: Renaming -> [PatM] -> (Renaming -> [PatM] -> a) -> a
renamePatMs = renameMany renamePatM

-- | Freshen a type variable binding
freshenTyPatM :: (Monad m, Supplies m VarID) => TyPatM -> m (TyPatM, Renaming)
freshenTyPatM (TyPatM (v ::: ty)) = do
  v' <- newClonedVar v
  return (TyPatM (v' ::: ty), singletonRenaming v v')

-- | Freshen a list of type variable bindings.  None of the bindings refer to
--   a variable bound by another member of the list.
freshenTyPatMs :: (Monad m, Supplies m VarID) => [TyPatM]
               -> m ([TyPatM], Renaming)
freshenTyPatMs pats = do
  (pats', assocs) <- mapAndUnzipM freshen_pattern pats
  return (pats', renaming assocs)
  where
    freshen_pattern (TyPatM (v ::: ty)) = do
      v' <- newClonedVar v
      return (TyPatM (v' ::: ty), (v, v'))

-- | Freshen a variable binding that is /not/ a local variable binding.
freshenPatM :: (Monad m, Supplies m VarID) => PatM -> m (PatM, Renaming)
freshenPatM pat = do 
  (pat', assocs) <- freshenPattern pat
  return (pat', maybe mempty (uncurry singletonRenaming) assocs)

-- | Freshen a list of variable bindings. 
--   There must not be any local variable bindings in the list.
--   None of the bindings may refer to a variable bound by another member of
--   the list. 
freshenPatMs :: (Monad m, Supplies m VarID) => [PatM] -> m ([PatM], Renaming)
freshenPatMs pats = do
  (pats', assocs) <- mapAndUnzipM freshenPattern pats
  return (pats', renaming $ catMaybes assocs)

freshenPattern (MemVarP (v ::: param_ty) uses) = do
  v' <- newClonedVar v
  return (MemVarP (v' ::: param_ty) uses, Just (v, v'))

freshenPattern (MemWildP param_ty) =
  return (MemWildP param_ty, Nothing)

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
  
-- | Apply a substitution to a pattern
substitutePatM :: EvalMonad m =>
                  Substitution -> PatM -> (Substitution -> PatM -> m a) -> m a
substitutePatM s pattern k =
  case pattern
  of MemVarP binder uses ->
       substituteBinding s binder $ \s' binder' ->
       k s' (MemVarP binder' uses)
     MemWildP ty -> do
       ty' <- substitute s ty
       k s (MemWildP ty')
     
substitutePatMs :: EvalMonad m =>
                  Substitution -> [PatM]
                -> (Substitution -> [PatM] -> m a)
                -> m a
substitutePatMs = renameMany substitutePatM

instance Renameable (Typ Mem) where
  rename rn (TypM t) = TypM $ rename rn t
  freshen (TypM t) = liftM TypM $ freshen t
  freeVariables (TypM t) = freeVariables t

instance Renameable (Ret Mem) where
  rename rn (RetM rt) = RetM (rename rn rt)
  freshen (RetM rt) = liftM RetM $ freshen rt
  freeVariables (RetM rt) = freeVariables rt

instance Renameable (Exp Mem) where
  rename rn (ExpM expression) = ExpM $
    case expression
    of VarE inf v ->
         case renameVar v rn
         of Just v' -> VarE inf v'
            Nothing -> expression
       LitE {} -> expression
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

  freshen (ExpM expression) =
    case expression
    of LetE inf pat rhs body -> do
         (pat', rn) <- freshenPatM pat
         let body' = rename rn body
         return $ ExpM $ LetE inf pat' rhs body'

       LetfunE inf (NonRec def) body -> do
         let v = definiendum def
         v' <- newClonedVar v
         let body' = rename (singletonRenaming v v') body
             def' = def {definiendum = v'}
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
       AppE _ op ty_args args -> Set.union (freeVariables op) $
                                 Set.union (freeVariables ty_args) $
                                 freeVariables args
       LamE _ f -> freeVariables f
       LetE _ pat rhs body ->
         let ty_fv = freeVariables $ patMType pat
             rhs_fv = freeVariables rhs
             body_fv = case patMVar pat 
                       of Nothing -> freeVariables body
                          Just v -> Set.delete v $ freeVariables body
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
    let ty_args = rename rn (altTyArgs alt)
    in renameTyPatMs rn (altExTypes alt) $ \rn' ex_types ->
       renamePatMs rn' (altParams alt) $ \rn'' params ->
       AltM $ Alt { altConstructor = altConstructor alt
                  , altTyArgs = ty_args
                  , altExTypes = ex_types
                  , altParams = params
                  , altBody = rename rn'' $ altBody alt}

  freshen (AltM alt) = do
    (ex_types, ex_renaming) <- freshenTyPatMs $ altExTypes alt
    renamePatMs ex_renaming (altParams alt) $ \ex_renaming' params -> do
      (rn_params, param_renaming) <- freshenPatMs params
      let renaming = param_renaming `mappend` ex_renaming'
      let body = rename renaming $ altBody alt    

      return $ AltM $ Alt { altConstructor = altConstructor alt
                          , altTyArgs = altTyArgs alt
                          , altExTypes = ex_types
                          , altParams = rn_params
                          , altBody = body}

  freeVariables (AltM alt) =
    let ty_fv = Set.unions $ map freeVariables $ altTyArgs alt
        typat_fv = Set.unions $
                   map freeVariables [t | TyPatM (_ ::: t) <- altExTypes alt]
        typat_vars = [v | TyPatM (v ::: _) <- altExTypes alt]
          
        -- Get free variables from patterns; remove existential variables
        pat_fv1 = Set.unions $
                  map (freeVariables . patMType) $ altParams alt
        pat_fv = foldr Set.delete pat_fv1 typat_vars

        pat_vars = mapMaybe patMVar $ altParams alt
        
        -- Get free variables from body;
        -- remove existential variables and fields
        body_fv = foldr Set.delete (freeVariables $ altBody alt)
                  (typat_vars ++ pat_vars)
    in ty_fv `Set.union` typat_fv `Set.union` pat_fv `Set.union` body_fv

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
  
  freshen (FunM fun) = do
    (ty_params, ty_renaming) <- freshenTyPatMs $ funTyParams fun
    renamePatMs ty_renaming (funParams fun) $ \ty_renaming' params -> do
      (rn_params, param_renaming) <- freshenPatMs params
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

        pat_vars = mapMaybe patMVar $ funParams fun
        
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

instance Substitutable (Ret Mem) where
  substitute s (RetM rt) = RetM `liftM` substitute s rt

instance Substitutable (Exp Mem) where
  substitute s (ExpM expression) =
    case expression
    of VarE inf v ->
         case substituteVar v s
         of Just _ ->
              internalError "Exp Mem.substitute: type substituted for variable"
            Nothing -> return (ExpM expression)
       LitE {} -> return (ExpM expression)
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
         substitutePatM s p $ \s' p' -> do
           body' <- substitute s' body
           return $ ExpM $ LetE inf p' val' body'
       LetfunE inf defs body -> do
         -- For simplicity, always rename the definition group 
         ExpM (LetfunE inf defs' body') <- freshen (ExpM expression)
         defs'' <- mapM (mapMDefiniens (substitute s)) defs'
         body'' <- substitute s body'
         return $ ExpM $ LetfunE inf defs'' body''
       CaseE inf scr alts -> do
         scr' <- substitute s scr
         alts' <- mapM (substitute s) alts
         return $ ExpM $ CaseE inf scr' alts'
       ExceptE inf ty -> do
         ty' <- substitute s ty
         return $ ExpM $ ExceptE inf ty

instance Substitutable (Alt Mem) where
  substitute s (AltM alt) = do
    ty_args <- mapM (substitute s) $ altTyArgs alt
    substituteTyPatMs s (altExTypes alt) $ \s' ex_types ->
      substitutePatMs s' (altParams alt) $ \s'' params -> do
        body <- substitute s'' $ altBody alt
        return $ AltM $ Alt { altConstructor = altConstructor alt
                            , altTyArgs = ty_args
                            , altExTypes = ex_types
                            , altParams = params
                            , altBody = body}

instance Substitutable (Fun Mem) where
  substitute s (FunM fun) =
    substituteTyPatMs s (funTyParams fun) $ \s' ty_params ->
    substitutePatMs s' (funParams fun) $ \s'' params -> do
      body <- substitute s'' $ funBody fun
      ret <- substitute s'' $ funReturn fun
      return $ FunM $ Fun { funInfo = funInfo fun
                          , funTyParams = ty_params
                          , funParams = params
                          , funReturn = ret
                          , funBody = body}

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

freshenRet (RetM rtype) =
  ReaderT $ \rn -> return (RetM (rename rn rtype))

freshenTyParam (TyPatM (v ::: ty)) k = do
  ty' <- freshenType ty
  freshenVar v $ \v' -> k (TyPatM (v' ::: ty'))

freshenParam (MemVarP (v ::: ty) dmd) k = do
  ty' <- freshenType ty
  dmd' <- freshenDmd dmd
  freshenVar v $ \v' -> k (MemVarP (v' ::: ty') dmd')

freshenParam (MemWildP ty) k = do
  ty' <- freshenType ty
  k (MemWildP ty')

freshenExp (ExpM expression) = ExpM <$>
  case expression
  of VarE inf v -> VarE inf <$> lookupVar v
     LitE _ _ -> return expression
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

freshenAlt (AltM alt) = do
  ty_args <- mapM freshenType $ altTyArgs alt
  withMany freshenTyParam (altExTypes alt) $ \ex_types ->
    withMany freshenParam (altParams alt) $ \params -> do
      body <- freshenExp $ altBody alt
      return $ AltM $ Alt { altConstructor = altConstructor alt
                          , altTyArgs = ty_args
                          , altExTypes = ex_types
                          , altParams = params
                          , altBody = body}

freshenFun (FunM f) =
  withMany freshenTyParam (funTyParams f) $ \ty_params ->
  withMany freshenParam (funParams f) $ \params -> do
    body <- freshenExp $ funBody f
    ret <- freshenRet $ funReturn f
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
freshenModuleFully (Module modname groups exports) =
  runReaderT freshen_module mempty
  where
    freshen_module = do
      (groups', exports') <- freshen_defs id groups
      return $ Module modname groups' exports'

    freshen_defs hd (g:gs) =
      freshenDefGroup g $ \g' -> freshen_defs (hd . (g':)) gs

    freshen_defs hd [] = do
      exports' <- mapM freshen_export exports
      return (hd [], exports')
    
    freshen_export e = do
      f <- freshenFun $ exportFunction e
      return $ e {exportFunction = f}