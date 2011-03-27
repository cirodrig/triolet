
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
        substituteDefM,
        freshenModuleFully)
where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Data.Maybe
import Data.Monoid
import qualified Data.Set as Set
import Debug.Trace

import Common.Error
import Common.MonadLogic
import Common.Supply
import SystemF.Syntax
import SystemF.MemoryIR
import Type.Type
import Type.Rename

-- | Apply a renaming to a type pattern
renameTyPatM :: Renaming -> TyPatM -> TyPatM
renameTyPatM rn pattern =
  case pattern
  of TyPatM v ty -> TyPatM v (rename rn ty)

-- | Apply a renaming to a pattern
renamePatM :: Renaming -> PatM -> PatM
renamePatM rn pattern =
  case pattern
  of MemVarP v prepr uses ->
       MemVarP v (rename_prepr prepr) uses
     LocalVarP v ty dict uses ->
       LocalVarP v (rename rn ty) (rename rn dict) uses
     MemWildP prepr ->
       MemWildP (rename_prepr prepr)
  where
    rename_prepr (repr ::: ty) =
      case repr
      of ValPT (Just _) -> internalError "renamePatM: Superfluous binding"
         _ -> repr ::: rename rn ty

-- | Freshen a type variable binding
freshenTyPatM :: (Monad m, Supplies m VarID) => TyPatM -> m (TyPatM, Renaming)
freshenTyPatM (TyPatM v ty) = do
  v' <- newClonedVar v
  return (TyPatM v' ty, singletonRenaming v v')

-- | Freshen a list of type variable bindings.  None of the bindings refer to
--   a variable bound by another member of the list.
freshenTyPatMs :: (Monad m, Supplies m VarID) => [TyPatM]
               -> m ([TyPatM], Renaming)
freshenTyPatMs pats = do                  
  (pats', assocs) <- mapAndUnzipM freshen_pattern pats
  return (pats', renaming assocs)
  where
    freshen_pattern (TyPatM v ty) = do
      v' <- newClonedVar v
      return (TyPatM v' ty, (v, v'))

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

freshenPattern (MemVarP v param_ty uses) = do
  v' <- newClonedVar v
  return (MemVarP v' param_ty uses, Just (v, v'))

freshenPattern (LocalVarP {}) =
  internalError "freshenPattern: Unexpected pattern"
                                   
freshenPattern (MemWildP param_ty) =
  return (MemWildP param_ty, Nothing)

-- | Apply a substitution to a type pattern
substituteTyPatM :: Substitution -> TyPatM -> TyPatM
substituteTyPatM s pattern =
  case pattern
  of TyPatM v ty -> TyPatM v (substitute s ty)

-- | Apply a substitution to a pattern
substitutePatM :: Substitution -> PatM -> PatM
substitutePatM s pattern =
  case pattern
  of MemVarP v (repr ::: ty) uses ->
       case repr
       of ValPT (Just _) -> internalError "substitutePatM: Superfluous binding"
          _ -> MemVarP v (repr ::: substitute s ty) uses
     LocalVarP v ty dict uses ->
       LocalVarP v (substitute s ty) (substitute s dict) uses
     MemWildP (repr ::: ty) ->
       case repr
       of ValPT (Just _) -> internalError "substitutePatM: Superfluous binding"
          _ -> MemWildP (repr ::: substitute s ty)
     
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
         AppE inf (recurse op) (map recurse ts) (map recurse es)
       LamE inf f ->
         LamE inf (recurse f)
       LetE inf p val body ->
         LetE inf (renamePatM rn p) (recurse val) (recurse body)
       LetfunE inf defs body ->
         LetfunE inf (fmap (renameDefM rn) defs) (recurse body)
       CaseE inf scr alts ->
         CaseE inf (recurse scr) (map recurse alts)
       ExceptE inf rty ->
         ExceptE inf (rename rn rty)
    where
      {-# INLINE recurse #-}
      recurse :: Renameable a => a -> a
      recurse = rename rn

  freshen (ExpM expression) =
    case expression
    of LetE inf (LocalVarP v ty dict uses) rhs body -> do
         -- This variable is in scope over the rhs and the body
         v' <- newClonedVar v
         let rhs' = rename (singletonRenaming v v') rhs
         let body' = rename (singletonRenaming v v') body
         return $ ExpM $ LetE inf (LocalVarP v' ty dict uses) rhs' body'

       LetE inf pat rhs body -> do
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
         in case pat
            of MemVarP {} -> ty_fv `Set.union` rhs_fv `Set.union` body_fv
               MemWildP {} -> ty_fv `Set.union` rhs_fv `Set.union` body_fv
               LocalVarP {} ->
                 let rhs_fv' = Set.delete (patMVar' pat) rhs_fv
                     dict_fv = freeVariables $ patMDict pat
                 in ty_fv `Set.union` dict_fv `Set.union` rhs_fv `Set.union` body_fv
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
    AltM $ Alt { altConstructor = altConstructor alt
               , altTyArgs = map (rename rn) $ altTyArgs alt
               , altExTypes = map (renameTyPatM rn) $ altExTypes alt
               , altParams = map (renamePatM rn) $ altParams alt
               , altBody = rename rn $ altBody alt}

  freshen (AltM alt) = do
    (ex_types, ex_renaming) <- freshenTyPatMs $ altExTypes alt
    (params, param_renaming) <-
      freshenPatMs $ map (renamePatM ex_renaming) $ altParams alt
    
    let renaming = ex_renaming `mappend` param_renaming
    let body = rename renaming $ altBody alt    

    return $ AltM $ Alt { altConstructor = altConstructor alt
                        , altTyArgs = altTyArgs alt
                        , altExTypes = ex_types
                        , altParams = params
                        , altBody = body}

  freeVariables (AltM alt) =
    let ty_fv = Set.unions $ map freeVariables $ altTyArgs alt
        typat_fv = Set.unions $
                   map freeVariables [t | TyPatM _ t <- altExTypes alt]
        typat_vars = [v | TyPatM v _ <- altExTypes alt]
          
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
    FunM $ Fun { funInfo = funInfo fun
               , funTyParams = map (renameTyPatM rn) $ funTyParams fun 
               , funParams = map (renamePatM rn) $ funParams fun
               , funReturn = rename rn $ funReturn fun
               , funBody = rename rn $ funBody fun}
  
  freshen (FunM fun) = do
    (ty_params, ty_renaming) <- freshenTyPatMs $ funTyParams fun
    (params, param_renaming) <-
      freshenPatMs $ map (renamePatM ty_renaming) $ funParams fun
    let renaming = ty_renaming `mappend` param_renaming
    let ret = rename renaming $ funReturn fun
        body = rename renaming $ funBody fun
    return $ FunM $ Fun { funInfo = funInfo fun
                        , funTyParams = ty_params
                        , funParams = params
                        , funReturn = ret
                        , funBody = body}

  freeVariables (FunM fun) = do
    let typat_fv = Set.unions $
                   map freeVariables [t | TyPatM _ t <- funTyParams fun]
        typat_vars = [v | TyPatM v _ <- funTyParams fun]
          
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

instance Substitutable (Typ Mem) where
  substitute s (TypM t) = TypM $ substitute s t

instance Substitutable (Ret Mem) where
  substitute s (RetM rt) = RetM (substitute s rt)

instance Substitutable (Exp Mem) where
  substitute s (ExpM expression) = ExpM $
    case expression
    of VarE inf v ->
         case substituteVar v s
         of Just _ ->
              internalError "Exp Mem.substitute: type substituted for variable"
            Nothing -> expression
       LitE {} -> expression
       AppE inf op ts es ->
         AppE inf (recurse op) (map recurse ts) (map recurse es)
       LamE inf f ->
         LamE inf (recurse f)
       LetE inf p val body ->
         LetE inf (substitutePatM s p) (recurse val) (recurse body)
       LetfunE inf defs body ->
         LetfunE inf (fmap (substituteDefM s) defs) (recurse body)
       CaseE inf scr alts ->
         CaseE inf (recurse scr) (map recurse alts)
       ExceptE inf ty ->
         ExceptE inf (substitute s ty)
    where
      {-# INLINE recurse #-}
      recurse :: Substitutable a => a -> a
      recurse = substitute s

instance Substitutable (Alt Mem) where
  substitute s (AltM alt) =
    AltM $ Alt { altConstructor = altConstructor alt
               , altTyArgs = map (substitute s) $ altTyArgs alt
               , altExTypes = map (substituteTyPatM s) $ altExTypes alt
               , altParams = map (substitutePatM s) $ altParams alt
               , altBody = substitute s $ altBody alt}

instance Substitutable (Fun Mem) where
  substitute s (FunM fun) =
    FunM $ Fun { funInfo = funInfo fun
               , funTyParams = map (substituteTyPatM s) $ funTyParams fun 
               , funParams = map (substitutePatM s) $ funParams fun
               , funReturn = substitute s $ funReturn fun
               , funBody = substitute s $ funBody fun}

substituteDefM s def = def {definiens = substitute s $ definiens def}

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

freshenRet (RetM (rrepr ::: rtype)) =
  ReaderT $ \rn -> return (RetM (rrepr ::: rename rn rtype))

freshenTyParam (TyPatM v ty) k = do
  ty' <- freshenType ty
  freshenVar v $ \v' -> k (TyPatM v' ty')

freshenParam (MemVarP v (prepr ::: ty) dmd) k = do
  ty' <- freshenType ty
  dmd' <- freshenDmd dmd
  freshenVar v $ \v' -> k (MemVarP v' (prepr ::: ty') dmd')

freshenParam (MemWildP (prepr ::: ty)) k = do
  ty' <- freshenType ty
  k (MemWildP (prepr ::: ty'))

freshenParam (LocalVarP {}) _ = internalError "freshenParam"

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
     LetE inf (LocalVarP pat_var ty dict uses) rhs body -> do
       ty' <- freshenType ty
       dict' <- freshenExp dict
       uses' <- freshenDmd uses
       freshenVar pat_var $ \pat_var' -> do
         rhs' <- freshenExp rhs
         body' <- freshenExp body
         trace ("freshenLocal " ++ show pat_var ++ " " ++ show pat_var') $
           return $ LetE inf (LocalVarP pat_var' ty' dict' uses') rhs' body'
         
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