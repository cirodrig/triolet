
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
module SystemF.Rename(freshen, renamePatM, freshenPatM, freshenPatMs, renameTyPatM, freshenTyPatMs) where

import Control.Monad
import Data.Monoid
import qualified Data.Set as Set

import Common.Error
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
  of MemVarP v (repr ::: ty) ->
       case repr
       of ValPT (Just _) -> internalError "renamePatM: Superfluous binding"
          _ -> MemVarP v (repr ::: rename rn ty)
     LocalVarP v ty dict -> LocalVarP v (rename rn ty) (rename rn dict)

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
freshenPatM (MemVarP v ty) = do
  v' <- newClonedVar v
  return (MemVarP v' ty, singletonRenaming v v')

freshenPatM (LocalVarP {}) = internalError "freshenPatM: Unexpected pattern"

-- | Freshen a list of variable bindings. 
--   There must not be any local variable bindings in the list.
--   None of the bindings may refer to a variable bound by another member of
--   the list. 
freshenPatMs :: (Monad m, Supplies m VarID) => [PatM] -> m ([PatM], Renaming)
freshenPatMs pats = do
  (pats', assocs) <- mapAndUnzipM freshen_pattern pats
  return (pats', renaming assocs)
  where
    freshen_pattern (MemVarP v param_ty) = do
      v' <- newClonedVar v
      return (MemVarP v' param_ty, (v, v'))

    freshen_pattern (LocalVarP {}) =
      internalError "freshenPatMs: Unexpected pattern"
                                   
-- | Apply a substitution to a type pattern
substituteTyPatM :: Substitution -> TyPatM -> TyPatM
substituteTyPatM s pattern =
  case pattern
  of TyPatM v ty -> TyPatM v (substitute s ty)

-- | Apply a substitution to a pattern
substitutePatM :: Substitution -> PatM -> PatM
substitutePatM s pattern =
  case pattern
  of MemVarP v (repr ::: ty) ->
       case repr
       of ValPT (Just _) -> internalError "substitutePatM: Superfluous binding"
          _ -> MemVarP v (repr ::: substitute s ty)
     LocalVarP v ty dict -> LocalVarP v (substitute s ty) (substitute s dict)

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
       LetrecE inf defs body ->
         LetrecE inf (map (renameDefM rn) defs) (recurse body)
       CaseE inf scr alts ->
         CaseE inf (recurse scr) (map recurse alts)
    where
      {-# INLINE recurse #-}
      recurse :: Renameable a => a -> a
      recurse = rename rn

  freshen (ExpM expression) =
    case expression
    of LetE inf (LocalVarP v ty dict) rhs body -> do
         -- This variable is in scope over the rhs and the body
         v' <- newClonedVar v
         let rhs' = rename (singletonRenaming v v') rhs
         let body' = rename (singletonRenaming v v') body
         return $ ExpM $ LetE inf (LocalVarP v' ty dict) rhs' body'

       LetE inf pat rhs body -> do
         (pat', rn) <- freshenPatM pat
         let body' = rename rn body
         return $ ExpM $ LetE inf pat' rhs body'

       LetrecE inf defs body -> do
         let def_vars = [v | Def v _ <- defs]
         renamed_vars <- mapM newClonedVar def_vars
         
         -- Rename everything
         let rn = renaming $ zip def_vars renamed_vars         
             local_functions = [rename rn f | Def _ f <- defs]
             defs' = zipWith Def renamed_vars local_functions
             body' = rename rn body
         return $ ExpM $ LetrecE inf defs' body'

       _ -> return (ExpM expression)

  freeVariables (ExpM expression) =
    case expression
    of VarE _ v -> Set.singleton v
       LitE _ _ -> Set.empty
       AppE _ op ty_args args -> Set.union (freeVariables op) $
                                 Set.union (freeVariables ty_args) $
                                 freeVariables args
       LamE _ f -> freeVariables f
       LetE _ (MemVarP v (_ ::: ty)) rhs body ->
         let ty_fv = freeVariables ty
             rhs_fv = freeVariables rhs
             body_fv = Set.delete v $ freeVariables body
         in ty_fv `Set.union` rhs_fv `Set.union` body_fv
       LetE _ (LocalVarP v ty dict) rhs body ->
         let ty_fv = freeVariables ty
             dict_fv = freeVariables dict
             rhs_fv = Set.delete v $ freeVariables rhs
             body_fv = Set.delete v $ freeVariables body
         in ty_fv `Set.union` dict_fv `Set.union` rhs_fv `Set.union` body_fv
       LetrecE _ defs body ->
         let local_functions = [v | Def v _ <- defs]
             fn_fv = Set.unions [freeVariables f | Def _ f <- defs]
             body_fv = freeVariables body
         in foldr Set.delete (Set.union fn_fv body_fv) local_functions
       CaseE _ scr alts ->
         freeVariables scr `Set.union` freeVariables alts

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
                  map freeVariables [ty | MemVarP _ (_ ::: ty) <- altParams alt]
        pat_fv = foldr Set.delete pat_fv1 typat_vars

        pat_vars = [v | MemVarP v _ <- altParams alt]
        
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
                  map freeVariables [ty | MemVarP _ (_ ::: ty) <- funParams fun]
        pat_fv = foldr Set.delete pat_fv1 typat_vars

        pat_vars = [v | MemVarP v _ <- funParams fun]
        
        -- Get free variables from body and return type;
        -- remove existential variables and fields
        return_fv = freeVariables $ funReturn fun
        body_fv = freeVariables $ funBody fun
        return_and_body_fv = foldr Set.delete (Set.union return_fv body_fv)
                             (typat_vars ++ pat_vars)
      in typat_fv `Set.union` pat_fv `Set.union` return_and_body_fv
      
renameDefM rn (Def v f) = Def v (rename rn f)

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
       LetrecE inf defs body ->
         LetrecE inf (map (substituteDefM s) defs) (recurse body)
       CaseE inf scr alts ->
         CaseE inf (recurse scr) (map recurse alts)
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

substituteDefM s (Def v f) = Def v (substitute s f)

-- TODO: Move this function to the appropriate place
-- | Given a function and its arguments, get an expresion equivalent to
--   the function applied to those arguments.
betaReduce :: (Monad m, Supplies m VarID) =>
              ExpInfo -> FunM -> [TypM] -> [ExpM] -> m ExpM
betaReduce inf (FunM fun) ty_args args = do
  -- Substitute type arguments for type parameters
  let type_subst =
        substitution [(tv, t)
                     | (TyPatM tv _, TypM t) <- zip (funTyParams fun) ty_args]
        
  -- Rename parameters
  (params, param_renaming) <-
    freshenPatMs $ map (substitutePatM type_subst) $ funParams fun
  
  -- Rename function body
  let body = rename param_renaming $ substitute type_subst $ funBody fun
  
  -- Bind parameters to arguments
  return $ bind_parameters params args body
  where
    bind_parameters params args body =
      foldr bind_parameter body $ zip params args
    
    bind_parameter (param, arg) body =
      ExpM $ LetE inf param arg body