
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
module SystemF.Rename where

import Control.Monad
import Data.Monoid

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

-- | Freshen a variable binding that is /not/ a local variable binding.
freshenPatM :: (Monad m, Supplies m VarID) => PatM -> m (PatM, Renaming)
freshenPatM (MemVarP v ty) = do
  v' <- newClonedVar v
  return (MemVarP v' ty, singletonRenaming v v')

freshenPatM (LocalVarP {}) = internalError "freshenPatM: Unexpected pattern"

instance Renameable (Typ Mem) where
  rename rn (TypM t) = TypM $ rename rn t
  freshen (TypM t) = liftM TypM $ freshen t

instance Renameable (Ret Mem) where
  rename rn (RetM rt) = RetM (rename rn rt)
  freshen (RetM rt) = liftM RetM $ freshen rt

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

instance Renameable (Alt Mem) where
  rename rn (AltM alt) =
    AltM $ Alt { altConstructor = altConstructor alt
               , altTyArgs = map (rename rn) $ altTyArgs alt
               , altExTypes = map (renameTyPatM rn) $ altExTypes alt
               , altParams = map (renamePatM rn) $ altParams alt
               , altBody = rename rn $ altBody alt}

  freshen (AltM alt) = do
    (ex_types, ex_renamings) <- mapAndUnzipM freshenTyPatM $ altExTypes alt
    let ex_renaming = mconcat ex_renamings
    (params, param_renamings) <-
      mapAndUnzipM (freshenPatM . renamePatM ex_renaming) $ altParams alt
    
    let renaming = mconcat (ex_renaming : param_renamings)
    let body = rename renaming $ altBody alt    

    return $ AltM $ Alt { altConstructor = altConstructor alt
                        , altTyArgs = altTyArgs alt
                        , altExTypes = ex_types
                        , altParams = params
                        , altBody = body}

instance Renameable (Fun Mem) where
  rename rn (FunM fun) =
    FunM $ Fun { funInfo = funInfo fun
               , funTyParams = map (renameTyPatM rn) $ funTyParams fun 
               , funParams = map (renamePatM rn) $ funParams fun
               , funReturn = rename rn $ funReturn fun
               , funBody = rename rn $ funBody fun}
  
  freshen (FunM fun) = do
    (ty_params, ty_renamings) <- mapAndUnzipM freshenTyPatM $ funTyParams fun
    let ty_renaming = mconcat ty_renamings
    (params, param_renamings) <-
      mapAndUnzipM (freshenPatM . renamePatM ty_renaming) $ funParams fun
    let renaming = mconcat (ty_renaming : param_renamings)
    let ret = rename renaming $ funReturn fun
        body = rename renaming $ funBody fun
    return $ FunM $ Fun { funInfo = funInfo fun
                        , funTyParams = ty_params
                        , funParams = params
                        , funReturn = ret
                        , funBody = body}
      
renameDefM rn (Def v f) = Def v (rename rn f)
