{-| Helper functions for creating code.
-}

{-# LANGUAGE FlexibleContexts, Rank2Types #-}
module SystemF.Build where

import Common.Error
import Common.Supply
import SystemF.Syntax
import SystemF.MemoryIR
import Builtins.Builtins
import Type.Environment
import Type.Eval
import Type.Type

type MkExpM = FreshVarM ExpM
type MkAltM = FreshVarM AltM
type MkFunM = FreshVarM FunM

{-# SPECIALIZE INLINE appExp :: MkExpM -> [Type] -> [MkExpM] -> MkExpM #-}
{-# SPECIALIZE INLINE mkVarAppE :: Var -> [Type] -> [MkExpM] -> MkExpM #-}

mkVarE :: (Supplies m VarID) => Var -> m ExpM
mkVarE v = return $ ExpM $ VarE defaultExpInfo v

litE :: (Supplies m VarID) => Lit -> m ExpM
litE l = return $ ExpM $ LitE defaultExpInfo l

appExp :: (Supplies m VarID) => m ExpM -> [Type] -> [m ExpM] -> m ExpM
appExp op t_args args = do
  op' <- op
  args' <- sequence args
  return $ mkAppE op' t_args args'

mkConE :: Supplies m VarID => ExpInfo -> ConInst -> [m ExpM] -> m ExpM
mkConE inf op args = do
  args' <- sequence args
  return $ conE inf op args'

-- | Create an application term, uncurrying the operator if possible
mkAppE :: ExpM -> [Type] -> [ExpM] -> ExpM
mkAppE op [] [] = op 

mkAppE (ExpM (AppE _ op t_args args1)) [] args2 =
  ExpM $ AppE defaultExpInfo op t_args (args1 ++ args2)
    
mkAppE (ExpM (AppE _ op t_args1 [])) t_args2 args =
  ExpM $ AppE defaultExpInfo op (t_args1 ++ t_args2) args
    
mkAppE op t_args args =
  ExpM $ AppE defaultExpInfo op t_args args

mkVarAppE :: (Supplies m VarID) => Var -> [Type] -> [m ExpM] -> m ExpM
mkVarAppE op_var t_args args = do
  let op = ExpM $ VarE defaultExpInfo op_var
  args' <- sequence args
  return $ mkAppE op t_args args'

lamE :: (Supplies m VarID) => m FunM -> m ExpM
lamE mk_f = do 
  f <- mk_f
  return $ ExpM $ LamE defaultExpInfo f

letE :: PatM -> ExpM -> ExpM -> ExpM
letE pat val body = ExpM $ LetE defaultExpInfo pat val body

initLocalE :: (Supplies m VarID) =>
              Type -> (Var -> m ExpM) -> (Var -> m ExpM) -> m ExpM
initLocalE ty mk_rhs mk_body = localE ty rhs mk_body
  where
    rhs = do
      -- Create a lambda expression (\x : OutPtr t. e1)
      tmpvar_rhs <- newAnonymousVar ObjectLevel
      rhs_body <- mk_rhs tmpvar_rhs
      let out_type = outType ty
          rhs_fun = FunM $ Fun { funInfo = defaultExpInfo 
                               , funTyParams = []
                               , funParams = [patM (tmpvar_rhs ::: out_type)]
                               , funReturn = initEffectType out_type
                               , funBody = rhs_body}
      return $ ExpM $ LamE defaultExpInfo rhs_fun

localE :: (Supplies m VarID) =>
          Type -> m ExpM -> (Var -> m ExpM) -> m ExpM
localE ty mk_rhs mk_body = do
  rhs <- mk_rhs
  tmpvar_body <- newAnonymousVar ObjectLevel
  body <- mk_body tmpvar_body
  let binder = tmpvar_body ::: ty
  return $ letViaBoxed binder rhs body

localE' :: (Supplies m VarID) =>
          Type -> m ExpM -> m (Var, ExpM -> ExpM)
localE' ty mk_rhs = do
  rhs <- mk_rhs
  tmpvar_body <- newAnonymousVar ObjectLevel
  let binder = tmpvar_body ::: ty
  return (tmpvar_body, \body -> letViaBoxed binder rhs body)

-- | Construct what amounts to a 'let' expression for bare objects.
--   Initialize a new boxed object, then read the boxed object.
--
--   TODO: Define localE in terms of this function.
letViaBoxed :: Binder -> ExpM -> ExpM -> ExpM
letViaBoxed binder rhs body =
  let -- Apply the 'boxed' constructor to the RHS
      ty = binderType binder
      boxed_con = VarCon (coreBuiltin The_boxed) [ty] []
      boxed_rhs = conE defaultExpInfo boxed_con [rhs]
  
      -- Create a case statement that binds a temporary value for the body
      expr = ExpM $ CaseE defaultExpInfo boxed_rhs [alt]
      decon = VarDeCon (coreBuiltin The_boxed) [ty] []
      alt = AltM $ Alt { altCon = decon
                       , altParams = [patM binder]
                       , altBody = body}
  in expr

letfunE :: DefGroup (FDef Mem) -> ExpM -> ExpM
letfunE defs body = ExpM $ LetfunE defaultExpInfo defs body

caseE :: (Supplies m VarID) => m ExpM -> [m AltM] -> m ExpM
caseE scr alts = do
  scr' <- scr
  alts' <- sequence alts
  return $ ExpM $ CaseE defaultExpInfo scr' alts'

exceptE :: (Supplies m VarID) => Type -> m ExpM
exceptE ty = return $ ExpM $ ExceptE defaultExpInfo ty

ifE :: (Supplies m VarID) => m ExpM -> m ExpM -> m ExpM -> m ExpM
ifE mk_cond mk_tr mk_fa = do
  cond <- mk_cond
  tr <- mk_tr
  fa <- mk_fa
  let true_con = VarDeCon (coreBuiltin The_True) [] []
      false_con = VarDeCon (coreBuiltin The_False) [] []
      true  = AltM $ Alt true_con [] tr
      false = AltM $ Alt false_con [] fa
  return $ ExpM $ CaseE defaultExpInfo cond [true, false]

mkFun :: forall m. (Supplies m VarID) =>
         [Type]
      -> ([Var] -> m ([Type], Type))
      -> ([Var] -> [Var] -> m ExpM)
      -> m FunM
mkFun typaram_kinds mk_params mk_body = do
  typaram_vars <- mapM (const $ newAnonymousVar TypeLevel) typaram_kinds
  (param_types, return_type) <- mk_params typaram_vars
  param_vars <- mapM (const $ newAnonymousVar ObjectLevel) param_types
  body <- mk_body typaram_vars param_vars
  let typarams = [TyPat (v ::: k) | (v, k) <- zip typaram_vars typaram_kinds]
      params = [patM (v ::: t) | (v, t) <- zip param_vars param_types]
  return $ FunM $ Fun defaultExpInfo typarams params return_type body
  where
    mk_typaram_var :: forall a. a -> m Var
    mk_typaram_var _ = newAnonymousVar TypeLevel

mkAlt :: EvalMonad m =>
         Var -> [Type]
      -> ([Var] -> [Var] -> m ExpM)
      -> m AltM
mkAlt con ty_args mk_body = do
  m_dcon <- lookupDataCon con
  case m_dcon of
    Just dcon_type -> do
       -- Get the types of the alternative patterns
       (ex_param_types, param_types, _) <-
         instantiateDataConTypeWithFreshVariables dcon_type ty_args
       
       -- Create the rest of the code
       let typat_vars = [v | v ::: _ <- ex_param_types]
       pat_vars <- mapM (const $ newAnonymousVar ObjectLevel) param_types
       body <- mk_body typat_vars pat_vars
       
       let ex_params = [v ::: t
                       | (v, _ ::: t) <- zip typat_vars ex_param_types]
           patterns = [patM (v ::: ty)
                      | (v, ty) <- zip pat_vars param_types]
           decon = VarDeCon con ty_args ex_params
       return $ AltM $ Alt decon patterns body
    _ -> internalError "mkAlt"

outType t = outPtrT `typeApp` [t]
initEffectType t = storeT
storedType t = varApp (coreBuiltin The_Stored) [t]

writerType t = outType t `FunT` initEffectType t

{-
mkMemLetE :: FreshVarM ExpM
          -> (Var -> FreshVarM (PatM, ExpM))
          -> FreshVarM ExpM
mkMemLetE rhs mk_val mk_body = do
  v <- newAnonymousVar ObjectLevel
  val <- mk_val
  (pat, body) <- mk_body v
  return $ ExpM $ LetE defaultExpInfo pat val body

-}