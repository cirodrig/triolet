{-| Helper functions for creating code.
-}

{-# LANGUAGE FlexibleContexts #-}
module SystemF.Build where

import Common.Error
import SystemF.Syntax
import SystemF.MemoryIR
import Type.Environment
import Type.Eval
import Type.Type

type MkExpM = FreshVarM ExpM
type MkAltM = FreshVarM AltM
type MkFunM = FreshVarM FunM

varE :: Var -> MkExpM
varE v = return $ ExpM $ VarE defaultExpInfo v

litE :: Lit -> MkExpM
litE l = return $ ExpM $ LitE defaultExpInfo l

appE :: MkExpM -> [TypM] -> [MkExpM] -> MkExpM
appE op t_args args = do
  op' <- op
  args' <- sequence args
  return $ ExpM $ AppE defaultExpInfo op' t_args args'

varAppE :: Var -> [TypM] -> [MkExpM] -> MkExpM
varAppE op_var t_args args = do
  let op = ExpM $ VarE defaultExpInfo op_var
  args' <- sequence args
  return $ ExpM $ AppE defaultExpInfo op t_args args'

lamE :: MkFunM -> MkExpM
lamE mk_f = do 
  f <- mk_f
  return $ ExpM $ LamE defaultExpInfo f

letE :: PatM -> ExpM -> ExpM -> ExpM
letE pat val body = ExpM $ LetE defaultExpInfo pat val body

letfunE :: DefGroup (Def Mem) -> ExpM -> ExpM
letfunE defs body = ExpM $ LetfunE defaultExpInfo defs body

caseE :: MkExpM -> [MkAltM] -> MkExpM
caseE scr alts = do
  scr' <- scr
  alts' <- sequence alts
  return $ ExpM $ CaseE defaultExpInfo scr' alts'

mkFun :: [Type]
      -> ([Var] -> FreshVarM ([ParamType], ReturnType))
      -> ([Var] -> [Var] -> MkExpM)
      -> MkFunM
mkFun typaram_kinds mk_params mk_body = do
  typaram_vars <- mapM (const $ newAnonymousVar TypeLevel) typaram_kinds
  (param_types, return_type) <- mk_params typaram_vars
  param_vars <- mapM (const $ newAnonymousVar ObjectLevel) param_types
  body <- mk_body typaram_vars param_vars
  let typarams = zipWith TyPatM typaram_vars typaram_kinds
      params = zipWith memVarP param_vars param_types
      ret = RetM return_type
  return $ FunM $ Fun defaultExpInfo typarams params ret body
  where
    mk_typaram_var _ = newAnonymousVar TypeLevel

mkAlt :: TypeEnv -> Var -> [TypM]
      -> ([Var] -> [Var] -> MkExpM)
      -> MkAltM
mkAlt tenv con ty_args mk_body =
  case lookupDataCon con tenv
  of Just dcon_type -> do
       -- Get the types of the alternative patterns
       (ex_param_types, param_types, _) <-
         instantiateDataConTypeWithFreshVariables dcon_type $
         map fromTypM ty_args
       
       -- Create the rest of the code
       let typat_vars = [v | ValPT (Just v) ::: _ <- ex_param_types]
       pat_vars <- mapM (const $ newAnonymousVar ObjectLevel) param_types
       body <- mk_body typat_vars pat_vars
       
       let ex_params = [TyPatM v t
                       | (v, _ ::: t) <- zip typat_vars ex_param_types]
           patterns = [memVarP v (returnReprToParamRepr repr ::: ty)
                      | (v, repr ::: ty) <- zip pat_vars param_types]
       return $ AltM $ Alt con ty_args ex_params patterns body
     _ -> internalError "mkAlt"

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