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

{-# SPECIALIZE INLINE appExp :: MkExpM -> [TypM] -> [MkExpM] -> MkExpM #-}
{-# SPECIALIZE INLINE varAppE :: Var -> [TypM] -> [MkExpM] -> MkExpM #-}

varE :: (Supplies m VarID) => Var -> m ExpM
varE v = return $ ExpM $ VarE defaultExpInfo v

litE :: (Supplies m VarID) => Lit -> m ExpM
litE l = return $ ExpM $ LitE defaultExpInfo l

appExp :: (Supplies m VarID) => m ExpM -> [TypM] -> [m ExpM] -> m ExpM
appExp op t_args args = do
  op' <- op
  args' <- sequence args
  return $ mkAppE op' t_args args'

-- | Create an application term, uncurrying the operator if possible
mkAppE :: ExpM -> [TypM] -> [ExpM] -> ExpM
mkAppE op [] [] = op 

mkAppE (ExpM (AppE _ op t_args args1)) [] args2 =
  ExpM $ AppE defaultExpInfo op t_args (args1 ++ args2)
    
mkAppE (ExpM (AppE _ op t_args1 [])) t_args2 args =
  ExpM $ AppE defaultExpInfo op (t_args1 ++ t_args2) args
    
mkAppE op t_args args =
  ExpM $ AppE defaultExpInfo op t_args args

varAppE :: (Supplies m VarID) => Var -> [TypM] -> [m ExpM] -> m ExpM
varAppE op_var t_args args = do
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
              TypM -> (Var -> m ExpM) -> (Var -> m ExpM) -> m ExpM
initLocalE ty mk_rhs mk_body = localE ty rhs mk_body
  where
    rhs = do
      -- Create a lambda expression (\x : OutPtr t. e1)
      tmpvar_rhs <- newAnonymousVar ObjectLevel
      rhs_body <- mk_rhs tmpvar_rhs
      let out_type = outType (fromTypM ty)
          rhs_fun = FunM $ Fun { funInfo = defaultExpInfo 
                               , funTyParams = []
                               , funParams = [patM (tmpvar_rhs ::: out_type)]
                               , funReturn = TypM $ initEffectType out_type
                               , funBody = rhs_body}
      return $ ExpM $ LamE defaultExpInfo rhs_fun

localE :: (Supplies m VarID) =>
          TypM -> m ExpM -> (Var -> m ExpM) -> m ExpM
localE ty mk_rhs mk_body = do
  rhs <- mk_rhs
  tmpvar_body <- newAnonymousVar ObjectLevel
  body <- mk_body tmpvar_body
  let binder = tmpvar_body ::: fromTypM ty
  return $ letViaBoxed binder rhs body

localE' :: (Supplies m VarID) =>
          TypM -> m ExpM -> m (Var, ExpM -> ExpM)
localE' ty mk_rhs = do
  rhs <- mk_rhs
  tmpvar_body <- newAnonymousVar ObjectLevel
  let binder = tmpvar_body ::: fromTypM ty
  return (tmpvar_body, \body -> letViaBoxed binder rhs body)

-- | Construct what amounts to a 'let' expression for bare objects.
--   Initialize a new boxed object, then read the boxed object.
--
--   TODO: Define localE in terms of this function.
letViaBoxed :: Binder -> ExpM -> ExpM -> ExpM
letViaBoxed binder rhs body =
  let -- Apply the 'boxed' constructor to the RHS
      ty = TypM $ binderType binder
      boxed_rhs = ExpM $ AppE defaultExpInfo boxed_con [ty] [rhs]
  
      -- Create a case statement that binds a temporary value for the body
      expr = ExpM $ CaseE defaultExpInfo boxed_rhs [alt]
      alt = AltM $ DeCon { altConstructor = pyonBuiltin the_boxed
                         , altTyArgs = [ty]
                         , altExTypes = []
                         , altParams = [patM binder]
                         , altBody = body}
  in expr
  where
    boxed_con = ExpM $ VarE defaultExpInfo (pyonBuiltin the_boxed)

letfunE :: DefGroup (Def Mem) -> ExpM -> ExpM
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
  let true  = AltM $ DeCon (pyonBuiltin the_True) [] [] [] tr
      false = AltM $ DeCon (pyonBuiltin the_False) [] [] [] fa
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
  let typarams = [TyPatM (v ::: k) | (v, k) <- zip typaram_vars typaram_kinds]
      params = [patM (v ::: t) | (v, t) <- zip param_vars param_types]
  return $ FunM $ Fun defaultExpInfo typarams params (TypM return_type) body
  where
    mk_typaram_var :: forall a. a -> m Var
    mk_typaram_var _ = newAnonymousVar TypeLevel

mkAlt :: EvalMonad m =>
         (forall a. FreshVarM a -> m a)
      -> TypeEnv -> Var -> [TypM]
      -> ([Var] -> [Var] -> m ExpM)
      -> m AltM
mkAlt lift_FreshVarM tenv con ty_args mk_body =
  case lookupDataCon con tenv
  of Just dcon_type -> do
       -- Get the types of the alternative patterns
       (ex_param_types, param_types, _) <-
         instantiateDataConTypeWithFreshVariables dcon_type $
         map fromTypM ty_args
       
       -- Create the rest of the code
       let typat_vars = [v | v ::: _ <- ex_param_types]
       pat_vars <- mapM (const $ newAnonymousVar ObjectLevel) param_types
       body <- mk_body typat_vars pat_vars
       
       let ex_params = [TyPatM (v ::: t)
                       | (v, _ ::: t) <- zip typat_vars ex_param_types]
           patterns = [patM (v ::: ty)
                      | (v, ty) <- zip pat_vars param_types]
       return $ AltM $ DeCon con ty_args ex_params patterns body
     _ -> internalError "mkAlt"

outType t = varApp (pyonBuiltin the_OutPtr) [t]
initEffectType t = varApp (pyonBuiltin the_IEffect) [t]
storedType t = varApp (pyonBuiltin the_Stored) [t]

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