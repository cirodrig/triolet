
{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving #-}
module SystemF.Floating2
       (longRangeFloating)
where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.Trans
import qualified Data.Set as Set

import Common.Identifier
import Common.Supply
import SystemF.Syntax
import SystemF.MemoryIR
import SystemF.Context
import SystemF.TypecheckMem
import Type.Type
import Type.Environment
import GlobalVar
import Globals

isSingletonConInst :: ConInst -> Bool
isSingletonConInst (VarCon op _ _) = isSingletonCon op
isSingletonConInst (TupleCon _) = False

-------------------------------------------------------------------------------
-- The Floating monad

data FloatCtx = 
  FloatCtx { fcVarSupply :: {-# UNPACK #-}!(IdentSupply Var)
             -- | The type environment
           , fcTypeEnv :: TypeEnv
           }

newtype Flt a = Flt {unFlt :: ReaderT FloatCtx IO a}
              deriving(Functor, Monad, MonadIO)

runFlt :: Flt a -> IdentSupply Var -> TypeEnv -> IO a
runFlt m id_supply tenv = runReaderT (unFlt m) (FloatCtx id_supply tenv)

instance TypeEnvMonad Flt where
  getTypeEnv = Flt (asks fcTypeEnv)
  assume v ty (Flt m) = Flt $ local insert_type m
    where
      insert_type ctx = ctx {fcTypeEnv = insertType v ty $ fcTypeEnv ctx}

instance Supplies Flt (Ident Var) where
  fresh = Flt $ ReaderT $ \ctx -> supplyValue (fcVarSupply ctx)

instance EvalMonad Flt where
  liftTypeEvalM m = Flt $ ReaderT $ \ctx ->
    runTypeEvalM m (fcVarSupply ctx) (fcTypeEnv ctx)

enterScope1 :: PatM -> TypeEvalM Type
            -> Flt (Contexted ExpM) -> Flt (Contexted ExpM)
enterScope1 pat get_type m =
  assumePatM pat $ m >>= anchorVar (patMVar pat) get_type

enterScopeOfVar :: Var -> Type -> TypeEvalM Type
                -> Flt (Contexted ExpM) -> Flt (Contexted ExpM)
enterScopeOfVar v t get_type m =
  assume v t $ m >>= anchorVar v get_type

enterScopeOfVars :: [Binder] -> TypeEvalM Type
                 -> Flt (Contexted ExpM) -> Flt (Contexted ExpM)
enterScopeOfVars bindings get_type m =
  assumeBinders bindings $ m >>= anchorVarList [v | v ::: _ <- bindings] get_type

enterScope :: [PatM] -> TypeEvalM Type
           -> Flt (Contexted ExpM) -> Flt (Contexted ExpM)
enterScope pats get_type m =
  assumePatMs pats $ m >>= anchorVarList (map patMVar pats) get_type

-- | Enter a scope in which some type and value variables are bound
enterScope' :: [Binder] -> [PatM] -> TypeEvalM Type
            -> Flt (Contexted ExpM)
            -> Flt (Contexted ExpM)
enterScope' ty_binders pats get_type m =
  let local_vars = [v | v ::: _ <- ty_binders] ++ map patMVar pats
  in assumeBinders ty_binders $ assumePatMs pats $
     m >>= anchorVarList local_vars get_type

-------------------------------------------------------------------------------

floatExps :: [ExpM] -> Flt (Contexted [ExpM])
floatExps es = mergeList =<< mapM floatExp es

floatExp :: ExpM -> Flt (Contexted ExpM)
floatExp expression =
  case fromExpM expression
  of VarE {} -> return $ unitContext expression
     LitE {} -> return $ unitContext expression
     ConE inf con args -> do
       ctx_args <- floatExps args
       let new_exp = mapContext (\es -> ExpM $ ConE inf con es) ctx_args
       
       -- If constructing a known-safe singleton type, float the constructor
       -- outward as far as possible
       if isSingletonConInst $ fromCInstM con
         then do
           ty <- inferExpType expression
           joinInContext new_exp $ asLetContext ty
         else return new_exp
     AppE inf op ty_args args -> do
       ctx_op <- floatExp op
       ctx_args <- floatExps args
       let make_new_exp op' args' = ExpM $ AppE inf op' ty_args args'
       mergeWith make_new_exp ctx_op ctx_args
     LamE inf f -> do
       ctx_f <- floatFun [] f
       return $ mapContext (\f' -> ExpM $ LamE inf f') ctx_f
     LetE inf pat rhs body -> do
       ctx_rhs <- floatExp rhs
       ctx_body <- enterScope1 pat (inferExpType body) $ floatExp body
       let make_new_exp rhs' body' = ExpM $ LetE inf pat rhs' body'
       mergeWith make_new_exp ctx_rhs ctx_body
     LetfunE inf (NonRec def) body -> do
       let f = definiens def
       ctx_f <- floatFun [] f
       ctx_body <-
         enterScopeOfVar (definiendum def) (functionType f) (inferExpType body) $
         floatExp body
       let make_new_exp f' body' =
             ExpM $ LetfunE inf (NonRec (def {definiens = f'})) body'
       mergeWith make_new_exp ctx_f ctx_body
     LetfunE inf (Rec defs) body -> do
       let fs = map definiens defs
           local_var_types =
             zipWith (:::) (map definiendum defs) (map functionType fs)
       ctx_fs <- mergeList =<< mapM (floatFun local_var_types) fs
       ctx_body <- enterScopeOfVars local_var_types (inferExpType body) $
                   floatExp body
       let make_new_exp fs' body' =
             let defs' = [def {definiens = f'} | (def, f') <- zip defs fs']
             in ExpM $ LetfunE inf (Rec defs') body'
       mergeWith make_new_exp ctx_fs ctx_body
     CaseE inf scr alts -> do
       ctx_scr <- floatExp scr
       ctx_alts <- mergeList =<< mapM floatAlt alts
       let make_new_exp scr' alts' = ExpM $ CaseE inf scr' alts'
       mergeWith make_new_exp ctx_scr ctx_alts
     ExceptE inf ty -> return $ unitContext expression
     CoerceE inf t1 t2 body -> do
       ctx_body <- floatExp body
       return $ mapContext (\e -> ExpM $ CoerceE inf t1 t2 e) ctx_body

floatAlt :: AltM -> Flt (Contexted AltM)
floatAlt (AltM (Alt (DeCInstM decon) params body)) = do
  ctx_body <- enterScope' (deConExTypes decon) params (inferExpType body) $
              floatExp body
  return $ mapContext (\e -> AltM $ Alt (DeCInstM decon) params e) ctx_body

-- | Perform floating in a function.
--
--   If the function is part of a recursive definition group, the binder list
--   is the list of all functions bound in the definition group.  References
--   to those functions can't be floated out of the function body.
floatFun :: [Binder] -> FunM -> Flt (Contexted FunM)
floatFun fun_binders (FunM f@(Fun inf ty_params params return_type body)) = do
  fun_body <-
    enterScope' [p | TyPatM p <- ty_params] params (return $ fromTypM return_type) $
    floatExp body
  return $ mapContext (\e -> FunM $ f {funBody = e}) fun_body

-- | Perform floating in a top-level function.  Nothing is floated out of
--   the function.
floatTopLevelFun :: FunM -> Flt FunM
floatTopLevelFun (FunM f@(Fun inf ty_params params return_type body)) =
  assumeBinders [p | TyPatM p <- ty_params] $ 
  assumePatMs params $ do
    ctx_body <- floatExp body
    body <- contextExpression ctx_body (fromTypM return_type)
    return $ FunM (f {funBody = body})

-- | Perform floating in a top-level definition group
floatTopLevelGroup :: DefGroup (Def Mem)
                   -> (DefGroup (Def Mem) -> Flt a)
                   -> Flt a
floatTopLevelGroup (NonRec def) k = do
  f <- floatTopLevelFun $ definiens def
  let def' = def {definiens = f}
  assume (definiendum def) (functionType f) $ k (NonRec def')

floatTopLevelGroup (Rec defs) k = assume_defs $ do
  fs <- mapM (floatTopLevelFun . definiens) defs
  let defs' = [def {definiens = f} | (def, f) <- zip defs fs]
  k (Rec defs')
  where
    assume_defs m = foldr assume_def m defs
    assume_def def = assume (definiendum def) (functionType $ definiens def)

floatExport :: Export Mem -> Flt (Export Mem)
floatExport export = do
  f <- floatTopLevelFun $ exportFunction export
  return $ export {exportFunction = f}

floatModule :: Module Mem -> Flt (Module Mem)
floatModule (Module module_name imports defs exports) = do
  (defs', exports') <- assume_imports $ float_groups defs
  return $ Module module_name imports defs' exports'
  where
    float_groups (ds:dss) =
      floatTopLevelGroup ds $ \ds' -> do
        (dss', exports') <- float_groups dss
        return (ds' : dss', exports')

    float_groups [] = do
      exports' <- mapM floatExport exports
      return ([], exports')

    assume_imports m = foldr assume_import m imports
    assume_import def = assume (definiendum def) (functionType $ definiens def)

longRangeFloating :: Module Mem -> IO (Module Mem)
longRangeFloating mod =
  withTheNewVarIdentSupply $ \var_supply -> do
    tenv <- readInitGlobalVarIO the_memTypes
    runFlt (floatModule mod) var_supply tenv