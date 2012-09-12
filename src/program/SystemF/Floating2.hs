
{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving #-}
module SystemF.Floating2
       (longRangeFloating)
where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.Trans
import qualified Data.Set as Set

import Common.Identifier
import Common.MonadLogic
import Common.Supply
import Builtins.Builtins
import SystemF.Syntax
import SystemF.MemoryIR
import SystemF.PrintMemoryIR
import SystemF.Rename
import SystemF.Context
import SystemF.TypecheckMem
import qualified Type.Rename as Rename
import qualified Type.Substitute as Substitute
import Type.Type
import Type.Environment
import Type.Eval
import GlobalVar
import Globals

-- | Return 'True' if this 'ConInst' constructs a data type that is
--   OK to float.
isDictionaryConInst :: ConInst -> Bool
isDictionaryConInst (VarCon op _ _) = isDictionaryDataCon op
isDictionaryConInst (TupleCon _) = False

-- | Decide whether a call of a particular function may be floated.
--   Floating has already been performed on the argument expressions.  
--   The entire call expression will be floated, including arguments.
--
--   To be floatable, an expression should:
--
--   1. Be very cheap to execute.  Floating may cause a function to execute
--      more often, increasing the overall amount of computation.
--   2. Not raise an exception.  Floating may cause an exeception to be 
--      raised where it would not otherwise have been executed.
--   3. Produce a value or boxed result, because the computed value will be 
--      assigned to a variable.
--
--   We float dictionary-constructing functions.  We also float integer
--   add, subtract, min, and max, because these are used by
--   dictionary-constructing functions.
isFloatableFunction :: Var -> [ExpM] -> Flt Bool
isFloatableFunction v args =
  if floatable_op 
  then allM isFloatableFunctionArg args
  else return False
  where
    floatable_op =
      isReprCon v ||
      v `isCoreBuiltin` The_AdditiveDict_int_add ||
      v `isCoreBuiltin` The_AdditiveDict_int_sub ||
      v `isCoreBuiltin` The_max_int ||
      v `isCoreBuiltin` The_min_int

-- | Return 'True' if it is okay to float a function call in which
--   this expression appears as a subexpression.
isFloatableFunctionArg :: ExpM -> Flt Bool
isFloatableFunctionArg (ExpM expression) =
  case expression
  of VarE {} -> return True
     LitE {} -> return True
     ConE _ con args -> isFloatableData con args
     AppE _ (ExpM (VarE _ op_var)) _ args -> isFloatableFunction op_var args
     _ -> return False

isFloatableFunction' :: Var -> Contexted [ExpM] -> Flt Bool
isFloatableFunction' op_var ctx_args =
  -- Add the context to the environment while making the decision.
  eliminateContext test_floatable ctx_args
  where
    test_floatable args =
      liftM Substitute.Nameless $ isFloatableFunction op_var args

-- | Decide whether a data constructor term appearing as a function argument
--   can be floated.
isFloatableData :: ConInst -> [ExpM] -> Flt Bool
isFloatableData cinst args =
  isFloatableCon cinst >&&> allM isFloatableFunctionArg args
-- | Decide whether a deconstructor can be floated. 
--
--   To be floated, the data type must have exactly one data constructor,
--   so that the pattern match is sure to succeed.
--   Moreover, that constructor's fields must fit in a single register, 
--   which is true if it has exactly one field and that field is boxed,
--   bare, or an approved value type.
isFloatableDecon :: DeConInst -> Flt Bool
isFloatableDecon (VarDeCon con ty_args ex_types) = do
  tenv <- getTypeEnv
  case lookupDataConWithType con tenv of
    Just (data_type, con_type) ->
      let instantiate_field_types = do
            (_, field_types, _) <-
              instantiateDataConType con_type ty_args $ map binderVar ex_types
            return field_types
      in isFloatableDataType tenv data_type con_type instantiate_field_types

-- Don't attempt to float tuples.
-- We could change this to be more permissive if there's a good reason to.
isFloatableDecon (TupleDeCon _) = return False

-- | Decide whether a constructor term can be floated.
--
--   The critera are the same as for deconstructors.
isFloatableCon :: ConInst -> Flt Bool
isFloatableCon (VarCon con ty_args ex_types) = do
  tenv <- getTypeEnv
  case lookupDataConWithType con tenv of
    Just (data_type, con_type) ->
      let instantiate_field_types = do
            (field_types, _) <-
              instantiateDataConTypeWithExistentials con_type
              (ty_args ++ ex_types)
            return field_types
      in isFloatableDataType tenv data_type con_type instantiate_field_types

isFloatableCon (TupleCon _) = return False

isFloatableDataType tenv data_type con_type compute_field_types
  | dataTypeIsAbstract data_type = return False
  | not_length_1 (dataTypeDataConstructors data_type) = return False
  | not_length_1 (dataConFields con_type) = return False
  | otherwise = do
      -- Get the type of the data constructor's single field
      [field_type] <- compute_field_types
      return $!
        case toBaseKind $ typeKind tenv field_type
        of BoxK -> True
           BareK -> True
           ValK ->
             -- Only allow types that are known to fit in a register
             case field_type
             of VarT a -> a `isCoreBuiltin` The_int ||
                          a `isCoreBuiltin` The_float ||
                          a `isCoreBuiltin` The_bool
                _ -> False
  where
    not_length_1 :: [a] -> Bool
    not_length_1 [_] = False
    not_length_1 _   = True

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
  type TypeFunctionInfo Flt = TypeFunction
  getTypeEnv = Flt (asks fcTypeEnv)
  assumeWithProperties v ty b (Flt m) = Flt $ local insert_type m
    where
      insert_type ctx =
        ctx {fcTypeEnv = insertTypeWithProperties v ty b $ fcTypeEnv ctx}

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
       if isDictionaryConInst con
         then do
           ty <- inferExpType expression
           joinInContext new_exp $ asLetContext ty
         else return new_exp

     AppE inf op ty_args args ->
       floatAppExp expression inf op ty_args args

     LamE inf f -> do
       ctx_f <- floatFun [] f
       return $ mapContext (\f' -> ExpM $ LamE inf f') ctx_f
     LetE inf pat rhs body ->
       floatLetExp inf pat rhs body
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
     CaseE inf scr alts ->
       floatCaseExp inf scr alts
     ExceptE inf ty -> return $ unitContext expression
     CoerceE inf t1 t2 body -> do
       ctx_body <- floatExp body
       return $ mapContext (\e -> ExpM $ CoerceE inf t1 t2 e) ctx_body
     ArrayE inf ty es -> do
       ctx_es <- mergeList =<< mapM floatExp es
       return $ mapContext (\es -> ExpM $ ArrayE inf ty es) ctx_es

floatAppExp original_expression inf op ty_args args =
  case op
  of ExpM (VarE op_inf op_var) -> do
       -- This may be a floatable term
       ctx_args <- floatExps args
       is_floatable <- isFloatableFunction' op_var ctx_args
       if is_floatable
         then do
           -- Float this application term
           let new_exp =
                 mapContext (make_app (ExpM $ VarE op_inf op_var)) ctx_args
           ty <- inferExpType original_expression
           joinInContext new_exp $ asLetContext ty

         else don't_float (unitContext op) ctx_args

     _ -> do
       -- Not floatable
       ctx_op <- floatExp op
       ctx_args <- floatExps args
       don't_float ctx_op ctx_args
  where
    make_app new_op new_args = ExpM $ AppE inf new_op ty_args new_args

    don't_float ctx_op ctx_args =
      mergeWith make_app ctx_op ctx_args

-- | Perform floating in a case expression.
--
--   The entire expression should be floated if
--
--   1. The scrutinee is a variable
--   2. The data type is cheap to deconstruct (see 'isFloatableDecon').
floatCaseExp inf scr alts =
  case scr
  of ExpM (VarE {}) -> do
       tenv <- getTypeEnv
       case alts of
         [AltM (Alt decon params body)] -> do
           floatable <- isFloatableDecon decon 
           if floatable
             then float decon params body
             else don't_float
         _ -> don't_float
     _ -> don't_float
  where
    don't_float = do
      ctx_scr <- floatExp scr
      ctx_alts <- mergeList =<< mapM floatAlt alts
      let make_new_exp scr' alts' = ExpM $ CaseE inf scr' alts'
      mergeWith make_new_exp ctx_scr ctx_alts

    float decon params body = do
      -- Since the case binding will be floated outwards,
      -- bound variables must be given fresh names
      (decon', decon_rn) <- freshenDeConInst decon
      renamePatMs decon_rn params $ \rn1 params1 -> do
        (params', params_rn) <- freshenPatMs params1
        let rn = params_rn `Rename.compose` decon_rn
        let body' = Rename.rename rn body

        -- Float this case binding.  The body stays here.
        ctx_body <- assumeBinders (deConExTypes decon') $
                    assumePatMs params' $
                    floatExp body'
        return $
          caseContext False inf scr decon' params' [] ctx_body

-- When floating let expressions, we take care to ensure that floating in the
-- body is not restricted.  Consider the expression
--
-- > let x = A
-- > let y = B x
-- > C
--
-- If A is floated, then 'floatLetExp' will remove the binding of x and
-- rename x, so that floating of 'B x' is not blocked by the let-binding that
-- defines x.

floatLetExp inf pat rhs body = do
  ctx_rhs <- floatExp rhs

  -- Check whether the RHS is a single variable (which probably means
  -- the RHS has been floated).  If so, eliminate this let-binding.
  case discardContext ctx_rhs of
    ExpM (VarE {}) -> joinInContext ctx_rhs $ \(ExpM (VarE _ rhs_var)) -> do
      -- Rename the pattern variable to 'rhs_var'
      let rn = Rename.singleton (patMVar pat) rhs_var
      floatExp $ Rename.rename rn body
    _ -> do
      -- Cannot eliminate the let-binding
      ctx_body <- enterScope1 pat (inferExpType body) $ floatExp body
      mergeWith make_let ctx_rhs ctx_body
  where
    make_let rhs' body' = ExpM $ LetE inf pat rhs' body'

floatAlt :: AltM -> Flt (Contexted AltM)
floatAlt (AltM (Alt decon params body)) = do
  ctx_body <- enterScope' (deConExTypes decon) params (inferExpType body) $
              floatExp body
  return $ mapContext (\e -> AltM $ Alt decon params e) ctx_body

-- | Perform floating in a function.
--
--   If the function is part of a recursive definition group, the binder list
--   is the list of all functions bound in the definition group.  References
--   to those functions can't be floated out of the function body.
floatFun :: [Binder] -> FunM -> Flt (Contexted FunM)
floatFun fun_binders (FunM f@(Fun inf ty_params params return_type body)) = do
  fun_body <-
    enterScopeOfVars fun_binders get_return_type $
    enterScope' [p | TyPat p <- ty_params] params get_return_type $
    floatExp body
  return $ mapContext (\e -> FunM $ f {funBody = e}) fun_body
  where
    get_return_type = return return_type

-- | Perform floating in a top-level function.  Nothing is floated out of
--   the function.
floatTopLevelFun :: FunM -> Flt FunM
floatTopLevelFun (FunM f@(Fun inf ty_params params return_type body)) =
  assumeBinders [p | TyPat p <- ty_params] $ 
  assumePatMs params $ do
    ctx_body <- floatExp body
    body <- contextExpression ctx_body return_type
    return $ FunM (f {funBody = body})

floatTopLevelEnt (FunEnt f) = FunEnt `liftM` floatTopLevelFun f
floatTopLevelEnt (DataEnt d) = return (DataEnt d)

-- | Perform floating in a top-level definition group
floatTopLevelGroup :: DefGroup (GDef Mem)
                   -> (DefGroup (GDef Mem) -> Flt a)
                   -> Flt a
floatTopLevelGroup (NonRec def) k = do
  f <- floatTopLevelEnt $ definiens def
  let def' = def {definiens = f}
  assume (definiendum def) (entityType f) $ k (NonRec def')

floatTopLevelGroup (Rec defs) k = assume_defs $ do
  fs <- mapM (floatTopLevelEnt . definiens) defs
  let defs' = [def {definiens = f} | (def, f) <- zip defs fs]
  k (Rec defs')
  where
    assume_defs m = foldr assume_def m defs
    assume_def def = assume (definiendum def) (entityType $ definiens def)

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
    assume_import def = assume (definiendum def) (entityType $ definiens def)

longRangeFloating :: Module Mem -> IO (Module Mem)
longRangeFloating mod =
  withTheNewVarIdentSupply $ \var_supply -> do
    tenv <- readInitGlobalVarIO the_memTypes
    runFlt (floatModule mod) var_supply tenv