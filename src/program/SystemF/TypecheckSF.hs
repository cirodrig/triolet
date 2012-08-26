
{-# LANGUAGE ScopedTypeVariables, TypeFamilies, EmptyDataDecls,
             FlexibleInstances, DeriveDataTypeable, TypeSynonymInstances #-}
module SystemF.TypecheckSF
       (functionType,
        typeCheckModule,
        inferExpType)
where

import Prelude hiding(mapM)

import Control.Applicative(Const(..))
import Control.Exception
import Control.Monad hiding(mapM)
import Control.Monad.Reader hiding(mapM)
import qualified Data.List as List
import Data.Traversable(mapM)
import Data.Typeable(Typeable)
import Data.Maybe
import qualified Data.Set as Set
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import Common.Supply
import Common.SourcePos

import GlobalVar
import Globals
import SystemF.Print
import SystemF.Syntax
import SystemF.Typecheck
import Builtins.Builtins
import Type.Eval
import Type.Environment
import Type.Type
import qualified Type.Rename as Rename
import Type.Compare

tyPatType :: TyPat -> Type
tyPatType (TyPat (_ ::: t)) = t

patType :: PatSF -> Type
patType (VarP _ t) = t

functionType :: FunSF -> Type 
functionType (FunSF (Fun { funTyParams = ty_params
                         , funParams = params
                         , funReturn = ret
                         })) =
  forallType [b | TyPat b <- ty_params] $
  funType [patType p | p <- params] ret

-------------------------------------------------------------------------------

assumePat :: PatSF -> TCM b -> TCM b
assumePat p k =
  case p
  of VarP v p_ty -> do
       typeInferType p_ty
       assume v p_ty k

assumePats pats m = foldr assumePat m pats

assumeTyPat :: TyPat -> TCM b -> TCM b
assumeTyPat (TyPat (v ::: t)) k = do
  t' <- typeInferType t
  assume v t k

-- Assume a function definition.  Do not check the function definition's body.
assumeDef :: FDef SF -> TCM a -> TCM a
assumeDef (Def v _ fun) = assume v (functionType fun)

assumeDefs defs m = foldr assumeDef m (defGroupMembers defs)

assumeGDef :: GDef SF -> TCM a -> TCM a
assumeGDef (Def v _ ent) =
  let ty = case ent
           of FunEnt f -> functionType f
              DataEnt d -> constType d
  in assume v ty

assumeGDefs defs m = foldr assumeGDef m (defGroupMembers defs)

typeInferType :: Type -> TCM Kind
typeInferType = typeCheckType

typeInferExp :: ExpSF -> TCM Type
typeInferExp (ExpSF expression) =
    case expression
    of VarE {expInfo = inf, expVar = v} ->
         typeInferVarE inf v
       ConE inf op args ->
         typeInferConE inf op args
       LitE {expInfo = inf, expLit = l} ->
         typeInferLitE inf l
       AppE {expInfo = inf, expOper = op, expTyArgs = ts, expArgs = args} ->
         typeInferAppE (ExpSF expression) inf op ts args
       LamE {expInfo = inf, expFun = f} -> do
         typeInferFun f
       LetE {expInfo = inf, expBinder = pat, expValue = e, expBody = body} ->
         typeInferLetE inf pat e body
       LetfunE {expInfo = inf, expDefs = defs, expBody = body} ->
         typeInferLetfunE inf defs body
       CaseE {expInfo = inf, expScrutinee = scr, expAlternatives = alts} ->
         typeInferCaseE inf scr alts
       ExceptE {expType = ty} -> do
         typeCheckType ty
         return ty
       CoerceE {expInfo = inf, expArgType = from_ty, expRetType = to_ty,
                expBody = body} ->
         typeInferCoerceE inf from_ty to_ty body
       ArrayE {expInfo = inf, expType = ty, expElements = es} ->
         typeInferArrayE inf ty es
         
-- To infer a variable's type, just look it up in the environment
typeInferVarE :: ExpInfo -> Var -> TCM Type
typeInferVarE inf var = do
  tenv <- getTypeEnv
  when (isJust $ lookupDataCon var tenv) $
    internalError $ "typeInferVarE: Data constructor used as variable: " ++ show var

  lookupVar var

-- Use the type that was attached to the literal value, but also verify that
-- it's a valid type
typeInferLitE :: ExpInfo -> Lit -> TCM Type
typeInferLitE inf l = do
  -- Check that type is valid
  let literal_type = literalType l
  checkLiteralType l
  return literal_type

typeInferConE inf con@(VarCon op ty_args ex_types) args = do
  let pos = getSourcePos inf
  -- Get constructor's type
  dcon_type <- tcLookupDataCon op
  
  -- Check type arguments
  check_type_args 1 (dataConPatternParams dcon_type) ty_args
  check_type_args (1 + length ty_args) (dataConPatternExTypes dcon_type)
    ex_types

  -- Get the argument types
  (expected_arg_types, ret_type) <-
    instantiateDataConTypeWithExistentials dcon_type (ty_args ++ ex_types)

  -- Apply to other arguments
  arg_types <- mapM typeInferExp args
  check_args expected_arg_types arg_types
  return ret_type
  where
    pos = getSourcePos inf
    check_type_args first binders givens
      | length binders /= length givens =
          typeError $ MiscError pos (text "Wrong number of type arguments to data constructor")
      | otherwise =
          sequence_ $ zipWith3 check_type_arg [first..] binders givens

    check_type_arg i (_ ::: expected_kind) ty = do
      k <- typeInferType ty
      checkType (typeArgKindMismatch pos i) expected_kind k

    check_args expected given
      | length expected /= length given =
          typeError $ MiscError pos (text "Wrong number of fields given to data constructor")
      | otherwise =
          sequence_ $ zipWith3 check_arg [1..] expected given

    check_arg i e g =
      checkType (conFieldTypeMismatch pos i) e g

typeInferAppE orig_expr inf op ty_args args = do
  let pos = getSourcePos inf
  op_type <- typeInferExp op

  -- Apply to type arguments
  ty_arg_kinds <- mapM typeInferType ty_args
  inst_type <- computeInstantiatedType pos op_type (zip ty_arg_kinds ty_args)

  -- Apply to other arguments
  arg_types <- mapM typeInferExp args
  computeAppliedType pos inst_type arg_types

computeInstantiatedType :: SourcePos -> Type -> [(Kind, Type)] -> TCM Type
computeInstantiatedType inf op_type_ all_args = go 1 op_type_ all_args
  where
    go index op_type ((arg_kind, arg) : args) = do
      -- Apply operator to argument
      app_type <- typeOfTypeApp op_type arg_kind arg
      case app_type of
        TypeAppOk result_type -> go (index + 1) result_type args
        KindMismatchErr e a   -> kind_mismatch index e a
        NotAForallErr         -> not_a_forall op_type arg_kind

    go _ op_type [] = return op_type

    kind_mismatch i e a = typeError $ typeArgKindMismatch inf i e a
    not_a_forall op_type arg_kind = typeError $ BadTyApp inf op_type arg_kind

-- | Given a function type and a list of argument types, compute the result of
-- applying the function to the arguments.
computeAppliedType :: SourcePos 
                   -> Type
                   -> [Type] 
                   -> TCM Type
computeAppliedType pos op_type arg_types =
  apply 1 op_type arg_types
  where
    apply index op_type (arg_t:arg_ts) = do
      result <- typeOfApp op_type arg_t
      case result of
        AppOk op_type'      -> apply (index + 1) op_type' arg_ts
        TypeMismatchErr e a -> type_mismatch index e a
        NotAFunctionErr     -> not_a_function op_type arg_t
    
    apply _ op_type [] = return op_type
    
    type_mismatch i e a = typeError $ argTypeMismatch pos i e a
    not_a_function op_type arg_t = typeError $ BadApp pos op_type arg_t

typeInferFun :: FunSF -> TCM Type
typeInferFun fun@(FunSF (Fun { funInfo = info
                             , funTyParams = ty_params
                             , funParams = params
                             , funReturn = return_type
                             , funBody = body})) =
  assumeTyParams $ assumePats params $ do
    body_type <- typeInferExp body
    typeInferType return_type
    
    -- Inferred type must match return type
    checkType (returnTypeMismatch (getSourcePos info)) return_type body_type
    
    -- Create the function's type
    return $ functionType fun
  where
    assumeTyParams m = foldr assumeTyPat m ty_params

typeInferLetE :: ExpInfo -> PatSF -> ExpSF -> ExpSF -> TCM Type
typeInferLetE inf pat@(VarP v pat_type) expression body = do
  ti_exp <- typeInferExp expression
  
  -- Expression type must match pattern type
  checkType (binderTypeMismatch (getSourcePos inf) v) ti_exp pat_type

  -- Assume the pattern while inferring the body; result is the body's type
  assumePat pat $ typeInferExp body

typeInferLetfunE :: ExpInfo -> DefGroup (FDef SF) -> ExpSF -> TCM Type
typeInferLetfunE inf defs body =
  typeCheckDefGroup defs $ typeInferExp body

typeInferCaseE :: ExpInfo -> ExpSF -> [AltSF] -> TCM Type
typeInferCaseE inf scr alts = do
  let pos = getSourcePos inf

  -- Get the scrutinee's type
  scr_type <- typeInferExp scr

  -- Match against each alternative
  when (null alts) $ typeError (emptyCaseError pos)
  (first_type:other_types) <- mapM (typeCheckAlternative pos scr_type) alts

  -- All alternatives must match
  forM_ (zip [2..] other_types) $ \(i, t) ->
    checkType (inconsistentCaseAlternatives pos i) first_type t

  -- The expression's type is the type of an alternative
  return first_type

typeCheckAlternative :: SourcePos -> Type -> Alt SF -> TCM Type
typeCheckAlternative pos scr_type (AltSF (Alt con fields body)) = do
  -- Data constructors are always constructor variables
  let VarDeCon con_var types ex_fields = con
      existential_vars = [v | v ::: _ <- ex_fields]

  -- Process arguments
  type_kinds <- mapM typeInferType types

  -- Apply constructor to type arguments
  con_ty <- tcLookupDataCon con_var
  (_, arg_types, con_scr_type) <-
    let argument_types = zip types type_kinds
        existential_types = [(v, kind) | v ::: kind <- ex_fields]
    in instantiatePatternType pos con_ty argument_types existential_types

  -- Verify that applied type matches constructor type
  checkType (scrutineeTypeMismatch pos) con_scr_type scr_type
  
  -- Add existential types to environment
  assumeBinders ex_fields $ do

    -- Verify that fields have the expected types
    check_number_of_fields arg_types fields
    zipWithM_ (checkAltParam pos) arg_types fields

    -- Match the resulting type against the function type
    -- field1 -> field2 -> ... -> scr_type
    ret_type <- bindParamTypes fields $ typeInferExp body

    -- Existential types must not escape
    when (ret_type `typeMentionsAny` Set.fromList existential_vars) $
      -- Pick one existential type to report in the error message
      let Just v = List.find (ret_type `typeMentions`) existential_vars
      in typeError $ typeVariableEscapes pos v

    return ret_type
  where
    check_number_of_fields atypes fs
      | length atypes /= length fields =
        internalError $ "typeCheckAlternative: Wrong number of fields in pattern (expected " ++
        show (length atypes) ++ ", got " ++ show (length fields) ++ ")"
      | otherwise = return ()

bindParamTypes params m = foldr bind_param_type m params
  where
    bind_param_type (VarP param param_ty) m =
      assume param param_ty m

-- | Verify that the given paramater matches the expected parameter
checkAltParam pos expected_type (VarP field_var given_type) = do
  typeInferType given_type
  checkType (binderTypeMismatch pos field_var) expected_type given_type

typeInferCoerceE inf from_ty to_ty body = do
  typeCheckType from_ty
  typeCheckType to_ty

  -- Verify that body type matches the given type
  body_ty <- typeInferExp body
  checkType (coercionTypeMismatch (getSourcePos inf)) from_ty body_ty

  return to_ty

typeInferArrayE inf ty es = do
  typeCheckType ty

  -- Infer each element type
  tys <- mapM typeInferExp es

  -- Elements must have the same type
  let message = text "Expecting array element to have type " <+> pprType ty
  forM_ (zip [0..] tys) $ \(i, g_ty) ->
    checkType (arrayConTypeMismatch (getSourcePos inf) i) ty g_ty

  -- Return an array type
  let len = IntT $ fromIntegral $ length es
  return $ varApp (coreBuiltin The_arr) [len, ty]

typeCheckEntity (FunEnt f) = void $ typeInferFun f

typeCheckEntity (DataEnt (Constant inf ty e)) = do
  typeCheckType ty 
  expression_type <- typeInferExp e
  checkType (constantTypeMismatch (getSourcePos inf)) ty expression_type

typeCheckDefGroup :: DefGroup (FDef SF) -> TCM b -> TCM b
typeCheckDefGroup defgroup k = 
  case defgroup
  of NonRec def -> do
       typeCheckDef def
       assumeDefs defgroup k
     Rec defs -> assumeDefs defgroup $ do
       mapM_ typeCheckDef defs
       k
  where
    -- To typecheck a definition, check the function it contains
    typeCheckDef def = typeInferFun $ definiens def

typeCheckGlobalDefGroup :: DefGroup (GDef SF) -> TCM b -> TCM b
typeCheckGlobalDefGroup defgroup k =
  case defgroup
  of NonRec def -> do
       typeCheckGlobalDef def
       assumeGDefs defgroup k
     Rec defs -> assumeGDefs defgroup $ do
       mapM_ typeCheckGlobalDef defs
       k
  where
    -- To typecheck a definition, check the function it contains
    typeCheckGlobalDef def = typeCheckEntity $ definiens def

typeCheckExport :: Export SF -> TCM ()
typeCheckExport (Export pos spec f) = do
  typeInferFun f
  return ()

typeCheckModule (Module module_name [] defs exports) = do
  global_type_env <- readInitGlobalVarIO the_systemFTypes
  withTheNewVarIdentSupply $ \varIDs -> do
    let typecheck = typeCheckDefGroups defs exports
    runTypeEvalM typecheck varIDs global_type_env
  where
    typeCheckDefGroups (defs:defss) exports = 
      typeCheckGlobalDefGroup defs $ typeCheckDefGroups defss exports
      
    typeCheckDefGroups [] exports = do 
      mapM_ typeCheckExport exports

typeCheckModule (Module {modImports = _:_}) =
  internalError "typeCheckModule: Import list is not empty"

-- | Infer the type of an expression.  The expression is assumed to be
--   well-typed; this function doesn't check for most errors.
inferExpType :: IdentSupply Var -> TypeEnv -> ExpSF -> IO Type
inferExpType id_supply tenv expression =
  runTypeEvalM (infer_exp expression) id_supply tenv
  where
    -- Get the return type of an expression.  Skip parts that don't matter 
    -- to the return type.  Variable bindings are added to the environment,
    -- but their definitions are skipped.
    infer_exp expression =
      case fromExpSF expression
      of LamE _ f -> return $ functionType f
         LetE _ pat e body ->
           assumePat pat $ infer_exp body
         LetfunE _ defs body ->
           assumeDefs defs $ infer_exp body
         CaseE _ _ (alt : _) ->
           infer_alt alt
         ExceptE _ rt ->
           return rt
         _ ->
           typeInferExp expression

    infer_alt (AltSF alt) =
      assumeBinders (getAltExTypes alt) $
      assumePats (altParams alt) $
      infer_exp $ altBody alt
