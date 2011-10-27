
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
assumeDef :: Def SF -> TCM a -> TCM a
assumeDef (Def v _ fun) = assume v (functionType fun)

assumeDefs defs m = foldr assumeDef m (defGroupMembers defs)

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
  op_type <- lookupVar op
  
  -- Apply to type arguments
  ty_arg_kinds <- mapM typeInferType ty_args
  ex_type_kinds <- mapM typeInferType ex_types
  inst_type <- computeInstantiatedType pos op_type (zip ty_arg_kinds ty_args ++ zip ex_type_kinds ex_types)

  -- Apply to other arguments
  arg_types <- mapM typeInferExp args
  computeAppliedType pos inst_type arg_types

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
computeInstantiatedType inf op_type_ all_args = go op_type_ all_args
  where
    go op_type ((arg_kind, arg) : args) = do
      -- Apply operator to argument
      app_type <- typeOfTypeApp op_type arg_kind arg
      case app_type of
        Just result_type -> go result_type args
        Nothing -> typeError "Error in type application"

    go op_type [] = return op_type

-- | Given a function type and a list of argument types, compute the result of
-- applying the function to the arguments.
computeAppliedType :: SourcePos 
                   -> Type
                   -> [Type] 
                   -> TCM Type
computeAppliedType pos op_type arg_types =
  apply op_type arg_types
  where
    apply op_type (arg_t:arg_ts) = do
      result <- typeOfApp op_type arg_t
      case result of
        Just op_type' -> apply op_type' arg_ts
        Nothing -> typeError $ "Error in application at " ++ show pos
    
    apply op_type [] = return op_type
    
    -- For debugging
    trace_types arg_t =
      traceShow
      (hang (text "computeAppliedType") 4 $
       parens (pprType arg_t) $$
       pprType op_type $$ vcat [text ">" <+> pprType t | t <- arg_types])

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
    checkType (text "Return type mismatch") (getSourcePos info)
      return_type body_type
    
    -- Create the function's type
    return $ functionType fun
  where
    assumeTyParams m = foldr assumeTyPat m ty_params

typeInferLetE :: ExpInfo -> PatSF -> ExpSF -> ExpSF -> TCM Type
typeInferLetE inf pat expression body = do
  ti_exp <- typeInferExp expression
  
  -- Expression type must match pattern type
  checkType (text "Let binder doesn't match type of right-hand side") (getSourcePos inf)
    ti_exp (patType pat)

  -- Assume the pattern while inferring the body; result is the body's type
  assumePat pat $ typeInferExp body

typeInferLetfunE :: ExpInfo -> DefGroup (Def SF) -> ExpSF -> TCM Type
typeInferLetfunE inf defs body =
  typeCheckDefGroup defs $ typeInferExp body

typeInferCaseE :: ExpInfo -> ExpSF -> [AltSF] -> TCM Type
typeInferCaseE inf scr alts = do
  let pos = getSourcePos inf

  -- Get the scrutinee's type
  scr_type <- typeInferExp scr

  when (null alts) $ typeError "Empty case statement"

  -- Match against each alternative
  alt_types <- mapM (typeCheckAlternative pos scr_type) alts

  -- All alternatives must match
  let msg = text "Case alternatives return different types"
  zipWithM (checkType msg pos) alt_types (tail alt_types)

  -- The expression's type is the type of an alternative
  return $! head alt_types

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
  checkType (text "Case alternative doesn't match scrutinee type") pos
    scr_type con_scr_type
  
  -- Add existential types to environment
  assumeBinders ex_fields $ do

    -- Verify that fields have the expected types
    check_number_of_fields arg_types fields
    zipWithM_ (checkAltParam pos) arg_types fields

    -- Match the resulting type against the function type
    -- field1 -> field2 -> ... -> scr_type
    ret_type <- bindParamTypes fields $ typeInferExp body

    -- The existential type must not escape
    when (ret_type `typeMentionsAny` Set.fromList existential_vars) $
      typeError "Existential variable escapes"

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
  let msg = text "Wrong type in field of pattern"
  checkType msg pos expected_type given_type

typeCheckDefGroup :: DefGroup (Def SF) -> TCM b -> TCM b
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
      typeCheckDefGroup defs $ typeCheckDefGroups defss exports
      
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
