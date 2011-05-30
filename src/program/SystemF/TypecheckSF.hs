
{-# LANGUAGE ScopedTypeVariables, TypeFamilies, EmptyDataDecls,
             FlexibleInstances, DeriveDataTypeable, TypeSynonymInstances #-}
module SystemF.TypecheckSF
       (Typed,
        TypeAnn(..),
        HasType(..),
        Typ(..),
        Exp(..),
        Alt(..),
        Fun(..),
        Pat(..),
        TyPat(..),
        TypTSF, ExpTSF, AltTSF, FunTSF, PatTSF,
        fromTypTSF,
        functionType,
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
import Type.Rename
import Type.Compare

newtype instance Typ (Typed SF) = TypTSF (TypeAnn Type)
newtype instance Exp (Typed SF) = ExpTSF (TypeAnn (BaseExp TSF))
newtype instance Alt (Typed SF) = AltTSF (TypeAnn (BaseAlt TSF))
newtype instance Fun (Typed SF) = FunTSF (TypeAnn (BaseFun TSF))

data instance Pat (Typed SF) =
    TypedWildP TypTSF
  | TypedVarP Var TypTSF
  | TypedTupleP [Pat (Typed SF)]

data instance TyPat (Typed SF) = TyPatTSF Var TypTSF

type TSF = Typed SF

type TypTSF = Typ TSF
type ExpTSF = Exp TSF
type AltTSF = Alt TSF
type FunTSF = Fun TSF
type PatTSF = Pat TSF
type TyPatTSF = TyPat TSF

instance HasType TypTSF where
  getTypeAnn (TypTSF x) = typeAnnotation x

instance HasType ExpTSF where
  getTypeAnn (ExpTSF x) = typeAnnotation x

instance HasType AltTSF where
  getTypeAnn (AltTSF x) = typeAnnotation x

instance HasType FunTSF where
  getTypeAnn (FunTSF x) = typeAnnotation x

fromTypTSF :: TypTSF -> Type 
fromTypTSF (TypTSF (TypeAnn _ t)) = t

tyPatType :: TyPat SF -> Type
tyPatType (TyPatSF (_ ::: t)) = t

patType :: PatSF -> Type
patType (WildP t)  = t
patType (VarP _ t) = t
patType (TupleP ps) = let con = VarT $ pyonTupleTypeCon (length ps)
                          field_types = map patType ps
                      in typeApp con field_types

functionType :: FunSF -> Type 
functionType (FunSF (Fun { funTyParams = ty_params
                         , funParams = params
                         , funReturn = TypSF ret
                         })) =
  forallType [b | TyPatSF b <- ty_params] $
  funType [patType p | p <- params] ret

-------------------------------------------------------------------------------

assumePat :: PatSF -> (PatTSF -> TCM b) -> TCM b
assumePat p k =
  case p
  of WildP p_ty -> k . TypedWildP =<< typeInferType (TypSF p_ty)
     VarP v p_ty -> do
       p_ty' <- typeInferType (TypSF p_ty)
       assume v p_ty $ k (TypedVarP v p_ty')
     TupleP pats -> withMany assumePat pats $ \pats' -> k (TypedTupleP pats')

assumeTyPat :: TyPat SF -> (TyPat TSF -> TCM b) -> TCM b
assumeTyPat (TyPatSF (v ::: t)) k = do
  t' <- typeInferType (TypSF t)
  assume v t $ k (TyPatTSF v t')

-- Assume a function definition.  Do not check the function definition's body.
assumeDef :: Def SF -> TCM a -> TCM a
assumeDef (Def v _ fun) = assume v (functionType fun)

assumeDefs defs m = foldr assumeDef m (defGroupMembers defs)

typeInferType :: TypSF -> TCM TypTSF
typeInferType (TypSF ty) = do
  k <- typeCheckType ty
  return (TypTSF (TypeAnn k ty))

typeInferExp :: ExpSF -> TCM ExpTSF
typeInferExp (ExpSF expression) =
    case expression
    of VarE {expInfo = inf, expVar = v} ->
         typeInferVarE inf v
       LitE {expInfo = inf, expLit = l} ->
         typeInferLitE inf l
       AppE {expInfo = inf, expOper = op, expTyArgs = ts, expArgs = args} ->
         typeInferAppE (ExpSF expression) inf op ts args
       LamE {expInfo = inf, expFun = f} -> do
         ti_fun <- typeInferFun f
         return $ ExpTSF $ TypeAnn (getTypeAnn ti_fun) (LamE inf ti_fun)
       LetE {expInfo = inf, expBinder = pat, expValue = e, expBody = body} ->
         typeInferLetE inf pat e body
       LetfunE {expInfo = inf, expDefs = defs, expBody = body} ->
         typeInferLetfunE inf defs body
       CaseE {expInfo = inf, expScrutinee = scr, expAlternatives = alts} ->
         typeInferCaseE inf scr alts
         
-- To infer a variable's type, just look it up in the environment
typeInferVarE :: ExpInfo -> Var -> TCM ExpTSF
typeInferVarE inf var = do
  ty <- lookupVar var
  return $ ExpTSF $ TypeAnn ty (VarE inf var)

-- Use the type that was attached to the literal value, but also verify that
-- it's a valid type
typeInferLitE :: ExpInfo -> Lit -> TCM ExpTSF
typeInferLitE inf l = do
  -- Check that type is valid
  let literal_type = literalType l
  checkLiteralType l
  return $ ExpTSF $ TypeAnn literal_type (LitE inf l)

typeInferAppE orig_expr inf op ty_args args = do
  let pos = getSourcePos inf
  ti_op <- typeInferExp op
  let op_type = getTypeAnn ti_op

  -- Apply to type arguments
  ti_ty_args <- mapM typeInferType ty_args
  inst_type <- computeInstantiatedType pos op_type ti_ty_args

  -- Apply to other arguments
  ti_args <- mapM typeInferExp args
  result_type <- computeAppliedType pos inst_type (map getTypeAnn ti_args)
  
  let new_exp = AppE inf ti_op ti_ty_args ti_args
  return $ ExpTSF $ TypeAnn result_type new_exp

computeInstantiatedType :: SourcePos -> Type -> [TypTSF] -> TCM Type
computeInstantiatedType inf op_type_ all_args = go op_type_ all_args
  where
    go op_type (TypTSF (TypeAnn arg_kind arg) : args) = do
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
    trace_types = traceShow (hang (text "computeAppliedType") 4 $
                             pprType op_type $$ vcat (map pprType arg_types))

typeInferFun :: FunSF -> TCM FunTSF
typeInferFun fun@(FunSF (Fun { funInfo = info
                             , funTyParams = ty_params
                             , funParams = params
                             , funReturn = return_type
                             , funBody = body})) =
  assumeTyParams $ \new_ty_params -> assumeParams $ \new_params -> do
    ti_body <- typeInferExp body
    ti_return_type <- typeInferType return_type
    
    -- Inferred type must match return type
    checkType (text "Return type mismatch") (getSourcePos info)
      (fromTypSF return_type) (getTypeAnn ti_body)
    
    -- Create the function's type
    let ty = functionType fun
    
    let new_fun =
          Fun { funInfo = info
              , funTyParams = new_ty_params
              , funParams = new_params
              , funReturn = ti_return_type
              , funBody = ti_body
              }
    return $ FunTSF $ TypeAnn ty new_fun
  where
    assumeTyParams = withMany assumeTyPat ty_params
    assumeParams = withMany assumePat params

typeInferLetE :: ExpInfo -> PatSF -> ExpSF -> ExpSF -> TCM ExpTSF
typeInferLetE inf pat expression body = do
  ti_exp <- typeInferExp expression
  
  -- Expression type must match pattern type
  checkType (text "Let binder doesn't match type of right-hand side") (getSourcePos inf)
    (getTypeAnn ti_exp) (patType pat)

  -- Assume the pattern while inferring the body; result is the body's type
  assumePat pat $ \pat' -> do
    ti_body <- typeInferExp body
    let new_exp = LetE inf pat' ti_exp ti_body
    return $ ExpTSF $ TypeAnn (getTypeAnn ti_body) new_exp

typeInferLetfunE :: ExpInfo -> DefGroup (Def SF) -> ExpSF -> TCM ExpTSF
typeInferLetfunE inf defs body =
  typeCheckDefGroup defs $ \defs' -> do
    ti_body <- typeInferExp body
    let new_exp = LetfunE inf defs' ti_body
    return $ ExpTSF $ TypeAnn (getTypeAnn ti_body) new_exp

typeInferCaseE :: ExpInfo -> ExpSF -> [AltSF] -> TCM ExpTSF
typeInferCaseE inf scr alts = do
  let pos = getSourcePos inf

  -- Get the scrutinee's type
  ti_scr <- typeInferExp scr
  let scr_type = getTypeAnn ti_scr
  
  when (null alts) $ typeError "Empty case statement"

  -- Match against each alternative
  ti_alts <- mapM (typeCheckAlternative pos scr_type) alts

  -- All alternatives must match
  let alt_subst_types = map getTypeAnn ti_alts
      msg = text "Case alternatives return different types"
  zipWithM (checkType msg pos) alt_subst_types (tail alt_subst_types)

  -- The expression's type is the type of an alternative
  let result_type = getTypeAnn $ head ti_alts
  return $! ExpTSF $! TypeAnn result_type $ CaseE inf ti_scr ti_alts

typeCheckAlternative :: SourcePos -> Type -> Alt SF -> TCM AltTSF
typeCheckAlternative pos scr_type (AltSF (DeCon { altConstructor = con
                                                , altTyArgs = types
                                                , altExTypes = ex_fields
                                                , altParams = fields
                                                , altBody = body})) = do
  -- Process arguments
  arg_vals <- mapM typeInferType types

  -- Apply constructor to type arguments
  con_ty <- tcLookupDataCon con
  (_, arg_types, con_scr_type) <-
    let argument_types = [(ty, kind) | TypTSF (TypeAnn kind ty) <- arg_vals]
        existential_types = [(v, kind) | TyPatSF (v ::: kind) <- ex_fields]
    in instantiatePatternType pos con_ty argument_types existential_types

  -- Verify that applied type matches constructor type
  checkType (text "Case alternative doesn't match scrutinee type") pos
    scr_type con_scr_type
  
  -- Add existential types to environment
  withMany assumeTyPat ex_fields $ \ex_fields' -> do

    -- Verify that fields have the expected types
    check_number_of_fields arg_types fields
    fields' <- zipWithM (checkAltParam pos) arg_types fields

    -- Match the resulting type against the function type
    -- field1 -> field2 -> ... -> scr_type
    ti_body <- bindParamTypes fields' $ typeInferExp body

    -- The existential type must not escape
    let ret_type = getTypeAnn ti_body
    when (ret_type `typeMentionsAny` Set.fromList existential_vars) $
      typeError "Existential variable escapes"

    let new_alt = DeCon con arg_vals ex_fields' fields' ti_body
    return $ AltTSF $ TypeAnn ret_type new_alt
  where
    -- The existential variables bound by this pattern
    existential_vars = [v | TyPatSF (v ::: _) <- ex_fields]

    check_number_of_fields atypes fs
      | length atypes /= length fields =
        internalError $ "typeCheckAlternative: Wrong number of fields in pattern (expected " ++
        show (length atypes) ++ ", got " ++ show (length fields) ++ ")"
      | otherwise = return ()

typeCheckAlternative pos scr_type (AltSF (DeTuple {})) =
  -- Should not appear in System F code
  internalError "typeCheckAlternative: Unexpected unboxed tuple"

bindParamTypes params m = foldr bind_param_type m params
  where
    bind_param_type (TypedVarP param param_ty) m =
      assume param (fromTypTSF param_ty) m

-- | Verify that the given paramater matches the expected parameter
checkAltParam pos expected_type (VarP field_var given_type) = do
  gt <- typeInferType (TypSF given_type)
  let msg = text "Wrong type in field of pattern"
  checkType msg pos expected_type (fromTypTSF gt)
  return (TypedVarP field_var gt)

typeCheckDefGroup :: DefGroup (Def SF) -> (DefGroup (Def TSF) -> TCM b) -> TCM b
typeCheckDefGroup defgroup k = 
  case defgroup
  of Rec {} ->
       assumeDefs defgroup (k =<< mapM typeCheckDef defgroup)
     NonRec {} ->
       (assumeDefs defgroup . k) =<< mapM typeCheckDef defgroup
  where
    -- To typecheck a definition, check the function it contains
    typeCheckDef def = mapMDefiniens typeInferFun def

typeCheckExport :: Export SF -> TCM (Export TSF) 
typeCheckExport (Export pos spec f) = do
  f' <- typeInferFun f
  return $ Export pos spec f'

typeCheckModule (Module module_name defs exports) = do
  global_type_env <- readInitGlobalVarIO the_systemFTypes
  putStrLn "TypeCheckSF"
  print $ pprTypeEnv global_type_env
  withTheNewVarIdentSupply $ \varIDs -> do
    let typecheck = typeCheckDefGroups defs exports
    (defs', exports') <- runTypeEvalM typecheck varIDs global_type_env
    return $ Module module_name defs' exports'
  where
    typeCheckDefGroups (defs:defss) exports = 
      typeCheckDefGroup defs $ \defs' -> do
        (defss', exports') <- typeCheckDefGroups defss exports
        return (defs' : defss', exports')
      
    typeCheckDefGroups [] exports = do 
      exports' <- mapM typeCheckExport exports
      return ([], exports')

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
           assumePat pat $ \_ -> infer_exp body
         LetfunE _ defs body ->
           assumeDefs defs $ infer_exp body
         CaseE _ _ (alt : _) ->
           infer_alt alt
         ExceptE _ rt ->
           return rt
         _ ->
           fmap getTypeAnn $ typeInferExp expression

    infer_alt (AltSF alt) =
      withMany assumeTyPat (altExTypes alt) $ \_ ->
      withMany assumePat (altParams alt) $ \_ ->
      infer_exp $ altBody alt
