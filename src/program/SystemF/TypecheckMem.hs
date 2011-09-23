
{-# LANGUAGE ScopedTypeVariables, TypeFamilies, EmptyDataDecls,
             FlexibleInstances, DeriveDataTypeable, TypeSynonymInstances #-}
module SystemF.TypecheckMem
       (Typed,
        TypeAnn(..),
        Typ(..),
        Exp(..),
        Alt(..),
        Fun(..),
        Pat(..),
        TyPat(..),
        CInst(..),
        DeCInst(..),
        TypTM, ExpTM, AltTM, FunTM, PatTM, TyPatTM,
        discardTypeAnnotationsExp,
        discardTypeAnnotationsFun,
        fromTypTM,
        fromPatTM,
        functionType,
        typeCheckModule,
        inferExpType,
        inferAppType,
        conInstType,
        deConInstType)
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
import SystemF.PrintMemoryIR
import SystemF.Syntax
import SystemF.MemoryIR
import SystemF.Typecheck
import Builtins.Builtins
import Type.Eval
import Type.Environment
import Type.Type
import qualified Type.Rename as Rename
import qualified Type.Substitute as Substitute
import Type.Compare

newtype instance Typ (Typed Mem) = TypTM (TypeAnn Type)
newtype instance Exp (Typed Mem) = ExpTM (TypeAnn (BaseExp TM))
newtype instance Alt (Typed Mem) = AltTM (TypeAnn (BaseAlt TM))
newtype instance Fun (Typed Mem) = FunTM (TypeAnn (BaseFun TM))
newtype instance CInst (Typed Mem) = CInstTM ConInst
newtype instance DeCInst (Typed Mem) = DeCInstTM DeConInst

data instance Pat (Typed Mem) = TypedMemVarP Binder
data instance TyPat (Typed Mem) = TyPatTM Var TypTM

type TM = Typed Mem

type TypTM = Typ TM
type ExpTM = Exp TM
type AltTM = Alt TM
type FunTM = Fun TM
type PatTM = Pat TM
type TyPatTM = TyPat TM

-- | Get the type of an expression
getExpType :: ExpTM -> Type
getExpType (ExpTM (TypeAnn t _)) = t

-- | Get the kind of a type
getTypType :: TypTM -> Type
getTypType (TypTM (TypeAnn t _)) = t

fromTypTM :: TypTM -> Type 
fromTypTM (TypTM (TypeAnn _ t)) = t

tyPatType :: TyPat Mem -> Type
tyPatType (TyPatM (_ ::: t)) = t

fromTyPatTM :: TyPatTM -> TyPatM
fromTyPatTM (TyPatTM v t) = TyPatM (v ::: fromTypTM t)

fromPatTM :: PatTM -> PatM
fromPatTM (TypedMemVarP binder) = patM binder

-- | Determine the type that a pattern-bound variable has after it's been 
--   bound.
patType :: PatM -> Type
patType = patMType

-- | An abbreviation for the long function name
dtae = discardTypeAnnotationsExp

-- | Remove type annotations from an expression
discardTypeAnnotationsExp :: ExpTM -> ExpM
discardTypeAnnotationsExp (ExpTM (TypeAnn _ expression)) = ExpM $ 
  case expression
  of VarE inf v -> VarE inf v
     LitE inf l -> LitE inf l
     ConE inf (CInstTM con) args -> ConE inf (CInstM con) $ map dtae args
     AppE inf op ty_args args ->
       AppE inf (dtae op) (map (TypM . fromTypTM) ty_args) (map dtae args)
     LamE inf f -> LamE inf $ discardTypeAnnotationsFun f
     LetE inf pat rhs body ->
       LetE inf (fromPatTM pat) (dtae rhs) (dtae body)
     LetfunE inf defs body ->
       let defs' = fmap (mapDefiniens discardTypeAnnotationsFun) defs
       in LetfunE inf defs' (dtae body)
     CaseE inf scr alts ->
       CaseE inf (dtae scr) (map discard_alt alts)
     ExceptE inf rty -> ExceptE inf rty
  where
    discard_alt (AltTM (TypeAnn _ alt)) =
      case alt
      of Alt (DeCInstTM con) params body ->
           AltM $ Alt (DeCInstM con) (map fromPatTM params) (dtae body)

discardTypeAnnotationsFun :: FunTM -> FunM
discardTypeAnnotationsFun (FunTM (TypeAnn _ f)) =
  FunM $ Fun { funInfo = funInfo f
             , funTyParams = map fromTyPatTM $ funTyParams f
             , funParams = map fromPatTM $ funParams f
             , funReturn = TypM $ fromTypTM $ funReturn f
             , funBody = dtae $ funBody f}


-- | Get the type of a function using its parameter and return types.
functionType :: FunM -> Type 
functionType (FunM (Fun { funTyParams = ty_params
                        , funParams = params
                        , funReturn = TypM ret
                        })) =
  forallType [b | TyPatM b <- ty_params] $
  funType (map patMType params) ret

-------------------------------------------------------------------------------

assumeAndAnnotatePat :: PatM -> (PatTM -> TCM b) -> TCM b
assumeAndAnnotatePat (PatM (v ::: ty) _) k =
  assume v ty $ k (TypedMemVarP (v ::: ty))

assumeAndAnnotateTyPat :: TyPat Mem -> (TyPat TM -> TCM b) -> TCM b
assumeAndAnnotateTyPat (TyPatM (v ::: t)) k = do
  t' <- typeInferType (TypM t)
  assume v t $ k (TyPatTM v t')

-- Assume a function definition.  Do not check the function definition's body.
assumeDef :: Def Mem -> TCM a -> TCM a
assumeDef (Def v _ fun) = assume v (functionType fun)

assumeDefs defs m = foldr assumeDef m (defGroupMembers defs)

typeInferType :: TypM -> TCM TypTM
typeInferType (TypM ty) = do
  k <- typeCheckType ty
  return $ TypTM (TypeAnn k ty)

typeInferExp :: ExpM -> TCM ExpTM
typeInferExp (ExpM expression) =
    case expression
    of VarE {expInfo = inf, expVar = v} ->
         typeInferVarE inf v
       LitE {expInfo = inf, expLit = l} ->
         typeInferLitE inf l
       ConE inf con args ->
         typeInferConE (ExpM expression) inf con args
       AppE {expInfo = inf, expOper = op, expTyArgs = ts, expArgs = args} ->
         typeInferAppE (ExpM expression) inf op ts args
       LamE {expInfo = inf, expFun = f} -> do
         ti_fun <- typeInferFun f
         let FunTM (TypeAnn return_type _) = ti_fun
         return $ ExpTM $ TypeAnn return_type (LamE inf ti_fun)
       LetE {expInfo = inf, expBinder = pat, expValue = e, expBody = body} ->
         typeInferLetE inf pat e body
       LetfunE {expInfo = inf, expDefs = defs, expBody = body} ->
         typeInferLetfunE inf defs body
       CaseE {expInfo = inf, expScrutinee = scr, expAlternatives = alts} ->
         typeInferCaseE inf scr alts
       ExceptE {expInfo = inf, expType = rt} ->
         return $ ExpTM $ TypeAnn rt (ExceptE inf rt)
       CoerceE inf from_t to_t body ->
         typeInferCoerceE inf from_t to_t body

-- To infer a variable's type, just look it up in the environment
typeInferVarE :: ExpInfo -> Var -> TCM ExpTM
typeInferVarE inf var = do
  -- It's an internal error if a data constructor appears here
  tenv <- getTypeEnv
  when (isJust $ lookupDataCon var tenv) $
    internalError $ "typeInferVarE: Data constructor used as variable: " ++ show var

  ty <- lookupVar var
  return $ ExpTM $ TypeAnn ty (VarE inf var)

-- Use the type that was attached to the literal value, but also verify that
-- it's a valid type
typeInferLitE :: ExpInfo -> Lit -> TCM ExpTM
typeInferLitE inf l = do
  let literal_type = literalType l
  checkLiteralType l
  return $ ExpTM $ TypeAnn literal_type (LitE inf l)

typeInferConE :: ExpM -> ExpInfo -> CInstM -> [ExpM] -> TCM ExpTM
typeInferConE orig_exp inf (CInstM con) args = do
  (t_con, field_types, result_type) <- typeInferCon con
  
  t_args <- forM (zip args field_types) $ \(arg, field_type) -> do
    t_arg <- typeInferExp arg 
    let message = text "Constructor field has wrong type"
    checkType message (getSourcePos inf) field_type (getExpType t_arg)
    return t_arg

  return $ ExpTM $ TypeAnn result_type (ConE inf t_con t_args)

-- | Infer the type of a constructor instance.  Return the parameter types
--   and return type.
typeInferCon :: EvalMonad m => ConInst -> m (CInst (Typed Mem), [Type], Type)
typeInferCon con@(VarCon op ty_args ex_types) = do
  env <- getTypeEnv
  let Just data_con = lookupDataCon op env
  let Just type_con = lookupDataType (dataConTyCon data_con) env
  (field_types, result_type) <-
    instantiateDataConTypeWithExistentials data_con (ty_args ++ ex_types)

  -- Convert fields to initializers
  tenv <- getTypeEnv
  let field_kinds = dataConFieldKinds tenv data_con
      con_field_types = zipWith make_initializer field_kinds field_types

  -- Convert result type to initializer
  let con_result_type = make_initializer (dataTypeKind type_con) result_type
  return (CInstTM con, con_field_types, con_result_type)
  where
    make_initializer BareK ty =
      FunT (varApp (pyonBuiltin The_OutPtr) [ty]) 
      (varApp (pyonBuiltin The_IEffect) [ty])
    make_initializer _ ty = ty

typeInferCon con@(TupleCon types) = do
  kinds <- liftTypeEvalM $ mapM typeCheckType types

  -- All fields must have value or boxed type 
  let valid_kind (VarT v) = v == valV || v == boxV
      valid_kind _ = False
  unless (all valid_kind kinds) $
    typeError "typeInferCon: Wrong kind in field of unboxed tuple"

  let tuple_type = typeApp (UTupleT $ map toBaseKind kinds) types
  return (CInstTM con, types, tuple_type)

typeInferAppE orig_expr inf op ty_args args = do
  let pos = getSourcePos inf
  ti_op <- typeInferExp op

  -- Apply to type arguments
  ti_ty_args <- mapM typeInferType ty_args
  inst_type <- computeInstantiatedType pos (getExpType ti_op) ti_ty_args

  -- Apply to other arguments
  ti_args <- mapM typeInferExp args
  result_type <-
    computeAppliedType (Just orig_expr) pos inst_type (map getExpType ti_args)
  
  let new_exp = AppE inf ti_op ti_ty_args ti_args
  return $ ExpTM $ TypeAnn result_type new_exp

-- | Compute the type of the result of applying an operator to some
--   type arguments.
computeInstantiatedType :: SourcePos -> Type -> [TypTM] -> TCM Type
computeInstantiatedType inf op_type args_ = go op_type args_
  where
    go op_type (TypTM (TypeAnn arg_kind arg) : args) = do
      app_type <- typeOfTypeApp op_type arg_kind arg
      case app_type of
        Just result_type -> go result_type args
        Nothing -> -- traceShow (text "CIT" <+> (pprType op_type $$ vcat (map (pprType . fromTypM) args_))) $
                   typeError $ "Error in type application at " ++ show inf

    go op_type [] = return op_type

-- | Given a function type and a list of argument types, compute the result of
-- applying the function to the arguments.
computeAppliedType :: Maybe ExpM
                   -> SourcePos
                   -> Type
                   -> [Type]
                   -> TCM Type
computeAppliedType orig_expr pos op_type_ arg_types =
  apply op_type_ arg_types
  where
    apply op_type (arg_t:arg_ts) = do
      result <- typeOfApp op_type arg_t
      case result of
        Just op_type' -> apply op_type' arg_ts
        Nothing -> traceShow debug_message $
                      typeError $ "Error in application at " ++ show pos
    
    apply op_type [] = return op_type
    
    debug_message = text "CAT" <+>
                    (maybe empty pprExp orig_expr $$
                     pprType op_type_ $$
                     vcat [text ">" <+> pprType t | t <- arg_types])

typeInferFun :: FunM -> TCM FunTM
typeInferFun fun@(FunM (Fun { funInfo = info
                            , funTyParams = ty_params
                            , funParams = params
                            , funReturn = return_type
                            , funBody = body})) =
  assumeTyParams $ \new_ty_params -> assumeParams $ \new_params -> do
    ti_body <- typeInferExp body

    -- Inferred type must match return type
    new_ret_type <- typeInferType return_type
    checkType (text "Return type mismatch") (getSourcePos info)
      (fromTypM return_type) (getExpType ti_body)
    
    -- Create the function's type
    let ty = functionType fun
    
    let new_fun =
          Fun { funInfo = info
              , funTyParams = new_ty_params
              , funParams = new_params
              , funReturn = new_ret_type
              , funBody = ti_body
              }
    return $ FunTM $ TypeAnn ty new_fun
  where
    assumeTyParams = withMany assumeAndAnnotateTyPat ty_params
    assumeParams = withMany assumeAndAnnotatePat params

typeInferLetE :: ExpInfo -> PatM -> ExpM -> ExpM -> TCM ExpTM
typeInferLetE inf pat expression body = do
  ti_exp <- typeInferExp expression

  -- Expression type must match pattern type
  checkType (text "Let binder doesn't match type of right-hand side") (getSourcePos inf)
    (getExpType ti_exp) (patType pat)

  -- Assume the pattern while inferring the body; result is the body's type
  assumeAndAnnotatePat pat $ \ti_pat -> do
    ti_body <- typeInferExp body
    let return_type = getExpType ti_body
        new_exp = LetE inf ti_pat ti_exp ti_body
    return $ ExpTM $ TypeAnn return_type new_exp

typeInferLetfunE :: ExpInfo -> DefGroup (Def Mem) -> ExpM -> TCM ExpTM
typeInferLetfunE inf defs body =
  typeCheckDefGroup defs $ \defs' -> do
    ti_body <- typeInferExp body
    let new_exp = LetfunE inf defs' ti_body
    return $ ExpTM $ TypeAnn (getExpType ti_body) new_exp

typeInferCaseE :: ExpInfo -> ExpM -> [AltM] -> TCM ExpTM
typeInferCaseE inf scr alts = do
  let pos = getSourcePos inf

  -- Get the scrutinee's type
  ti_scr <- typeInferExp scr
  let scr_type = getExpType ti_scr
  
  when (null alts) $ typeError "Empty case statement"

  -- Match against each alternative
  ti_alts <- mapM (typeCheckAlternative pos scr_type) alts

  -- All alternatives must match
  let alt_subst_types = [rt | AltTM (TypeAnn rt _) <- ti_alts]
      msg = text "Case alternatives return different types"
  zipWithM (checkType msg pos) alt_subst_types (tail alt_subst_types)
  
  -- The expression's type is the type of an alternative
  let result_type = case head ti_alts of AltTM (TypeAnn rt _) -> rt
  return $! ExpTM $! TypeAnn result_type $ CaseE inf ti_scr ti_alts

-- | Typecheck a pattern match.
--   Return the field types that should be matched and the expected
--   scrutinee type.
typeInferDeCon :: SourcePos 
               -> DeConInst
               -> TCM (DeCInst (Typed Mem), [Type], Type)
typeInferDeCon pos decon@(VarDeCon op ty_args ex_types) = do
  env <- getTypeEnv
  data_con <- tcLookupDataCon op
  
  t_ty_args <- mapM (typeInferType . TypM) ty_args
  let argument_types =
        [(ty, kind) | TypTM (TypeAnn kind ty) <- t_ty_args]
      existential_vars = [(v, k) | v ::: k <- ex_types]
  (_, inst_arg_types, con_scr_type) <-
    instantiatePatternType pos data_con argument_types existential_vars
  return (DeCInstTM decon, inst_arg_types, con_scr_type)

typeInferDeCon pos decon@(TupleDeCon types) = do
  kinds <- mapM typeCheckType types

  -- All fields must have value or boxed type 
  let valid_kind (VarT v) = v == valV || v == boxV
      valid_kind _ = False
  unless (all valid_kind kinds) $
    typeError "typeInferDeCon: Wrong kind in field of unboxed tuple"

  let tuple_type = typeApp (UTupleT $ map toBaseKind kinds) types
  return (DeCInstTM decon, types, tuple_type)

typeCheckAlternative :: SourcePos -> Type -> AltM -> TCM AltTM
typeCheckAlternative pos scr_type alt@(AltM (Alt (DeCInstM con) fields body)) = do
  -- Check constructor type
  (t_con, field_types, expected_scr_type) <- typeInferDeCon pos con
  
  -- Sanity check.  These types cannot be pattern-matched.
  let invalid_type =
        case expected_scr_type
        of FunT {} -> True
           AppT (VarT v) _ | v `isPyonBuiltin` The_OutPtr -> True
                           | v `isPyonBuiltin` The_IEffect -> True
           _ -> False
  when invalid_type $ internalError "typeCheckAlternative: Invalid pattern"

  -- Verify that applied type matches constructor type
  let mismatch_message =
        hang (text "Pattern type doesn't match scrutinee type") 4
        (text "Pattern type:" <+> pprType expected_scr_type $$
         text "Scrutinee type:" <+> pprType scr_type)
  checkType mismatch_message pos scr_type expected_scr_type

  -- Add existential variables to environment
  assumeBinders (deConExTypes con) $ do
    
    -- Verify that fields have the expected types
    check_number_of_fields field_types fields
    zipWithM_ check_arg field_types (zip [1..] fields)

    -- Add fields to enironment
    withMany assumeAndAnnotatePat fields $ \fields' -> do

      -- Infer the body
      ti_body <- typeInferExp body

      -- Make sure existential types don't escape 
      let ret_type = getExpType ti_body
          ex_vars = [v | v ::: _ <- deConExTypes con]
      when (ret_type `typeMentionsAny` Set.fromList ex_vars) $
        typeError "Existential type variable escapes"

      let new_alt = Alt (DeCInstTM con) fields' ti_body
      return $ AltTM $ TypeAnn (getExpType ti_body) new_alt
  where
    check_number_of_fields atypes fs
      | length atypes /= length fields =
        let expected = show (length atypes)
            got = show (length fields)
            location = show pos
        in internalError $ location ++ ": Wrong number of fields in pattern (expected " ++ expected
           ++ ", got " ++ got ++ ")"
      | otherwise = return ()

    check_arg expected_rtype (pat_index, pat) =
      let given_type = patMType pat
          msg = text "Wrong type in field" <+> int pat_index <+> text "of pattern"
      in checkType msg pos expected_rtype given_type

bindParamTypes params m = foldr bind_param_type m params
  where
    bind_param_type (TypedMemVarP (param ::: param_ty)) m =
      assume param param_ty m

-- | Verify that the given parameter matches the expected parameter
checkAltParam pos expected_type pattern = do 
  let given_type = patMType pattern
  checkType pos expected_type given_type
  return $ patMBinder pattern

typeInferCoerceE inf from_t to_t body = do
  from_t' <- typeInferType from_t
  to_t' <- typeInferType to_t
  body' <- typeInferExp body
  
  -- Body type must match the coercion's input type
  checkType (text "Argument of coercion has wrong type") (getSourcePos inf) (fromTypM from_t) (getExpType body')
  
  let new_exp = CoerceE inf from_t' to_t' body'
  return $ ExpTM $ TypeAnn (fromTypM to_t) new_exp
  
typeCheckDefGroup :: DefGroup (Def Mem) -> (DefGroup (Def TM) -> TCM b) -> TCM b
typeCheckDefGroup defgroup k = 
  case defgroup
  of NonRec {} -> (assumeDefs defgroup . k) =<< mapM typeCheckDef defgroup
     Rec {} -> assumeDefs defgroup (k =<< mapM typeCheckDef defgroup)
  where
    -- To typecheck a definition, check the function it contains
    typeCheckDef def = mapMDefiniens typeInferFun def

typeCheckExport :: Export Mem -> TCM (Export TM)
typeCheckExport (Export pos spec f) = do
  f' <- typeInferFun f
  return $ Export pos spec f'

typeCheckModule (Module module_name imports defs exports) = do
  global_type_env <- readInitGlobalVarIO the_memTypes
  withTheNewVarIdentSupply $ \varIDs -> do
    let do_typecheck = typeCheckTopLevel imports defs exports
    (imports', defs', exports') <-
      runTypeEvalM do_typecheck varIDs global_type_env
    return $ Module module_name imports' defs' exports'

typeCheckTopLevel imports defss exports =
  typeCheckDefGroup (Rec imports) $ \(Rec imports') -> do
    (defss', exports') <- typecheck_contents defss
    return (imports', defss', exports')
  where
    typecheck_contents (defs:defss) = 
      typeCheckDefGroup defs $ \defs' -> do
        (defss', exports') <- typecheck_contents defss
        return (defs' : defss', exports')

    typecheck_contents [] = do
      exports' <- mapM typeCheckExport exports
      return ([], exports')

-- | Infer the type of an expression.  The expression is assumed to be
--   well-typed; this function doesn't check for most errors.
inferExpType :: EvalMonad m => ExpM -> m Type
inferExpType expression =
  liftTypeEvalM $ infer_exp expression
  where
    -- Get the return type of an expression.  Skip parts that don't matter 
    -- to the return type.  Variable bindings are added to the environment,
    -- but their definitions are skipped.
    infer_exp expression =
      case fromExpM expression
      of ConE _ (CInstM con) _ ->
           inferConAppType con
         LamE _ f ->
           return $ functionType f
         LetE _ pat e body ->
           assumeAndAnnotatePat pat $ \_ -> infer_exp body
         LetfunE _ defs body ->
           assumeDefs defs $ infer_exp body
         CaseE _ _ (alt : _) ->
           infer_alt alt
         ExceptE _ rt ->
           return rt
         CoerceE {expRetType = TypM rt} ->
           return rt
         _ ->
           fmap getExpType $ typeInferExp expression

    infer_alt (AltM (Alt (DeCInstM con) params body)) =
      assumeBinders (deConExTypes con) $ assumePatMs params $ infer_exp body

    debug = traceShow (text "inferExpType" <+> pprExp expression)

-- | Infer the type of a fully applied data constructor.
--
--   For bare object constructors, it's the type of a writer function.
inferConAppType (VarCon op ty_args _) = do
  -- Get the data type's type
  tenv <- getTypeEnv
  case lookupDataConWithType op tenv of
    Just (data_type, con_type) -> let
      -- Apply the data type constructor to the type arguments 
      app_type = varApp (dataConTyCon con_type) ty_args

      -- Create a writer function type, if it's a bare type
      in return $!
         case dataTypeKind data_type
         of BareK -> varApp (pyonBuiltin The_OutPtr) [app_type] `FunT`
                     varApp (pyonBuiltin The_IEffect) [app_type]
            _ -> app_type

inferConAppType (TupleCon ty_args) = do
  tenv <- getTypeEnv
  let kinds = map (toBaseKind . typeKind tenv) ty_args
  return $ typeApp (UTupleT kinds) ty_args

-- | Infer the type of an application, given the operator type and argument
--   types.  If the application is not well-typed, an exception is raised.
inferAppType :: EvalMonad m =>
                Type            -- ^ Operator type
             -> [TypM]          -- ^ Type arguments
             -> [Type]          -- ^ Operand types
             -> m Type
inferAppType op_type ty_args arg_types =
  liftTypeEvalM $ do
    ti_ty_args <- mapM typeInferType ty_args
    inst_type <- computeInstantiatedType noSourcePos op_type ti_ty_args
    computeAppliedType Nothing noSourcePos inst_type arg_types
  where

    debug = traceShow (text "inferAppType" <+> types)
      where
        types = pprType op_type $$
                vcat (map ((text "@" <+>) . pprType . fromTypM) ty_args) $$
                vcat (map ((text ">" <+>) . pprType) arg_types)

-- | Get the parameter types and result type of a data constructor application.
conInstType :: EvalMonad m => ConInst -> m ([Type], Type)
conInstType c = do
  (_, arg_types, result_type) <- typeInferCon c
  return (arg_types, result_type)

-- | Get the type described by a 'DeConInst'.
deConInstType :: EvalMonad m => DeConInst -> m Type
deConInstType mono_con =
  liftTypeEvalM $
  case mono_con
  of VarDeCon con ty_args ex_types -> do
       op_type <- tcLookupDataCon con
       let ex_args = [VarT a | a ::: _ <- ex_types]
       (_, ret_type) <-
         instantiateDataConTypeWithExistentials op_type (ty_args ++ ex_args)
       return ret_type
     TupleDeCon field_types -> do
       tenv <- getTypeEnv
       let field_kinds = map (toBaseKind . typeKind tenv) field_types
       return $ typeApp (UTupleT field_kinds) field_types