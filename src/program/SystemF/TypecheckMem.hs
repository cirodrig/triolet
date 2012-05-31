
{-# LANGUAGE ScopedTypeVariables, TypeFamilies, EmptyDataDecls,
             FlexibleInstances, DeriveDataTypeable, TypeSynonymInstances #-}
module SystemF.TypecheckMem
       (functionType,
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

arrayInitializerType len element_type =
  let length_type = IntT $ fromIntegral len
      arr_type = varApp (coreBuiltin The_arr) [length_type, element_type]
  in varApp (coreBuiltin The_OutPtr) [arr_type] `FunT`
     VarT (coreBuiltin The_Store)

assumeAndAnnotatePat :: PatM -> TCM b -> TCM b
assumeAndAnnotatePat (PatM (v ::: ty) _) k = do
  typeCheckType ty              -- Verify that type is well-formed
  assume v ty k

assumeAndAnnotatePats pats m = foldr assumeAndAnnotatePat m pats

assumeAndAnnotateTyPat :: TyPat -> TCM b -> TCM b
assumeAndAnnotateTyPat (TyPat (v ::: t)) k = do
  typeCheckType t               -- Verify that kind is well-formed
  assume v t k

assumeDefs defs m = foldr assumeFDef m (defGroupMembers defs)

typeInferType :: Type -> TCM Kind
typeInferType = typeCheckType

typeInferExp :: ExpM -> TCM Type
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
         typeInferFun f
       LetE {expInfo = inf, expBinder = pat, expValue = e, expBody = body} ->
         typeInferLetE inf pat e body
       LetfunE {expInfo = inf, expDefs = defs, expBody = body} ->
         typeInferLetfunE inf defs body
       CaseE {expInfo = inf, expScrutinee = scr, expAlternatives = alts} ->
         typeInferCaseE inf scr alts
       ExceptE {expInfo = inf, expType = rt} -> do
         typeCheckType rt
         return rt
       CoerceE inf from_t to_t body ->
         typeInferCoerceE inf from_t to_t body
       ArrayE inf ty es ->
         typeInferArray inf ty es

-- To infer a variable's type, just look it up in the environment
typeInferVarE :: ExpInfo -> Var -> TCM Type
typeInferVarE inf var = do
  -- It's an internal error if a data constructor appears here
  tenv <- getTypeEnv
  when (isJust $ lookupDataCon var tenv) $
    internalError $ "typeInferVarE: Data constructor used as variable: " ++ show var

  lookupVar var

-- Use the type that was attached to the literal value, but also verify that
-- it's a valid type
typeInferLitE :: ExpInfo -> Lit -> TCM Type
typeInferLitE inf l = do
  let literal_type = literalType l
  checkLiteralType l
  return literal_type

typeInferConE :: ExpM -> ExpInfo -> ConInst -> [ExpM] -> TCM Type
typeInferConE orig_exp inf con args = do
  (field_types, result_type) <- typeInferCon con

  -- Verify that argument types match
  forM_ (zip3 [1..] args field_types) $ \(index, arg, field_type) -> do
    arg_type <- typeInferExp arg
    let message = text "Constructor field" <+> int index <+> text "has wrong type"
    checkType message (getSourcePos inf) field_type arg_type

  return result_type

-- | Infer the type of a constructor instance.  Return the parameter types
--   and return type.
typeInferCon :: EvalMonad m => ConInst -> m ([Type], Type)
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
  return (con_field_types, con_result_type)
  where
    make_initializer BareK ty =
      varApp (coreBuiltin The_OutPtr) [ty] `FunT` VarT (coreBuiltin The_Store)
    make_initializer _ ty = ty

typeInferCon con@(TupleCon types) = do
  kinds <- liftTypeEvalM $ mapM typeCheckType types

  -- All fields must have value or boxed type 
  let valid_kind (VarT v) = v == valV || v == boxV
      valid_kind _ = False
  unless (all valid_kind kinds) $
    typeError "typeInferCon: Wrong kind in field of unboxed tuple"

  let tuple_type = typeApp (UTupleT $ map toBaseKind kinds) types
  return (types, tuple_type)

typeInferAppE orig_expr inf op ty_args args = do
  let pos = getSourcePos inf
  op_type <- typeInferExp op

  -- Apply to type arguments
  ty_arg_kinds <- mapM typeInferType ty_args
  inst_type <- computeInstantiatedType pos op_type (zip ty_arg_kinds ty_args)

  -- Apply to other arguments
  arg_types <- mapM typeInferExp args
  computeAppliedType (Just orig_expr) pos inst_type arg_types

-- | Compute the type of the result of applying an operator to some
--   type arguments.
computeInstantiatedType :: SourcePos -> Type -> [(Kind, Type)] -> TCM Type
computeInstantiatedType inf op_type args_ = go op_type args_
  where
    go op_type ((arg_kind, arg) : args) = do
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

typeInferFun :: FunM -> TCM Type
typeInferFun fun@(FunM (Fun { funInfo = info
                            , funTyParams = ty_params
                            , funParams = params
                            , funReturn = return_type
                            , funBody = body})) = do

  -- Check types in the function
  assumeTyParams $ assumeAndAnnotatePats params $ do
    ti_body <- typeInferExp body

    -- Inferred type must match return type
    new_ret_type <- typeInferType return_type
    checkType (text "Return type mismatch") (getSourcePos info)
      return_type ti_body
    
  -- Create the function's type
  return $ functionType fun
  where
    assumeTyParams m = foldr assumeAndAnnotateTyPat m ty_params

typeInferLetE :: ExpInfo -> PatM -> ExpM -> ExpM -> TCM Type
typeInferLetE inf pat expression body = do
  rhs_type <- typeInferExp expression

  -- Expression type must match pattern type
  checkType (text "Let binder doesn't match type of right-hand side") (getSourcePos inf)
    rhs_type (patMType pat)

  -- Assume the pattern while inferring the body; result is the body's type
  assumeAndAnnotatePat pat $ typeInferExp body

typeInferLetfunE :: ExpInfo -> DefGroup (FDef Mem) -> ExpM -> TCM Type
typeInferLetfunE inf defs body =
  typeCheckDefGroup defs $ typeInferExp body

typeInferCaseE :: ExpInfo -> ExpM -> [AltM] -> TCM Type
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

-- | Typecheck a pattern match.
--   Return the field types that should be matched and the expected
--   scrutinee type.
typeInferDeCon :: SourcePos 
               -> DeConInst
               -> TCM ([Type], Type)
typeInferDeCon pos decon@(VarDeCon op ty_args ex_types) = do
  env <- getTypeEnv
  data_con <- tcLookupDataCon op
  
  arg_kinds <- mapM typeCheckType ty_args
  let argument_types = zip ty_args arg_kinds
      existential_vars = [(v, k) | v ::: k <- ex_types]
  (_, inst_arg_types, con_scr_type) <-
    instantiatePatternType pos data_con argument_types existential_vars
  return (inst_arg_types, con_scr_type)

typeInferDeCon pos decon@(TupleDeCon types) = do
  kinds <- mapM typeCheckType types

  -- All fields must have value or boxed type 
  let valid_kind (VarT v) = v == valV || v == boxV
      valid_kind _ = False
  unless (all valid_kind kinds) $
    typeError "typeInferDeCon: Wrong kind in field of unboxed tuple"

  let tuple_type = typeApp (UTupleT $ map toBaseKind kinds) types
  return (types, tuple_type)

typeCheckAlternative :: SourcePos -> Type -> AltM -> TCM Type
typeCheckAlternative pos scr_type alt@(AltM (Alt con fields body)) = do
  -- Check constructor type
  (field_types, expected_scr_type) <- typeInferDeCon pos con
  
  -- Sanity check.  These types cannot be pattern-matched.
  let invalid_type =
        case expected_scr_type
        of FunT {} -> True
           AppT (VarT v) _ | v `isCoreBuiltin` The_OutPtr -> True
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
    assumeAndAnnotatePats fields $ do

      -- Infer the body
      ret_type <- typeInferExp body

      -- Make sure existential types don't escape 
      let ex_vars = [v | v ::: _ <- deConExTypes con]
      when (ret_type `typeMentionsAny` Set.fromList ex_vars) $
        typeError "Existential type variable escapes"

      return ret_type
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

-- | Verify that the given parameter matches the expected parameter
checkAltParam pos expected_type pattern = do 
  let given_type = patMType pattern
  checkType pos expected_type given_type
  return $ patMBinder pattern

typeInferCoerceE inf from_t to_t body = do
  from_kind <- typeInferType from_t
  to_kind <- typeInferType to_t
  body_type <- typeInferExp body
  
  -- Body type must match the coercion's input type
  checkType (text "Argument of coercion has wrong type")
    (getSourcePos inf) from_t body_type
  
  return to_t

typeInferArray inf ty es = do
  e_tys <- mapM typeInferExp es
  
  -- Expressions must have an initializer type
  let init_type = 
        varApp (coreBuiltin The_OutPtr) [ty] `FunT` VarT (coreBuiltin The_Store)
  let message = text "Expecting array element to have type " <+> pprType init_type

  forM_ e_tys $ \g_ty -> checkType message (getSourcePos inf) init_type g_ty

  return $ arrayInitializerType (length es) ty

checkConstant :: Constant Mem -> TCM ()
checkConstant (Constant inf ty e) = do
  typeCheckType ty
  g_type <- typeInferExp e
  checkType (text "Constant annotated with wrong type") (getSourcePos inf)
    ty g_type

typeCheckDefGroup :: DefGroup (FDef Mem) -> TCM b -> TCM b
typeCheckDefGroup defgroup do_body = do
  (_, body_type) <-
    assumeFDefGroup defgroup
    (mapM_ typeCheckDef $ defGroupMembers defgroup)
    do_body
  return body_type
  where
    -- To typecheck a definition, check the function it contains
    typeCheckDef def = typeInferFun $ definiens def

typeCheckGlobalDefGroup :: DefGroup (GDef Mem) -> TCM b -> TCM b
typeCheckGlobalDefGroup defgroup do_body = do
  (_, body_type) <-
    assumeGDefGroup defgroup
    (mapM_ typeCheckDef $ defGroupMembers defgroup)
    do_body
  return body_type
  where
    -- To typecheck a definition, check the function it contains
    typeCheckDef def =
      case definiens def
      of FunEnt f -> void $ typeInferFun f
         DataEnt d -> checkConstant d

typeCheckExport :: Export Mem -> TCM ()
typeCheckExport (Export pos spec f) = do
  typeInferFun f
  return ()

typeCheckModule (Module module_name imports defs exports) = do
  global_type_env <- readInitGlobalVarIO the_memTypes
  withTheNewVarIdentSupply $ \varIDs -> do
    let do_typecheck = typeCheckTopLevel imports defs exports
    runTypeEvalM do_typecheck varIDs global_type_env

typeCheckTopLevel imports defss exports =
  typeCheckGlobalDefGroup (Rec imports) $ typecheck_contents defss
  where
    typecheck_contents (defs:defss) =
      typeCheckGlobalDefGroup defs $ typecheck_contents defss

    typecheck_contents [] =
      mapM_ typeCheckExport exports

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
      of ConE _ con _ ->
           inferConAppType con
         AppE _ op ty_args args ->
           inferAppTypeQuickly op ty_args args
         LamE _ f ->
           return $ functionType f
         LetE _ pat e body ->
           assumeAndAnnotatePat pat $ infer_exp body
         LetfunE _ defs body ->
           assumeDefs defs $ infer_exp body
         CaseE _ _ (alt : _) ->
           infer_alt alt
         ExceptE _ rt ->
           return rt
         CoerceE {expRetType = rt} ->
           return rt
         ArrayE _ ty es ->
           return $ arrayInitializerType (length es) ty
         _ ->
           typeInferExp expression

    infer_alt (AltM (Alt con params body)) =
      assumeBinders (deConExTypes con) $ assumePatMs params $ infer_exp body

    debug = traceShow (text "inferExpType" <+> pprExp expression)

-- | Infer the type of an application, with minimal error checking
inferAppTypeQuickly op ty_args args = do
  op_type <- inferExpType op
  tenv <- getTypeEnv
  inst_op_type <- apply_types tenv op_type ty_args
  apply_arguments inst_op_type args
  where
    apply_types tenv op_type (arg:args) = do
      let kind = typeKind tenv arg
      m_app_type <- typeOfTypeApp op_type kind arg
      case m_app_type of
        Nothing -> err
        Just t  -> apply_types tenv t args
    
    apply_types _ t [] = return t
  
    -- Compute the result of applying a type to some arguments.
    -- For each argument, eliminate the function type constructor.
    apply_arguments t [] = return t
    apply_arguments t (_:args') = do
      whnf_t <- reduceToWhnf t 
      case whnf_t of
        FunT _ rng -> apply_arguments rng args'
        _ -> err
    
    err :: a
    err = internalError "inferExpType: Type error in application"

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
         of BareK -> varApp (coreBuiltin The_OutPtr) [app_type] `FunT`
                     VarT (coreBuiltin The_Store)
            _ -> app_type

inferConAppType (TupleCon ty_args) = do
  tenv <- getTypeEnv
  let kinds = map (toBaseKind . typeKind tenv) ty_args
  return $ typeApp (UTupleT kinds) ty_args

-- | Infer the type of an application, given the operator type and argument
--   types.  If the application is not well-typed, an exception is raised.
inferAppType :: EvalMonad m =>
                Type            -- ^ Operator type
             -> [Type]          -- ^ Type arguments
             -> [Type]          -- ^ Operand types
             -> m Type
inferAppType op_type ty_args arg_types =
  liftTypeEvalM $ do
    arg_kinds <- mapM typeInferType ty_args
    inst_type <- computeInstantiatedType noSourcePos op_type (zip arg_kinds ty_args)
    computeAppliedType Nothing noSourcePos inst_type arg_types
  where

    debug = traceShow (text "inferAppType" <+> types)
      where
        types = pprType op_type $$
                vcat (map ((text "@" <+>) . pprType) ty_args) $$
                vcat (map ((text ">" <+>) . pprType) arg_types)

-- | Get the parameter types and result type of a data constructor application.
conInstType :: EvalMonad m => ConInst -> m ([Type], Type)
conInstType c = typeInferCon c

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