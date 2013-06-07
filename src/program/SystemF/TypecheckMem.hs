
{-# LANGUAGE ScopedTypeVariables, TypeFamilies, EmptyDataDecls,
             FlexibleInstances, DeriveDataTypeable, TypeSynonymInstances #-}
module SystemF.TypecheckMem
       (functionType,
        typeCheckModule,

        -- * Type inference with type checking
        tcType,
        tcExp,
        
        -- * Type inference with type checking on expressions.
        --   Subterms have already been inferred.
        tcVar,
        tcLit,
        tcCon,
        tcApp,
        
        -- * Quick type inference.  These functions do minimal error
        --   checking, and should only be used on code that's known to
        --   be well-typed.
        inferExpType,
        inferAltType,
        inferAppType,
        conInstType,
        deConInstType)
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
import Common.MonadLogic
import Common.Supply
import Common.SourcePos

import GlobalVar
import Globals
import SystemF.PrintMemoryIR
import SystemF.Syntax
import SystemF.MemoryIR
import SystemF.Typecheck
import Type.Error
import Type.Eval
import Type.Environment
import Type.Type
import qualified Type.Rename as Rename
import qualified Type.Substitute as Substitute
import Type.Compare

type TC a = TCM UnboxedMode a

initType t = AppT outPtrT t `FunT` storeT

arrayInitializerType len element_type =
  let length_type = IntT $ fromIntegral len
      arr_type = arrT `typeApp` [length_type, element_type]
  in initType arr_type

assumeAndAnnotatePat :: PatM -> TC b -> TC b
assumeAndAnnotatePat (PatM (v ::: ty) _) k = do
  typeCheckType ty              -- Verify that type is well-formed
  assume v ty k

assumeAndAnnotatePats pats m = foldr assumeAndAnnotatePat m pats

assumeAndAnnotateTyPat :: TyPat -> TC b -> TC b
assumeAndAnnotateTyPat (TyPat (v ::: t)) k = do
  typeCheckType t               -- Verify that kind is well-formed
  assume v t k

assumeDefs defs m = foldr assumeFDef m (defGroupMembers defs)

-- | Typecheck a type and return its kind
tcType :: Type -> TC Kind
tcType = typeCheckType

-- | Typecheck an expression and return its type
tcExp :: ExpM -> TC Type
tcExp (ExpM expression) =
    case expression
    of VarE inf v -> tcVar pos v
       LitE inf l -> tcLit pos l
       ConE inf con sps ty_obj args ->
         typeInferConE (ExpM expression) pos con sps ty_obj args
       AppE {expInfo = inf, expOper = op, expTyArgs = ts, expArgs = args} ->
         typeInferAppE (ExpM expression) pos op ts args
       LamE {expInfo = inf, expFun = f} -> do
         typeInferFun f
       LetE {expInfo = inf, expBinder = pat, expValue = e, expBody = body} ->
         typeInferLetE inf pat e body
       LetfunE {expInfo = inf, expDefs = defs, expBody = body} ->
         typeInferLetfunE inf defs body
       CaseE inf scr sps alts ->
         typeInferCaseE inf scr sps alts
       ExceptE {expInfo = inf, expType = rt} -> do
         typeCheckType rt
         return rt
       CoerceE inf from_t to_t body ->
         typeInferCoerceE inf from_t to_t body
       ArrayE inf ty es ->
         typeInferArray inf ty es
  where
    pos = getSourcePos $ expInfo expression

-- To infer a variable's type, just look it up in the environment
tcVar :: SourcePos -> Var -> TC Type
tcVar pos var = do
  -- It's an internal error if a data constructor appears here
  m_dcon <- lookupDataCon var
  when (isJust m_dcon) $
    internalError $ "typeInferVarE: Data constructor used as variable: " ++ show var

  lookupVar var

-- Use the type that was attached to the literal value, but also verify that
-- it's a valid type
tcLit :: SourcePos -> Lit -> TC Type
tcLit pos l = do
  let literal_type = literalType l
  -- checkLiteralType l
  return literal_type

typeInferConE :: ExpM -> SourcePos -> ConInst -> [ExpM] -> Maybe ExpM
              -> [ExpM] -> TC Type
typeInferConE orig_exp pos con sps ty_obj args = do
  sp_types <- mapM tcExp sps
  ty_obj_type <- mapM tcExp ty_obj
  arg_types <- mapM tcExp args
  tcCon pos con sp_types ty_obj_type arg_types

tcCon :: SourcePos -> ConInst -> [Type] -> Maybe Type -> [Type] -> TC Type
tcCon pos con sp_tys ty_obj_ty arg_tys = do
  (expected_ty_obj_ty, expected_sps, field_tys, result_ty) <-
    typeInferCon pos con

  -- Check type object
  case (expected_ty_obj_ty, ty_obj_ty) of
    (Nothing, Nothing) -> return ()
    (Just et, Just gt) -> checkType (typeObjTypeMismatch pos) et gt
    (Just _, Nothing)  -> throwTypeError $ missingTypeObj pos
    (Nothing, Just _)  -> throwTypeError $ unwantedTypeObj pos

  -- Check size parameters
  let expected_num_sps = length expected_sps
      given_num_sps = length sp_tys
  when (expected_num_sps /= given_num_sps) $
    throwTypeError $ sizeParamLengthMismatch pos given_num_sps expected_num_sps
  sequence_ [checkType (sizeParamTypeMismatch pos index) et gt
            | (index, et, gt) <- zip3 [1..] expected_sps sp_tys]

  -- Check number of arguments
  let num_fields = length field_tys
      num_args = length arg_tys
  when (num_fields /= num_args) $
    throwTypeError $ conFieldLengthMismatch pos num_fields num_args

  -- Check argument types
  sequence_ [checkType (conFieldTypeMismatch pos index) field_ty arg_ty
            | (index, arg_ty, field_ty) <- zip3 [1..] arg_tys field_tys]

  return result_ty

-- | Infer the type of a constructor instance.
--   Return the type object type, size parameter types, field parameter types,
--   and return type.
typeInferCon :: EvalMonad m => SourcePos -> ConInst
             -> m (Maybe Type, [Type], [Type], Type)
typeInferCon pos con@(VarCon op ty_args ex_types) = do
  Just (type_con, data_con) <- lookupDataConWithType op
  (field_types, result_type) <-
    instantiateDataConTypeWithExistentials data_con (ty_args ++ ex_types)

  -- Get the type object
  ty_obj_type <-
    case dataTypeKind type_con
    of BoxK -> do t <- instantiateInfoType type_con ty_args
                  return $ Just t
       _ -> return Nothing

  -- Get types of size parameters from the type constructor's properties
  size_param_kinded_types <- instantiateSizeParams type_con ty_args 
  let size_param_types = map sizeParamType size_param_kinded_types

  -- Convert fields to initializers
  let field_kinds = dataConFieldKinds data_con
      con_field_types = zipWith make_initializer field_kinds field_types

  -- Convert result type to initializer
  let con_result_type = make_initializer (dataTypeKind type_con) result_type
  return (ty_obj_type, size_param_types, con_field_types, con_result_type)
  where
    make_initializer BareK ty = initType ty
    make_initializer _ ty = ty

typeInferCon pos con@(TupleCon types) = do
  kinds <- liftTypeEvalM $ mapM typeCheckType types

  -- All fields must have value or boxed type
  let check_kind i k@(VarT v)
        | v == valV || v == boxV = Nothing -- No error
        | otherwise = Just $ badUnboxedTupleField pos i k

  maybe (return ()) throwTypeError $ msum $ zipWith check_kind [1..] kinds

  let tuple_type = typeApp (UTupleT $ map toBaseKind kinds) types
  return (Nothing, [], types, tuple_type)

typeInferAppE orig_expr pos op ty_args args = do
  op_type <- tcExp op
  ty_arg_kinds <- mapM tcType ty_args
  arg_types <- mapM tcExp args

  -- Compute type of the type application
  tcApp pos op_type (zip ty_arg_kinds ty_args) arg_types

-- | Typecheck a type application and compute the result type
tcApp :: SourcePos -> Type -> [(Kind, Type)] -> [Type] -> TC Type
tcApp pos op_ty ty_args arg_tys = do
  inst_type <- computeInstantiatedType pos op_ty ty_args
  computeAppliedType Nothing pos inst_type arg_tys

-- | Compute the type of the result of applying an operator to some
--   type arguments.
computeInstantiatedType :: SourcePos -> Type -> [(Kind, Type)] -> TC Type
computeInstantiatedType inf op_type args_ = go 1 op_type args_
  where
    go index op_type ((arg_kind, arg) : args) = do
      result_type <- typeOfTypeApp inf index op_type arg_kind arg
      go (index+1) result_type args

    go _ op_type [] = return op_type

-- | Given a function type and a list of argument types, compute the result of
-- applying the function to the arguments.
computeAppliedType :: Maybe ExpM
                   -> SourcePos
                   -> Type
                   -> [Type]
                   -> TC Type
computeAppliedType orig_expr pos op_type_ arg_types =
  apply 1 op_type_ arg_types
  where
    apply index op_type (arg_t:arg_ts) = do
      op_type' <- typeOfApp pos index op_type arg_t
      apply (index + 1) op_type' arg_ts
    
    apply _ op_type [] = return op_type

typeInferFun :: FunM -> TC Type
typeInferFun fun@(FunM (Fun { funInfo = info
                            , funTyParams = ty_params
                            , funParams = params
                            , funReturn = return_type
                            , funBody = body})) = do

  -- Check types in the function
  assumeTyParams $ assumeAndAnnotatePats params $ do
    ti_body <- tcExp body

    -- Inferred type must match return type
    ret_kind <- tcType return_type
    checkType (returnTypeMismatch source_pos) return_type ti_body
    
  -- Create the function's type
  return $ functionType fun
  where
    source_pos = getSourcePos info
    assumeTyParams m = foldr assumeAndAnnotateTyPat m ty_params

typeInferLetE :: ExpInfo -> PatM -> ExpM -> ExpM -> TC Type
typeInferLetE inf pat expression body = do
  rhs_type <- tcExp expression

  -- Expression type must match pattern type
  let source_pos = getSourcePos inf
      pat_var = patMVar pat
  checkType (binderTypeMismatch source_pos pat_var) (patMType pat) rhs_type

  -- Assume the pattern while inferring the body; result is the body's type
  assumeAndAnnotatePat pat $ tcExp body

typeInferLetfunE :: ExpInfo -> DefGroup (FDef Mem) -> ExpM -> TC Type
typeInferLetfunE inf defs body =
  typeCheckDefGroup defs $ tcExp body

typeInferCaseE :: ExpInfo -> ExpM -> [ExpM] -> [AltM] -> TC Type
typeInferCaseE inf scr sps alts = do
  let pos = getSourcePos inf

  -- Get the scrutinee's type
  scr_type <- tcExp scr

  -- Check size parameter types
  expected_sps_types <-
    -- Look up the algebraic data type and instantiate its size parameter types
    condM (reduceToWhnf scr_type)
    [ -- Algebraic data type constructor
      do (VarT con, ty_args) <- fmap fromTypeApp it
         Just data_type <- lift $ lookupDataType con
         lift $ do size_param_types <- instantiateSizeParams data_type ty_args
                   return $ map sizeParamType size_param_types

      -- Unboxed tuple types do not take size parameters
    , do (UTupleT _, _) <- fmap fromTypeApp it
         return []

    , lift $ throwTypeError $
      MiscError pos (text "Scrutinee has type" <+> pprType scr_type <> comma $$
                     text "but only algebraic data types can be scrutinized")
    ]

  when (length expected_sps_types /= length sps) $
    throwTypeError $ sizeParamLengthMismatch pos (length expected_sps_types) (length sps)
  sps_types <- mapM tcExp sps
  forM_ (zip3 [1..] expected_sps_types sps_types) $ \(i, e, g) ->
    checkType (sizeParamTypeMismatch pos i) e g

  -- Match against each alternative
  when (null alts) $ throwTypeError (emptyCaseError pos)
  (first_alt_type : other_alt_types) <-
    mapM (typeCheckAlternative pos scr_type) alts

  -- All alternatives must have the same type
  forM_ (zip [2..] other_alt_types) $ \(i, t) ->
    checkType (inconsistentCaseAlternatives pos i) first_alt_type t
  
  -- The expression's type is the type of an alternative
  return first_alt_type

-- | Typecheck a pattern match.
--   Return the field types that should be matched and the expected
--   scrutinee type.
typeInferDeCon :: SourcePos 
               -> DeConInst
               -> TC ([Type], Type)
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
  let check_kind i k@(VarT v)
        | v == valV || v == boxV = Nothing -- No error
        | otherwise = Just $ badUnboxedTupleField pos i k

  maybe (return ()) throwTypeError $ msum $ zipWith check_kind [1..] kinds

  let tuple_type = typeApp (UTupleT $ map toBaseKind kinds) types
  return (types, tuple_type)

typeCheckAlternative :: SourcePos -> Type -> AltM -> TC Type
typeCheckAlternative pos scr_type alt@(AltM (Alt con m_ty_param fields body)) = do
  -- Check constructor type
  (field_types, expected_scr_type) <- typeInferDeCon pos con
  
  -- Sanity check.  These types cannot be pattern-matched.
  let invalid_type =
        case expected_scr_type
        of FunT {} -> True
           AppT (VarT v) _ | v == outPtrV -> True
           _ -> False
  when invalid_type $ internalError "typeCheckAlternative: Invalid pattern"

  -- Verify that applied type matches constructor type
  checkType (scrutineeTypeMismatch pos) expected_scr_type scr_type

  -- If the scrutinee is a boxed data type, check the type object parameter
  -- Otherwise, there should be no type object parameter
  case fromVarApp expected_scr_type of
    Just (tycon, args) -> do 
      Just data_type <- lookupDataType tycon
      case (dataTypeKind data_type, m_ty_param) of
        (BoxK, Just pat) -> do
          expected_type <- instantiateInfoType data_type (deConTyArgs con)
          checkType (typeObjTypeMismatch pos) expected_type (patMType pat)
        (BoxK, Nothing) ->
          throwTypeError $ missingTypeObj pos
        (_, Just _) ->
          throwTypeError $ unwantedTypeObj pos
        (_, Nothing) ->
          return ()
    Nothing ->
      case m_ty_param
      of Nothing -> return ()
         Just _ -> throwTypeError $ unwantedTypeObj pos
          
  -- Add existential variables to environment
  assumeBinders (deConExTypes con) $ do

    -- Verify that fields have the expected types
    check_number_of_fields field_types fields
    zipWithM_ check_arg field_types (zip [1..] fields)

    -- Add fields to enironment
    assumeAndAnnotatePats (maybeToList m_ty_param ++ fields) $ do

      -- Infer the body
      ret_type <- tcExp body

      -- Make sure existential types don't escape 
      let ex_vars = [v | v ::: _ <- deConExTypes con]
      when (ret_type `typeMentionsAny` Set.fromList ex_vars) $
        -- Choose one escaping variable to report with the error message
        let Just v = List.find (ret_type `typeMentions`) ex_vars
        in throwTypeError $ typeVariableEscapes pos v

      return ret_type
  where
    check_number_of_fields atypes fs
      | length atypes /= length fields =
        let expected = length atypes
            got = length fields
        in throwTypeError $ wrongPatternBinderCount pos expected got
      | otherwise = return ()

    check_arg expected_rtype (pat_index, pat) =
      let given_type = patMType pat
          pat_var = patMVar pat
      in checkType (binderTypeMismatch pos pat_var) expected_rtype given_type

-- | Verify that the given parameter matches the expected parameter
checkAltParam pos expected_type pattern = do 
  let given_type = patMType pattern
  checkType pos expected_type given_type
  return $ patMBinder pattern

typeInferCoerceE inf from_t to_t body = do
  from_kind <- tcType from_t
  to_kind <- tcType to_t
  body_type <- tcExp body
  
  -- Body type must match the coercion's input type
  checkType (coercionTypeMismatch (getSourcePos inf)) from_t body_type

  return to_t

typeInferArray inf ty es = do
  e_tys <- mapM tcExp es
  
  -- Expressions must have an initializer type
  let init_type = initType ty

  forM_ (zip [0..] e_tys) $ \(i, g_ty) ->
    checkType (arrayConTypeMismatch (getSourcePos inf) i) init_type g_ty

  return $ arrayInitializerType (length es) ty

checkConstant :: Constant Mem -> TC ()
checkConstant (Constant inf ty e) = do
  typeCheckType ty
  g_type <- tcExp e
  checkType (constantTypeMismatch (getSourcePos inf)) ty g_type

typeCheckDefGroup :: DefGroup (FDef Mem) -> TC b -> TC b
typeCheckDefGroup defgroup do_body = do
  (_, body_type) <-
    assumeFDefGroup defgroup
    (mapM_ typeCheckDef $ defGroupMembers defgroup)
    do_body
  return body_type
  where
    -- To typecheck a definition, check the function it contains
    typeCheckDef def = typeInferFun $ definiens def

typeCheckGlobalDefGroup :: DefGroup (GDef Mem) -> TC b -> TC b
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

typeCheckExport :: Export Mem -> TC ()
typeCheckExport (Export pos spec f) = do
  typeInferFun f
  return ()

typeCheckModule (Module module_name imports defs exports) = do
  global_type_env <- readInitGlobalVarIO the_memTypes
  withTheNewVarIdentSupply $ \varIDs -> do
    i_type_env <- thawTypeEnv global_type_env
    let do_typecheck = typeCheckTopLevel imports defs exports
    runTypeEvalM do_typecheck varIDs i_type_env

typeCheckTopLevel imports defss exports =
  typeCheckGlobalDefGroup (Rec imports) $ typecheck_contents defss
  where
    typecheck_contents (defs:defss) =
      typeCheckGlobalDefGroup defs $ typecheck_contents defss

    typecheck_contents [] =
      mapM_ typeCheckExport exports

-------------------------------------------------------------------------------
-- Quick type inference

-- | Infer the type of an expression.  The expression is assumed to be
--   well-typed; this function doesn't check for most errors.
inferExpType :: forall m. (EvalMonad m, EvalBoxingMode m ~ UnboxedMode) =>
                ExpM -> m Type
inferExpType expression =
  liftTypeEvalM $ infer_exp expression
  where
    -- Get the return type of an expression.  Skip parts that don't matter 
    -- to the return type.  Variable bindings are added to the environment,
    -- but their definitions are skipped.
    infer_exp expression =
      case fromExpM expression
      of ConE _ con _ _ _ ->
           inferConAppType con
         AppE _ op ty_args args ->
           inferAppTypeQuickly op ty_args args
         LamE _ f ->
           return $ functionType f
         LetE _ pat e body ->
           assumeAndAnnotatePat pat $ infer_exp body
         LetfunE _ defs body ->
           assumeDefs defs $ infer_exp body
         CaseE _ _ _ (alt : _) ->
           infer_alt alt
         ExceptE _ rt ->
           return rt
         CoerceE {expRetType = rt} ->
           return rt
         ArrayE _ ty es ->
           return $ arrayInitializerType (length es) ty
         _ ->
           tcExp expression

    infer_alt (AltM (Alt con ty_ob params body)) =
      assumeBinders (deConExTypes con) $ maybe id assumePatM ty_ob $
      assumePatMs params $ infer_exp body

    debug = traceShow (text "inferExpType" <+> pprExp expression)

-- | Infer the type of an application, with minimal error checking
inferAppTypeQuickly :: ExpM -> [Type] -> [ExpM] -> UnboxedTypeEvalM Type
inferAppTypeQuickly op ty_args args = do
  op_type <- inferExpType op
  inst_op_type <- apply_types op_type ty_args
  apply_arguments inst_op_type args
  where
    apply_types op_type (arg:args) = do
      kind <- typeKind arg
      t <- typeOfTypeApp noSourcePos 1 op_type kind arg
      apply_types t args
    
    apply_types t [] = return t
  
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
  Just (data_type, con_type) <- lookupDataConWithType op

  -- Apply the data type constructor to the type arguments 
  let app_type = varApp (dataConTyCon con_type) ty_args

  -- Create a writer function type, if it's a bare type
  return $!
    case dataTypeKind data_type
    of BareK -> initType app_type
       _ -> app_type

inferConAppType (TupleCon ty_args) = do
  kinds <- mapM typeBaseKind ty_args
  return $ typeApp (UTupleT kinds) ty_args

-- | Infer the type of a case alternative's result.  The code is assumed to be
--   well-typed; this function doesn't check for most errors.
inferAltType :: forall m. (EvalMonad m, EvalBoxingMode m ~ UnboxedMode) =>
                AltM -> m Type
inferAltType (AltM (Alt con ty_ob params body)) =
  assumeBinders (deConExTypes con) $
  maybe id assumePatM ty_ob $
  assumePatMs params $ inferExpType body
  
-- | Infer the type of an application, given the operator type and argument
--   types.  If the application is not well-typed, an exception is raised.
inferAppType :: (EvalMonad m, EvalBoxingMode m ~ UnboxedMode) =>
                Type            -- ^ Operator type
             -> [Type]          -- ^ Type arguments
             -> [Type]          -- ^ Operand types
             -> m Type
inferAppType op_type ty_args arg_types =
  liftTypeEvalM $ do
    arg_kinds <- mapM tcType ty_args
    inst_type <- computeInstantiatedType noSourcePos op_type (zip arg_kinds ty_args)
    computeAppliedType Nothing noSourcePos inst_type arg_types
  where

    debug = traceShow (text "inferAppType" <+> types)
      where
        types = pprType op_type $$
                vcat (map ((text "@" <+>) . pprType) ty_args) $$
                vcat (map ((text ">" <+>) . pprType) arg_types)

-- | Get the type object type, size parameter types, 
--   parameter types and result type of a data constructor application.
conInstType :: EvalMonad m => ConInst -> m (Maybe Type, [Type], [Type], Type)
conInstType c = typeInferCon noSourcePos c

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
       field_kinds <- mapM typeBaseKind field_types
       return $ typeApp (UTupleT field_kinds) field_types