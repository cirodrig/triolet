
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
        TypTM, ExpTM, AltTM, FunTM, PatTM,
        discardTypeAnnotationsExp,
        discardTypeAnnotationsFun,
        fromTypTM,
        fromPatTM,
        functionType,
        typeCheckModule,
        inferExpType,
        inferAppType,
        monoConType)
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
import Type.Rename
import Type.Compare

newtype instance Typ (Typed Mem) = TypTM (TypeAnn Type)
newtype instance Exp (Typed Mem) = ExpTM (TypeAnn (BaseExp TM))
newtype instance Alt (Typed Mem) = AltTM (TypeAnn (BaseAlt TM))
newtype instance Fun (Typed Mem) = FunTM (TypeAnn (BaseFun TM))

data instance Pat (Typed Mem) = TypedMemVarP Binder
                              | TypedMemWildP Type
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
fromPatTM (TypedMemVarP binder) = memVarP binder
fromPatTM (TypedMemWildP pt) = memWildP pt

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
      of DeCon con ty_args ex_types params body ->
           AltM $ DeCon { altConstructor = con
                        , altTyArgs = map (TypM . fromTypTM) ty_args
                        , altExTypes = map fromTyPatTM ex_types
                        , altParams = map fromPatTM params
                        , altBody = dtae body}
         DeTuple params body ->
           AltM $ DeTuple { altParams = map fromPatTM params
                          , altBody = dtae body}

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

assumePat :: PatM -> (PatTM -> TCM b) -> TCM b
assumePat (MemVarP (v ::: ty) _) k =
  assume v ty $ k (TypedMemVarP (v ::: ty))

assumePat (MemWildP ty) k = k (TypedMemWildP ty)

-- | Add pattern-bound variables from a let statement to the environment 
--   while processing the definition of the local value
assumeDefiningLetPattern :: PatM -> TCM a -> TCM a
assumeDefiningLetPattern (MemVarP {}) m = m -- Not visible during definition
assumeDefiningLetPattern (MemWildP {}) _ =
  internalError "assumeDefiningLetPattern: Unexpected wildcard"

-- | Add pattern-bound variables from a let statement to the environment 
--   while processing the use of the local value
assumeUsingLetPattern :: PatM -> TCM a -> TCM a
assumeUsingLetPattern pattern k =
  case pattern
  of MemVarP {}         -> assumePat pattern $ \_ -> k
     MemWildP {}        -> internalError "assumeUsingLetPattern: Unexpected wildcard"
     
assumeTyPat :: TyPat Mem -> (TyPat TM -> TCM b) -> TCM b
assumeTyPat (TyPatM (v ::: t)) k = do
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
       UTupleE {expInfo = inf, expArgs = args} ->
         typeInferUTupleE inf args
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

-- To infer a variable's type, just look it up in the environment
typeInferVarE :: ExpInfo -> Var -> TCM ExpTM
typeInferVarE inf var = do
  ty <- lookupVar var
  return $ ExpTM $ TypeAnn ty (VarE inf var)

-- Use the type that was attached to the literal value, but also verify that
-- it's a valid type
typeInferLitE :: ExpInfo -> Lit -> TCM ExpTM
typeInferLitE inf l = do
  let literal_type = literalType l
  checkLiteralType l
  return $ ExpTM $ TypeAnn literal_type (LitE inf l)

typeInferUTupleE inf args = do
  args' <- mapM typeInferExp args
  
  -- Determine tuple type
  tenv <- getTypeEnv
  let arg_types = map getExpType args'
      arg_kinds = map (toBaseKind . typeKind tenv) arg_types
      tuple_type = typeApp (UTupleT arg_kinds) arg_types
  return $ ExpTM $ TypeAnn tuple_type (UTupleE inf args')

typeInferAppE orig_expr inf op ty_args args = do
  let pos = getSourcePos inf
  ti_op <- typeInferExp op

  -- Apply to type arguments
  ti_ty_args <- mapM typeInferType ty_args
  inst_type <- computeInstantiatedType pos (getExpType ti_op) ti_ty_args

  -- Apply to other arguments
  ti_args <- mapM typeInferExp args
  result_type <-
    computeAppliedType pos inst_type (map getExpType ti_args)
  
  let new_exp = AppE inf ti_op ti_ty_args ti_args
  return $ ExpTM $ TypeAnn result_type new_exp

-- | Compute the type of the result of applying an operator to some
--   type arguments.
computeInstantiatedType :: SourcePos -> Type -> [TypTM] -> TCM Type
computeInstantiatedType inf op_type args = go op_type args
  where
    go op_type (TypTM (TypeAnn arg_kind arg) : args) = do
      app_type <- typeOfTypeApp op_type arg_kind arg
      case app_type of
        Just result_type -> go result_type args
        Nothing -> typeError "Error in type application"

    go op_type [] = return op_type
    
    go _ _ = typeError "Operator has wrong representation"

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

    apply _ _ = typeError "Operator has wrong representation"

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
    checkType noSourcePos (fromTypM return_type) (getExpType ti_body)
    
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
    assumeTyParams = withMany assumeTyPat ty_params
    assumeParams = withMany assumePat params

typeInferLetE :: ExpInfo -> PatM -> ExpM -> ExpM -> TCM ExpTM
typeInferLetE inf pat expression body = do
  ti_pat <- type_infer_pattern pat
  ti_exp <- assumeDefiningLetPattern pat $ typeInferExp expression

  -- Expression type must match pattern type
  checkType noSourcePos (getExpType ti_exp) (patType pat)

  -- Assume the pattern while inferring the body; result is the body's type
  ti_body <- assumeUsingLetPattern pat $ typeInferExp body
  let return_type = getExpType ti_body
      new_exp = LetE inf ti_pat ti_exp ti_body
  return $ ExpTM $ TypeAnn return_type new_exp
  where
    type_infer_pattern (MemVarP binder _) = return $ TypedMemVarP binder
    type_infer_pattern (MemWildP pt) =
      internalError "typeInferLetE: Unexpected wildcard"

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
  zipWithM (checkType pos) alt_subst_types (tail alt_subst_types)

  -- The expression's type is the type of an alternative
  let result_type = case head ti_alts of AltTM (TypeAnn rt _) -> rt
  return $! ExpTM $! TypeAnn result_type $ CaseE inf ti_scr ti_alts

typeCheckAlternative :: SourcePos -> Type -> AltM -> TCM AltTM
typeCheckAlternative pos scr_type (AltM (DeCon { altConstructor = con
                                               , altTyArgs = types
                                               , altExTypes = ex_fields
                                               , altParams = fields
                                               , altBody = body})) = do
  -- Process arguments
  arg_vals <- mapM typeInferType types

  -- Apply constructor to type arguments
  con_ty <- tcLookupDataCon con
  (_, inst_arg_types, con_scr_type) <-
    let argument_types =
          [(ty, kind) | TypTM (TypeAnn kind ty) <- arg_vals]
        existential_vars = [(v, k) | TyPatM (v ::: k) <- ex_fields]
    in instantiatePatternType pos con_ty argument_types existential_vars

  -- Verify that applied type matches constructor type
  checkType pos scr_type con_scr_type

  -- Add existential variables to environment
  withMany assumeTyPat ex_fields $ \ex_fields' -> do

    -- Verify that fields have the expected types
    check_number_of_fields inst_arg_types fields
    zipWithM_ check_arg inst_arg_types fields
  
    -- Add fields to enironment
    withMany assumePat fields $ \fields' -> do

      -- Infer the body
      ti_body <- typeInferExp body

      -- Make sure existential types don't escape 
      let ret_type = getExpType ti_body
      when (ret_type `typeMentionsAny` Set.fromList [v | TyPatTM v _ <- ex_fields']) $
        typeError "Existential type variable escapes"

      let new_alt = DeCon con arg_vals ex_fields' fields' ti_body
      return $ AltTM $ TypeAnn (getExpType ti_body) new_alt
  where
    check_number_of_fields atypes fs
      | length atypes /= length fields =
        internalError $ "typeCheckAlternative: Wrong number of fields in pattern (expected " ++
        show (length atypes) ++ ", got " ++ show (length fields) ++ ")"
      | otherwise = return ()

    check_arg expected_rtype pat =
      let given_type = patMType pat
      in checkType pos expected_rtype given_type

typeCheckAlternative pos scr_type (AltM (DeTuple { altParams = fields
                                                 , altBody = body})) = do
  -- Compute field kinds
  field_types <- mapM (typeInferType . TypM . patMType) fields
  let kinds = map getTypType field_types

  -- All fields must have value or boxed type 
  let valid_kind (VarT v) = v == valV || v == boxV
      valid_kind _ = False
  unless (all valid_kind kinds) $
    typeError "typeCheckAlternative: Wrong kind in field of unboxed tuple"

  -- Verify that the tuple type matches the scrutinee type
  let tuple_type =
        typeApp (UTupleT $ map toBaseKind kinds) (map patMType fields)
  checkType pos scr_type tuple_type

  -- Add fields to enironment
  withMany assumePat fields $ \fields' -> do
    -- Infer the body
    ti_body <- typeInferExp body

    let new_alt = DeTuple fields' ti_body
    return $ AltTM $ TypeAnn (getExpType ti_body) new_alt

bindParamTypes params m = foldr bind_param_type m params
  where
    bind_param_type (TypedMemVarP (param ::: param_ty)) m =
      assume param param_ty m

    bind_param_type (TypedMemWildP _) m = m

-- | Verify that the given parameter matches the expected parameter
checkAltParam pos expected_type pattern = do 
  let given_type = patMType pattern
  checkType pos expected_type given_type
  return $ case pattern
           of MemVarP binder _ -> TypedMemVarP binder
              MemWildP ptype -> TypedMemWildP ptype

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

typeCheckModule (Module module_name defs exports) = do
  global_type_env <- readInitGlobalVarIO the_memTypes
  withTheNewVarIdentSupply $ \varIDs -> do
    let do_typecheck = typeCheckDefGroups defs exports
    (defs', exports') <- runTypeEvalM do_typecheck varIDs global_type_env
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
inferExpType :: IdentSupply Var -> TypeEnv -> ExpM -> IO Type
inferExpType id_supply tenv expression =
  runTypeEvalM (infer_exp expression) id_supply tenv
  where
    -- Get the return type of an expression.  Skip parts that don't matter 
    -- to the return type.  Variable bindings are added to the environment,
    -- but their definitions are skipped.
    infer_exp expression =
      case fromExpM expression
      of LamE _ f -> return $ functionType f
         LetE _ pat e body ->
           assumeUsingLetPattern pat $ infer_exp body
         LetfunE _ defs body ->
           assumeDefs defs $ infer_exp body
         CaseE _ _ (alt : _) ->
           infer_alt alt
         ExceptE _ rt ->
           return rt
         _ ->
           fmap getExpType $ typeInferExp expression

    infer_alt (AltM alt) =
      withMany assumeTyPat (getAltExTypes alt) $ \_ ->
      withMany assumePat (altParams alt) $ \_ ->
      infer_exp $ altBody alt

-- | Infer the type of an application, given the operator type and argument
--   types.  If the application is not well-typed, an exception is raised.
inferAppType :: IdentSupply Var
             -> TypeEnv
             -> Type            -- ^ Operator type
             -> [TypM]          -- ^ Type arguments
             -> [Type]          -- ^ Operand types
             -> IO Type
inferAppType id_supply tenv op_type ty_args arg_types =
  runTypeEvalM infer_type id_supply tenv
  where
    infer_type = do
      ti_ty_args <- mapM typeInferType ty_args
      inst_type <- computeInstantiatedType noSourcePos op_type ti_ty_args
      computeAppliedType noSourcePos inst_type arg_types

-- | Get the type described by a 'MonoCon'.
monoConType :: EvalMonad m => MonoCon -> m Type
monoConType mono_con =
  liftTypeEvalM $
  case mono_con
  of MonoCon con ty_args ex_types -> do
       op_type <- tcLookupDataCon con
       let ex_args = [VarT a | a ::: _ <- ex_types]
       (_, ret_type) <-
         instantiateDataConTypeWithExistentials op_type (ty_args ++ ex_args)
       return ret_type
     MonoTuple field_types -> do
       tenv <- getTypeEnv
       let field_kinds = map (toBaseKind . typeKind tenv) field_types
       return $ typeApp (UTupleT field_kinds) field_types