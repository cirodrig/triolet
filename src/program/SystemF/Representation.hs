
{-# LANGUAGE FlexibleInstances #-}
module SystemF.Representation(inferRepresentations)
where

import Control.Monad
import Data.Maybe
import Data.Monoid
import Debug.Trace

import Text.PrettyPrint.HughesPJ

import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.MonadLogic
import Gluon.Common.SourcePos
import Gluon.Common.Supply
import Gluon.Core.Level
import Gluon.Core(internalSynInfo)
import SystemF.Syntax
import SystemF.Typecheck
import SystemF.Print
import Type.Compare
import Type.Eval
import Type.Environment
import Type.Rename
import Type.Type
import Type.Var
import Globals
import GlobalVar

data Rep

newtype instance Typ Rep = TypR {fromTypR :: Type}
data instance Pat Rep = PatR Var !ParamType
data instance TyPat Rep = TyPatR Var Type
newtype instance Ret Rep = RetR ReturnType

data instance Exp Rep =
    -- | Convert a readable reference to a value by loading the data.
    -- The ReturnRepr must be 'Val' or 'Box'.
    LoadExpr Repr Type ExpR

    -- | Convert a value to a writable reference by storing the data.
    -- The ReturnRepr must be 'Val' or 'Box'.
  | StoreExpr Repr Type ExpR
    
    -- | Reinterpret a readable pointer as a boxed object.
  | AsBoxExpr Type ExpR
    
    -- | Reinterpret a boxed object as a readable reference.
  | AsReadExpr Type ExpR

    -- | Copy a readable reference to a writable reference.
    --   If the type's natural representation is boxed, then this stores the
    --   reference into the destination.
    --   Otherwise, data is actually loaded from one place and stored to the
    --   other.
  | CopyExpr Type ExpR
    
    -- | Other expressions.
  | ExpR (BaseExp Rep)

newtype instance Fun Rep = FunR (BaseFun Rep)
newtype instance Alt Rep = AltR (BaseAlt Rep)

type TypR = Typ Rep
type PatR = Pat Rep
type TyPatR = TyPat Rep
type RetR = Ret Rep
type ExpR = Exp Rep
type FunR = Fun Rep
type AltR = Alt Rep

-- | Create the return representation corresponding to a 'Repr' for a value
--   that is read, rather than written.
asReadReturnRepr :: Repr -> ReturnRepr
asReadReturnRepr Value = ValRT
asReadReturnRepr Boxed = BoxRT
asReadReturnRepr Referenced = ReadRT

asWriteReturnRepr :: Repr -> ReturnRepr
asWriteReturnRepr Value = ValRT
asWriteReturnRepr Boxed = BoxRT
asWriteReturnRepr Referenced = WriteRT

paramReprToReturnRepr :: ParamRepr -> ReturnRepr
paramReprToReturnRepr (ValPT _) = ValRT
paramReprToReturnRepr BoxPT = BoxRT
paramReprToReturnRepr ReadPT = ReadRT
paramReprToReturnRepr WritePT = WriteRT

asReadParamRepr :: ParamRepr -> Repr -> ParamRepr
asReadParamRepr (ValPT mv)       Value = ValPT mv
asReadParamRepr (ValPT (Just _)) _     =
  internalError "asReadParamRepr: Inconsistent parameter representation"
asReadParamRepr _                Value = ValPT Nothing
asReadParamRepr _                Boxed = BoxPT
asReadParamRepr _                Referenced = ReadPT

asWriteParamRepr :: ParamRepr -> Repr -> ParamRepr
asWriteParamRepr (ValPT mv)       Value = ValPT mv
asWriteParamRepr (ValPT (Just _)) _     =
  internalError "asWriteParamRepr: Inconsistent parameter representation"
asWriteParamRepr _                Value = ValPT Nothing
asWriteParamRepr _                Boxed = BoxPT
asWriteParamRepr _                Referenced = WritePT

-- | Determine the default representation used for values of a data type.
--
--   Type variables, which stand for polymorphic types, have 'Referenced'
--   representation.
typeRepr :: TypeEnv -> Type -> Repr
typeRepr env t =
  case getLevel t
  of TypeLevel ->
       case fromTypeApp t
       of (FunT {}, _) -> Boxed
          (VarT var, args) ->
            case lookupDataType var env
            of Just op_type -> dataTypeRepresentation op_type
               Nothing -> case lookupType var env
                          of Just _ -> Referenced
                             _ -> not_found
     KindLevel -> Value
  where
    not_found = internalError "typeRepr: No information for variable"

-- | Given a data type from System F, insert the correct representation
--   information for its use in Core
fixUpTypeRepresentations :: TypeEnv -> Type -> Type
fixUpTypeRepresentations env ty = go ty
  where
    go ty =
      case ty
      of VarT v -> ty
         AppT t1 t2 -> AppT (go t1) (go t2)
         FunT (arg ::: dom) (ret ::: rng) ->
           let dom' = go dom
               dom_repr = typeRepr env dom'
               arg' = asReadParamRepr arg dom_repr
               env' = case arg
                      of ValPT (Just v) -> insertType v (ValRT ::: dom') env
                         _ -> env
               rng' = fixUpTypeRepresentations env' rng
               ret' = asWriteReturnRepr $ typeRepr env rng'
           in FunT (arg' ::: dom') (ret' ::: rng')

getFunType :: FunTSF -> InferRepr Type
getFunType f = infFixUpType $ getTypeAnn f

-- | Wrapper code placed around an expression 
data WrapperCode =
  NoWrapper | Wrapper (ExpR -> ExpR)

applyWrapper :: WrapperCode -> ExpR -> ExpR
applyWrapper NoWrapper = id
applyWrapper (Wrapper f) = f

isNoWrapper NoWrapper = True
isNoWrapper _ = False

-- | As a monoid, @w1 `mappend` w2@ is the result of performing w2 first,
--   followed by w1.
instance Monoid WrapperCode where
  mempty = NoWrapper
  NoWrapper `mappend` w = w
  w `mappend` NoWrapper = w
  Wrapper f `mappend` Wrapper g = Wrapper (f . g)

data Coercion =
    -- | Don't coerce
    NoCoercion
    
    -- | Apply a wrapper to the producer value
  | WrapperCoercion (ExpR -> ExpR)
    
    -- | Bind the producer value to a temporary variable, and supply
    --   something else to the consumer
  | BinderCoercion (ExpR -> (ExpR, ExpR -> ExpR))

-- | As a monoid, @c1 `mappend` c2@ applies c2, followed by c1.
instance Monoid Coercion where
  mempty = NoCoercion
  c1 `mappend` c2 = 
    case (c1, c2)
    of (NoCoercion, c) -> c
       (c, NoCoercion) -> c
       (WrapperCoercion f1, WrapperCoercion f2) ->
         WrapperCoercion (f1 . f2)
       (WrapperCoercion f1, BinderCoercion f2) ->
         BinderCoercion $ \p -> case f2 p
                                of (p', wrapper) -> (f1 p', wrapper)
       (BinderCoercion f1, WrapperCoercion f2) ->
         BinderCoercion (f1 . f2)
       (BinderCoercion f1, BinderCoercion f2) ->
         BinderCoercion $ \p -> case f2 p
                                of (p', wrapper) ->
                                     case f1 p'
                                     of (p'', wrapper') ->
                                          (p'', wrapper . wrapper')

-- | Given a coercion and its parameter value, make a wrapper around the
--   consumer value
applyCoercion :: Coercion -> ExpR -> (ExpR -> ExpR) -> ExpR
applyCoercion co p c = 
  case co
  of NoCoercion        -> c p
     WrapperCoercion f -> c (f p)
     BinderCoercion f  -> case f p of (p', wrapper) -> wrapper (c p')

applyCoercions :: [(Coercion, ExpR)] -> ([ExpR] -> ExpR) -> ExpR
applyCoercions ((co, param):co_params) consumer =
  applyCoercion co param $ \param' ->
  applyCoercions co_params $ \params' -> consumer (param' : params')

applyCoercions [] consumer = consumer []

coercionToWrapper :: Coercion -> ExpR -> (ExpR, WrapperCode)
coercionToWrapper co p =
  case co
  of NoCoercion        -> (p, NoWrapper)
     WrapperCoercion f -> (f p, NoWrapper)
     BinderCoercion f  -> case f p of (p', wrapper) -> (p', Wrapper wrapper)

idCoercion = NoCoercion

isIdCoercion NoCoercion = True
isIdCoercion _ = False

-- | Coerce @Val -> Read@.
--   Store the value to a temporary variable, then read it.
valToReadCoercion ty tmpvar = BinderCoercion $ \producer ->
  let rhs_exp = StoreExpr Value ty producer
      use_exp = ExpR $ VarE defaultExpInfo tmpvar
      wrapper body =
        ExpR $ LetE { expInfo = defaultExpInfo
                    , expBinder = PatR tmpvar (WritePT ::: ty)
                    , expValue = rhs_exp
                    , expBody = body}
  in (use_exp, wrapper)

valToWriteCoercion ty = WrapperCoercion (\e -> StoreExpr Value ty e)

boxToReadCoercion ty = WrapperCoercion (\e -> AsReadExpr ty e)

boxToWriteCoercion ty = WrapperCoercion (\e -> StoreExpr Boxed ty e)

-- | Coerce @Read -> Val@
loadValCoercion ty = WrapperCoercion (\e -> LoadExpr Value ty e)

-- | Coerce @Read -> Box@
asBoxCoercion ty = WrapperCoercion (\e -> AsBoxExpr ty e)

-- | Coerce @Read -> Write@
copyCoercion ty = WrapperCoercion (\e -> CopyExpr ty e)

-- | Coerce @Write -> Val@
writeToValCoercion ty tmpvar = BinderCoercion $ \producer ->
  let use_exp = LoadExpr Value ty $ ExpR $ VarE defaultExpInfo tmpvar
      wrapper body =
        ExpR $ LetE { expInfo = defaultExpInfo
                    , expBinder = PatR tmpvar (WritePT ::: ty)
                    , expValue = producer
                    , expBody = body}
  in (use_exp, wrapper)

-- | Coerce @Write -> Box@
writeToBoxCoercion ty tmpvar = BinderCoercion $ \producer ->
  let use_exp = AsBoxExpr ty $
                ExpR $ VarE defaultExpInfo tmpvar
      wrapper body =
        ExpR $ LetE { expInfo = defaultExpInfo
                    , expBinder = PatR tmpvar (WritePT ::: ty)
                    , expValue = producer
                    , expBody = body}
  in (use_exp, wrapper)

-- | Coerce @Write -> Read@
writeToReadCoercion ty tmpvar = BinderCoercion $ \producer ->
  let use_exp = ExpR $ VarE defaultExpInfo tmpvar
      wrapper body =
        ExpR $ LetE { expInfo = defaultExpInfo
                      , expBinder = PatR tmpvar (WritePT ::: ty)
                      , expValue = producer
                      , expBody = body}
  in (use_exp, wrapper)

-------------------------------------------------------------------------------

data InferReprEnv =
  InferReprEnv
  { irTypeEnv :: TypeEnv
  , irVarSupply :: !(IdentSupply Var)
  }

newtype InferRepr a = InferRepr (InferReprEnv -> IO a)

runInferRepr :: InferReprEnv -> InferRepr a -> IO a
runInferRepr env (InferRepr f) = f env

instance Monad InferRepr where
  return x = InferRepr $ \_ -> return x
  m >>= k = InferRepr $ \env -> do x <- case m of InferRepr f -> f env
                                   case k x of InferRepr f -> f env

instance Supplies InferRepr (Ident Var) where
  fresh = InferRepr $ \env -> supplyValue (irVarSupply env)

withTypeEnv :: (TypeEnv -> a) -> InferRepr a
withTypeEnv f = InferRepr (\env -> return (f $ irTypeEnv env))

assume :: Var -> ReturnType -> InferRepr a -> InferRepr a
assume v t (InferRepr f) = InferRepr $ \env ->
  let env' = env {irTypeEnv = insertType v t $ irTypeEnv env}
  in f env'

infLookupType v = withTypeEnv (lookupType v)
infLookupDataCon v = withTypeEnv (lookupDataCon v)
infFixUpType t = withTypeEnv $ \env -> fixUpTypeRepresentations  env t
infTypeRepr t = withTypeEnv $ \env -> typeRepr env t

infApplyType pos op arg arg_val = InferRepr $ \env ->
  typeOfApp (irVarSupply env) pos (irTypeEnv env) op arg arg_val

infCompareTypes pos e_type g_type = InferRepr $ \env ->
  compareTypes (irVarSupply env) pos (irTypeEnv env) e_type g_type

-------------------------------------------------------------------------------
-- Coercions

-- | Coerce a returned value to the specified representation
coerceReturn :: Type -> ReturnRepr -> ReturnRepr -> InferRepr Coercion
coerceReturn ty e_repr g_repr =
  case e_repr
  of ValRT ->
       case g_repr
       of ValRT -> return idCoercion
          BoxRT -> can't
          ReadRT -> return $ loadValCoercion ty
          WriteRT -> do
            tmpvar <- newAnonymousVar ObjectLevel
            return $ writeToValCoercion ty tmpvar
     BoxRT ->
       case g_repr
       of ValRT -> can't
          BoxRT -> return idCoercion
          ReadRT -> return $ asBoxCoercion ty
          WriteRT -> do
            tmpvar <- newAnonymousVar ObjectLevel
            return $ writeToBoxCoercion ty tmpvar
     ReadRT ->
       case g_repr
       of ValRT -> do
            tmpvar <- newAnonymousVar ObjectLevel
            return $ valToReadCoercion ty tmpvar
          BoxRT -> return $ boxToReadCoercion ty
          ReadRT -> return idCoercion
          WriteRT -> do
            tmpvar <- newAnonymousVar ObjectLevel
            return $ writeToReadCoercion ty tmpvar
     WriteRT ->
       case g_repr
       of ValRT -> return $ valToWriteCoercion ty
          BoxRT -> return $ boxToWriteCoercion ty
          ReadRT -> return $ copyCoercion ty
          WriteRT -> return idCoercion
  where
    can't = internalError "coerceReturn"

-- | Coerce a parameter from given to expected parameter type.
--   This returns a coercion that should be applied to the given parameter
--   variable.
coerceParameter :: Type -> ParamRepr -> ParamRepr -> InferRepr Coercion
coerceParameter ty e_repr g_repr =
  case (e_repr, g_repr)
  of (ValPT e_param, ValPT g_param)
       | parameter_variable_mismatch e_param g_param ->
         internalError "coerceParameter"
     _ -> coerceReturn ty (to_return_repr e_repr) (to_return_repr g_repr)
  where
    to_return_repr (ValPT _) = ValRT
    to_return_repr BoxPT = BoxRT
    to_return_repr ReadPT = ReadRT
    to_return_repr WritePT = WriteRT

    parameter_variable_mismatch (Just v1) (Just v2) = v1 /= v2
    parameter_variable_mismatch _ _ = False

coerceReturnType :: ReturnType -> ReturnType -> InferRepr Coercion
coerceReturnType (e_repr ::: e_type) (g_repr ::: g_type) = do
  co_type <- coerceType e_type g_type
  
  -- Do types match?
  if isIdCoercion co_type
    then coerceReturn e_type e_repr g_repr
    else do
      -- Coerce the given value to the type's natural representation.
      -- The natural representation is the same for given and expected types.
      natural_repr <- infTypeRepr g_type
      let n_repr = asWriteReturnRepr natural_repr
      co1 <- coerceReturn g_type n_repr g_repr
      
      -- Coerce the coerced value to the expected representation
      co3 <- coerceReturn e_type e_repr n_repr
      return (co3 `mappend` co_type `mappend` co1)

coerceParameterType :: ParamType -> ParamType -> InferRepr Coercion
coerceParameterType (e_repr ::: e_type) (g_repr ::: g_type) = do
  co_type <- coerceType e_type g_type
  
  -- Do types match?
  if isIdCoercion co_type
    then coerceParameter e_type e_repr g_repr
    else do
      -- Coerce the given value to the type's natural representation.
      -- The natural representation is the same for given and expected types.
      natural_repr <- infTypeRepr g_type
      co1 <- coerceParameter g_type (asWriteParamRepr g_repr natural_repr) g_repr
      
      -- Coerce the coerced value to the expected representation
      co3 <- coerceParameter e_type e_repr (asReadParamRepr e_repr natural_repr)
      return (co3 `mappend` co_type `mappend` co1)

coerceType :: Type -> Type -> InferRepr Coercion
coerceType e_type g_type = do
  utypes <- unifyBoundVariables e_type g_type
  case utypes of
    (VarT e_var, VarT g_var)
      | e_var == g_var -> return mempty
      | otherwise -> internalError "coerceType"
    (FunT {}, FunT {}) -> coerce_function_type [] e_type g_type
    (e_type', g_type') -> do
      ok <- infCompareTypes noSourcePos e_type' g_type'
      if ok then return mempty else internalError "coerceType: Type mismatch"
  where
    coerce_function_type
      r_param_coercions
      (FunT e_param e_result)
      (FunT g_param g_result) = do
        -- Coerce the parameter.  Note that we coerce from expected to given.
        co <- coerceParameterType g_param e_param
        let r_param_coercions' = (e_param, co) : r_param_coercions
        
        -- Continue coercing parameters?
        case (e_result, g_result) of
          (BoxRT ::: e_type@(FunT {}), BoxRT ::: g_type@(FunT {})) ->
            coerce_function_type r_param_coercions' e_type g_type
          (_, _) ->
            coerce_return_type (reverse r_param_coercions') e_result g_result

    coerce_return_type param_coercions e_rt g_rt = do
      ret_coercion <- coerceReturnType e_rt g_rt
      
      -- If nothing was coerced, then don't construct a coercion
      if isIdCoercion ret_coercion &&
         and [isIdCoercion co | (_, co) <- param_coercions]
        then return mempty
        else createFunctionCoercion param_coercions e_rt g_rt ret_coercion

createFunctionCoercion :: [(ParamType, Coercion)]
                       -> ReturnType
                       -> ReturnType
                       -> Coercion
                       -> InferRepr Coercion
createFunctionCoercion param_coercions e_rt g_rt ret_coercion = do
  params <- mapM create_coercion_parameter param_coercions
  return $ WrapperCoercion $ \real_fun -> coerced_fun real_fun params
  where
    coerced_fun real_fun params = ExpR $ LamE defaultExpInfo coercion_fun
      where
        ty_params = takeWhile (\(v, _, _) -> getLevel v == TypeLevel) params
        val_params = dropWhile (\(v, _, _) -> getLevel v == TypeLevel) params

        coercion_fun =
          let param_exprs = [(co, ExpR $ VarE defaultExpInfo v)
                            | (v, _, co) <- val_params]
              typaram_types = [TypR (VarT v) | (v, _, _) <- ty_params]
              body = applyCoercions param_exprs $ \param_exprs' ->
                let call_expr =
                      mkCall defaultExpInfo real_fun typaram_types param_exprs'
                in applyCoercion ret_coercion call_expr id
          in FunR $ Fun { funInfo = defaultExpInfo
                        , funTyParams = [TyPatR v t
                                        | (v, _ ::: t, _) <- ty_params]
                        , funParams = [PatR v t | (v, t, _) <- val_params]
                        , funBody = body}
      
    create_coercion_parameter :: (ParamType, Coercion)
                              -> InferRepr (Var, ParamType, Coercion)
    create_coercion_parameter (e_param, co) =
      case e_param
      of ValPT (Just pvar) ::: _ -> return (pvar, e_param, co)
         _ ::: e_type -> do v <- newAnonymousVar (pred $ getLevel e_type)
                            return (v, e_param, co)

mkCall :: ExpInfo -> ExpR -> [TypR] -> [ExpR] -> ExpR
mkCall inf op ty_args args = ExpR $ AppE inf op ty_args args

-------------------------------------------------------------------------------
-- Representation infernece

-- | Coerce a returned value to the specified representation
coerceInferredExp :: ReturnRepr
                  -> (WrapperCode, ExpR, ReturnType)
                  -> InferRepr (WrapperCode, ExpR, ReturnType)
coerceInferredExp e_repr given@(wr, expression, g_repr ::: g_rt) = do
  co <- coerceReturn g_rt e_repr g_repr
  let (expression', co_wr) = coercionToWrapper co expression
  return (wr `mappend` co_wr, expression', e_repr ::: g_rt)

withTyPat :: Substitution
          -> TyPat (Typed SF)
          -> (Substitution -> TyPat Rep -> InferRepr a)
          -> InferRepr a
withTyPat subst (TyPatTSF v typed_t) f =
  let t = fromTypTSF typed_t
      pat' = TyPatR v t
      subst' = insertSubstitution v t subst
  in do repr <- infTypeRepr t
        assume v (asReadReturnRepr repr ::: t) $ f subst' pat'

withTyPats :: Substitution
           -> [TyPat (Typed SF)]
           -> (Substitution -> [TyPat Rep] -> InferRepr a)
           -> InferRepr a
withTyPats subst (p:ps) f =
  withTyPat subst p $ \subst' p' ->
  withTyPats subst' ps $ \subst'' ps' -> f subst'' (p':ps')

withTyPats subst [] f = f subst []

withPat :: PatTSF -> (Pat Rep -> InferRepr a) -> InferRepr a
withPat (TypedVarP v (TypTSF (TypeAnn _ ty))) f = do
  repr <- infTypeRepr ty
  let p_repr = case repr
               of Value -> ValPT Nothing
                  Boxed -> BoxPT
                  Referenced -> ReadPT
      r_repr = asReadReturnRepr repr
  assume v (r_repr ::: ty) $ f (PatR v (p_repr ::: ty))

withPats = withMany withPat

withDefs :: [Def (Typed SF)] -> ([Def Rep] -> InferRepr a) -> InferRepr a
withDefs defs f = assume_defs $ mapM inferDef defs >>= f
  where
    assume_defs m = foldr assume_def m defs
    assume_def (Def v f) m = do
      ty <- getFunType f
      assume v (BoxRT ::: ty) m

-- | Infer the representation of an expression.
--   Coerce the return representation to its natural representation.
inferReturnExp :: Bool          -- ^ If true, coerce to a write return.
                                -- Otherwise coerce to a read return.
               -> Maybe Type    -- ^ Expected type
               -> ExpTSF        -- ^ Expression
               -> InferRepr (WrapperCode, ExpR, ReturnType)
inferReturnExp to_write mtype expression = do
  (wr, exp', inf_repr ::: inf_type) <- inferReprExp expression
  let expected_type = fromMaybe inf_type mtype
  rrepr <- infTypeRepr expected_type
  let return_repr = if to_write
                    then asWriteReturnRepr rrepr
                    else asReadReturnRepr rrepr

  -- Coerce it
  co <-
    coerceReturnType (return_repr ::: expected_type) (inf_repr ::: inf_type)
  let (exp'', co_wr) = coercionToWrapper co exp'
  return (wr `mappend` co_wr, exp'', return_repr ::: expected_type)

inferReadReturnExp  = inferReturnExp False
inferWriteReturnExp = inferReturnExp True

-- | Infer the representation of an expression.  Return coercions that
--   should be applied to the /user/ of the expression, the expression itself,
--   and the expression's return type.
inferReprExp :: ExpTSF -> InferRepr (WrapperCode, ExpR, ReturnType)
inferReprExp texpression@(ExpTSF (TypeAnn ty expression)) = do
  case expression of
    VarE inf v -> inferVarE inf v
    LitE inf l -> inferLitE inf l
    AppE inf op ty_args args -> inferCall inf op ty_args args
    LamE inf f -> inferFunE inf f
    LetE inf b rhs body -> inferLetE inf b rhs body
    LetrecE inf defs body -> inferLetrecE inf defs body
    CaseE inf scr alts -> inferCaseE inf scr alts

inferVarE inf v = do
  mreturn_type <- infLookupType v
  let return_type =
        case mreturn_type
        of Just t -> t
           Nothing -> internalError "inferVarE: No type for variable"
                      
  let exp = ExpR (VarE inf v)
  return (mempty, exp, return_type) 

inferLitE inf l = do
  return_repr <- infTypeRepr $ literalType l
  let exp = ExpR (LitE inf l)
  return (mempty, exp, asReadReturnRepr return_repr ::: literalType l)

inferCall inf op t_args v_args = do
  (op_wr, op', op_type) <- coerceInferredExp BoxRT =<< inferReprExp op
  (expr, return_type) <- inferApplication inf op' op_type t_args v_args
  return (op_wr, expr, return_type)

inferApplication inf op op_type t_args v_args = do 
  -- Apply operator to argument types
  inst_op_type <- instantiate op_type t_args
  
  -- Apply to arguments
  (wrappers, new_v_args, ret_ty) <- apply inst_op_type v_args
  
  -- Create call expression
  let new_t_args = [TypR t | TypTSF (TypeAnn _ t) <- t_args]
      new_call = mkCall inf op new_t_args new_v_args
  return (applyWrapper wrappers new_call, ret_ty)
  where
    pos = getSourcePos inf

    instantiate ty (t:ts) = do
      ty' <- inferTypeApp pos ty t
      instantiate ty' ts
    instantiate ty [] = return ty
    
    apply op_ty (arg:args) = do
      (wr, arg', op_ty') <- inferApp pos op_ty arg
      (wrs, args', ret_ty) <- apply op_ty' args
      return (wr `mappend` wrs, arg':args', ret_ty)

    apply op_ty [] = return (mempty, [], op_ty)

-- | Compute the result type produced by a type application.
--
-- The parameter's type is assumed to be correct, since it went through
-- type inference.
inferTypeApp :: SourcePos
             -> ReturnType
             -> TypTSF
             -> InferRepr ReturnType
inferTypeApp pos (BoxRT ::: FunT (ValPT mparam ::: _) (ret ::: rng))
                 (TypTSF (TypeAnn _ arg)) =
  case mparam
  of Nothing -> return (ret ::: rng)
     Just param_var ->
       let subst = singletonSubstitution param_var arg
       in return (ret ::: substitute subst rng)

inferTypeApp _ _ _ = internalError "Error in type application during representation inference"

-- | Compute the result of a type application, given the type of the operator
--   and the argument expression.
--   Returns the coerced argument and the type returned by the application.
inferApp :: SourcePos
         -> ReturnType
         -> ExpTSF
         -> InferRepr (WrapperCode, ExpR, ReturnType)
inferApp pos (BoxRT ::: FunT (param_repr ::: dom) result) arg_exp = do
  -- Infer parameter
  let expected_repr = paramReprToReturnRepr param_repr
  (wr, arg_exp', arg_rtype) <-
    coerceInferredExp expected_repr =<< inferReprExp arg_exp
  
  -- Return the range.  Cannot handle dependent parameters.
  case param_repr of
    ValPT (Just _) -> internalError "inferApp: Unexpected dependent parameter"
    _ -> return ()

  return (wr, arg_exp', result)

inferApp _ _ _ = internalError "inferApp: Unexpected operator type"

inferFunE inf f = do
  f' <- inferFun f
  fun_type <- getFunType f
  let new_expr = ExpR $ LamE inf f'
  return (mempty, new_expr, BoxRT ::: fun_type)

inferFun (FunTSF (TypeAnn _ f)) =
  withTyPats emptySubstitution (funTyParams f) $ \ty_subst ty_pats ->
  withPats (funParams f) $ \pats -> do
    let expected_return_type = case funReturn f of RetTSF t -> t
    (body_wrapper, body, body_type) <-
      inferWriteReturnExp (Just expected_return_type) (funBody f)
    
    let co_body = applyWrapper body_wrapper body
    return $ FunR $ Fun { funInfo = funInfo f
                        , funTyParams = ty_pats
                        , funParams = pats
                        , funReturn = RetR body_type
                        , funBody = co_body}

inferLetE inf binder rhs body = do
  (rhs_wr, rhs', rhs_ty) <- inferReprExp rhs
  withPat binder $ \pat' -> do
    (body_wr, body', body_ty) <- inferReprExp body
    let new_expr = ExpR $ LetE inf pat' rhs' body'
    return (body_wr, applyWrapper rhs_wr new_expr, body_ty)

inferLetrecE inf defs body = do
  withDefs defs $ \defs' -> do
    (wr, body', ret_type) <- inferReprExp body
    let new_expr = ExpR $ LetrecE inf defs' body' 
    return (wr, new_expr, ret_type)

inferCaseE inf scr alts = do
  -- Process the scrutinee
  (scr_wrapper, scr') <- inferScrutinee scr
      
  -- Process the alternatives
  let sf_ret_type = getTypeAnn $ head alts
  ret_type <- infFixUpType sf_ret_type
  ret_repr <- liftM asWriteReturnRepr $ infTypeRepr ret_type
  alts' <- mapM (inferAlt (getSourcePos inf) ret_repr) alts
  
  let new_expr = ExpR $ CaseE inf scr' alts'
  return (mempty,
          applyWrapper scr_wrapper new_expr,
          ret_repr ::: ret_type)

inferScrutinee scr = do
  (scr_wrapper, scr', scr_repr ::: scr_ty) <- inferReprExp scr
  expected_scr_ty <- infTypeRepr scr_ty

  -- Coerce to read return type
  coercion <- coerceReturn scr_ty (asReadReturnRepr expected_scr_ty) scr_repr
  let (co_scr, co_wr) = coercionToWrapper coercion scr'
  return (scr_wrapper `mappend` co_wr, co_scr)

inferAlt pos repr (AltTSF (TypeAnn _ (Alt con ty_args params body))) = do  
  -- Instantiate the constructor's actual type with the given type arguments
  (dc_params, dc_args, _) <- lookup_con_type
  let subst = instantiate dc_params
              [t | TypTSF (TypeAnn _ t) <- ty_args]
      inst_dc_args = map (substituteBinding subst) dc_args
  
  -- Construct Alt parameters with correct representation information
  let rep_ty_args = [TypR t | TypTSF (TypeAnn _ t) <- ty_args]
      rep_params = zipWith mk_ty_pat params inst_dc_args
        where
          mk_ty_pat (TypedVarP v _) (return_repr ::: repr_type) =
            let param_repr =
                  case return_repr
                  of ValRT -> ValPT Nothing
                     BoxRT -> BoxPT
                     ReadRT -> ReadPT
                     WriteRT -> internalError "inferAlt"
            in PatR v (param_repr ::: repr_type)

  -- Infer the body
  (body_wrapper, body', body_type) <-
    assume_fields rep_params $ inferReturnExp True Nothing body
  let body'' = applyWrapper body_wrapper body'
  
  -- Construct the new Alt
  let new_alt = AltR $ Alt { altConstructor = con
                           , altTyArgs = rep_ty_args
                           , altParams = rep_params
                           , altBody = body''}
  return new_alt
  where
    -- Look up the actual representation of this alternative.
    -- This will replace the representation that was used in System F.
    lookup_con_type = do
      mdcon <- infLookupDataCon con
      case mdcon of
        Just dcon -> return
                     (dataConPatternParams dcon,
                      dataConPatternArgs dcon,
                      dataConPatternRange dcon)
        Nothing ->
          internalError "inferAlt: Constructor is not a data constructor"
  
    instantiate params args = inst emptySubstitution params args  
      where
        inst s ((ValPT (Just v) ::: _) : params) (arg : args) =
          let s' = insertSubstitution v arg s
          in inst s' params args
      
        inst s (_ : params) (_ : args) = inst s params args
        
        inst s [] [] = s
    
    assume_fields params m = foldr assume_field m params
      where
        assume_field (PatR v (repr ::: ty)) m =
          assume v (paramReprToReturnRepr repr ::: ty) m

inferDef (Def v f) = do
  f' <- inferFun f
  return $ Def v f'

inferExport (Export pos spec f) = do
  f' <- inferFun f
  return $ Export pos spec f'

inferTopLevel (defs:defss) exports =
  withDefs defs $ \defs' -> do
    (defss', exports') <- inferTopLevel defss exports
    return (defs' : defss', exports')

inferTopLevel [] exports = do
  exports' <- mapM inferExport exports
  return ([], exports')

inferModule (Module modname defss exports) = do
  (defss', exports') <- inferTopLevel defss exports
  return ()

inferRepresentations mod =
  withTheNewVarIdentSupply $ \var_supply -> do
    core_types <- readInitGlobalVarIO the_newCoreTypes
    let env = InferReprEnv core_types var_supply
    runInferRepr env $ inferModule mod

{-

inferTyAppE inf op (TypedSFType (TypeAnn arg_ty (SFType arg))) = do
  (op', BoxRT ::: op_type) <- coerceReturnRepr Boxed =<< inferReprExp op
  arg_ty' <- infFixUpType arg_ty
  arg' <- infFixUpType arg
  mreturn_type <- infApplyType (getSourcePos inf) op' arg_ty' (Just arg')
  return_type <-
    case mreturn_type
    of Just t -> return t
       Nothing -> internalError "inferTyAppE"
  let exp = ExpR (TyAppE inf op' arg')
  return (exp, return_type)

inferCallE inf op args = do
  (op', BoxRT ::: op_type) <- coerceReturnRepr Boxed =<< inferReprExp op
  (args', arg_types) <- mapAndUnzipM inferReprExp args
  
  (return_type, arg_coercions) <- applyCallType op_type arg_types
  let exp = arg_coercions ExpR (CallE inf op' args')
  undefined
-}