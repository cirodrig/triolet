
{-# LANGUAGE ScopedTypeVariables, TypeFamilies, EmptyDataDecls,
             FlexibleInstances, DeriveDataTypeable, TypeSynonymInstances #-}
module SystemF.TypecheckMem
       (Typed,
        RTypeAnn(..),
        Typ(..),
        Exp(..),
        Alt(..),
        Fun(..),
        Pat(..),
        TyPat(..),
        Ret(..),
        TypTM, ExpTM, AltTM, FunTM, PatTM,
        fromTypTM,
        fromPatTM,
        functionType,
        typeCheckModule)
where

import Control.Applicative(Const(..))
import Control.Exception
import Control.Monad
import Control.Monad.Reader
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

data RTypeAnn a = 
  RTypeAnn { typeAnnotation :: {-# UNPACK #-}!ReturnType
           , typeAnnValue :: a
           }

newtype instance Typ (Typed Mem) = TypTM (RTypeAnn Type)
newtype instance Exp (Typed Mem) = ExpTM (RTypeAnn (BaseExp TM))
newtype instance Alt (Typed Mem) = AltTM (RTypeAnn (BaseAlt TM))
newtype instance Fun (Typed Mem) = FunTM (RTypeAnn (BaseFun TM))

data instance Pat (Typed Mem) = TypedMemVarP Var ParamType
                              | TypedLocalVarP Var Type ExpTM
data instance TyPat (Typed Mem) = TyPatTM Var TypTM
newtype instance Ret (Typed Mem) = RetTM {fromRetTM :: ReturnType}

type TM = Typed Mem

type TypTM = Typ TM
type ExpTM = Exp TM
type AltTM = Alt TM
type FunTM = Fun TM
type PatTM = Pat TM
type TyPatTM = TyPat TM

-- | Get the type of an expression
getExpType :: ExpTM -> ReturnType
getExpType (ExpTM (RTypeAnn t _)) = t

-- | Get the kind of a type
getTypType :: TypTM -> Type
getTypType (TypTM (RTypeAnn (_ ::: t) _)) = t

fromTypTM :: TypTM -> Type 
fromTypTM (TypTM (RTypeAnn _ t)) = t

tyPatType :: TyPat Mem -> Type
tyPatType (TyPatM _ t) = t

fromPatTM :: PatTM -> PatM
fromPatTM (TypedMemVarP v pt) = MemVarP v pt
fromPatTM (TypedLocalVarP v ty repr) = LocalVarP v ty repr'
  where repr' = internalError "fromPatTM: Not implemented"

-- | Determine the type that a pattern-bound variable has after it's been 
--   bound.
patType :: PatM -> ReturnType
patType (MemVarP _ (prepr ::: ty)) = paramReprToReturnRepr prepr ::: ty
patType (LocalVarP _ t _) = ReadRT ::: t

functionType :: FunM -> Type 
functionType (FunM (Fun { funTyParams = ty_params
                        , funParams = params
                        , funReturn = RetM ret
                        })) =
  let ty_param_reprs = [ValPT (Just v) ::: k | TyPatM v k <- ty_params]
      param_reprs = map get_param_repr params
      ret_repr = ret
  in funType (ty_param_reprs ++ param_reprs) ret_repr
  where
    get_param_repr (MemVarP _ rt) = rt
    get_param_repr (LocalVarP _ _ _) = internalError "functionType"

-------------------------------------------------------------------------------

assumePat :: PatM -> (PatTM -> TCM b) -> TCM b
assumePat (MemVarP v (prepr ::: ty)) k =
  assume v (paramReprToReturnRepr prepr ::: ty) $
  k (TypedMemVarP v (prepr ::: ty))

assumePat (LocalVarP v ty repr) k = internalError "assumePat"

-- | Add pattern-bound variables from a let statement to the environment 
--   while processing the definition of the local value
assumeDefiningLetPattern :: PatM -> TCM a -> TCM a
assumeDefiningLetPattern (MemVarP _ _) m = m -- Not visible during definition
assumeDefiningLetPattern (LocalVarP v ty _) m = assume v (OutRT ::: ty) m

-- | Add pattern-bound variables from a let statement to the environment 
--   while processing the use of the local value
assumeUsingLetPattern :: PatM -> TCM a -> TCM a
assumeUsingLetPattern pattern k =
  case pattern
  of MemVarP _ _      -> assumePat pattern $ \_ -> k
     LocalVarP v ty _ -> assume v (ReadRT ::: ty) k

assumeTyPat :: TyPat Mem -> (TyPat TM -> TCM b) -> TCM b
assumeTyPat (TyPatM v t) k = do
  t' <- typeInferType (TypM t)
  assume v (ValRT ::: t) $ k (TyPatTM v t')

-- Assume a function definition.  Do not check the function definition's body.
assumeDef :: Def Mem -> TCM a -> TCM a
assumeDef (Def v fun) = assume v (BoxRT ::: functionType fun)

assumeDefs defs m = foldr assumeDef m defs

typeInferType :: TypM -> TCM TypTM
typeInferType (TypM ty) =
  case ty
  of VarT v -> return_type =<< lookupVar v
     AppT op arg -> do
         -- Get type of operator and argument
         op' <- typeInferType (TypM op)
         arg' <- typeInferType (TypM arg)
         let inferred_arg = fromTypTM arg'
             
         -- Get type of application
         applied <- applyType (getTypType op') (ValRT ::: getTypType arg') (Just inferred_arg)
         case applied of
           Nothing -> typeError "Error in type application"
           Just result_t -> return_type result_t

     FunT (param ::: dom) (ret ::: rng) -> do
       -- Check that types are valid
       typeInferType (TypM dom)
       assume_param param dom $ typeInferType (TypM rng)

       case getLevel rng of
         TypeLevel -> return_type (ValRT ::: pureT)
         KindLevel -> return_type (ValRT ::: kindT)
  where
    assume_param (ValPT (Just v)) t k = assume v (ValRT ::: t) k
    assume_param _ _ k = k
    
    return_type inferred_type =
      return $ TypTM (RTypeAnn inferred_type ty)

typeInferExp :: ExpM -> TCM ExpTM
typeInferExp (ExpM expression) =
    case expression
    of VarE {expInfo = inf, expVar = v} ->
         typeInferVarE inf v
       LitE {expInfo = inf, expLit = l} ->
         typeInferLitE inf l
       AppE {expInfo = inf, expOper = op, expTyArgs = ts, expArgs = args} ->
         traceShow (text "typeInferAppE:" <+> pprExp (ExpM expression)) $ typeInferAppE inf op ts args
       LamE {expInfo = inf, expFun = f} -> do
         ti_fun <- typeInferFun f
         let FunTM (RTypeAnn return_type _) = ti_fun
         return $ ExpTM $ RTypeAnn return_type (LamE inf ti_fun)
       LetE {expInfo = inf, expBinder = pat, expValue = e, expBody = body} ->
         typeInferLetE inf pat e body
       LetrecE {expInfo = inf, expDefs = defs, expBody = body} ->
         typeInferLetrecE inf defs body
       CaseE {expInfo = inf, expScrutinee = scr, expAlternatives = alts} ->
         typeInferCaseE inf scr alts

-- To infer a variable's type, just look it up in the environment
typeInferVarE :: ExpInfo -> Var -> TCM ExpTM
typeInferVarE inf var = do
  ty <- lookupVar var
  return $ ExpTM $ RTypeAnn ty (VarE inf var)

-- Use the type that was attached to the literal value, but also verify that
-- it's a valid type
typeInferLitE :: ExpInfo -> Lit -> TCM ExpTM
typeInferLitE inf l = do
  let literal_type = literalType l
  checkLiteralType l
  return $ ExpTM $ RTypeAnn (ValRT ::: literal_type) (LitE inf l)

typeInferAppE inf op ty_args args = do
  let pos = getSourcePos inf
  ti_op <- typeInferExp op

  -- Apply to type arguments
  ti_ty_args <- mapM typeInferType ty_args
  inst_type <- traceShow (text "typeInferAppE" <+> pprReturnType (getExpType ti_op)) $ computeInstantiatedType pos (getExpType ti_op) ti_ty_args

  -- Apply to other arguments
  ti_args <- mapM typeInferExp args
  result_type <- computeAppliedType pos inst_type (map getExpType ti_args)
  
  let new_exp = AppE inf ti_op ti_ty_args ti_args
  return $ ExpTM $ RTypeAnn result_type new_exp

computeInstantiatedType :: SourcePos -> ReturnType -> [TypTM] -> TCM ReturnType
computeInstantiatedType inf op_type args = go op_type args
  where
    go (BoxRT ::: op_type) (TypTM (RTypeAnn arg_kind arg) : args) = do
      -- Apply operator to argument
      app_type <- applyType op_type arg_kind (Just arg)
      case app_type of
        Just result_type -> go result_type args
        Nothing -> typeError "Error in type application"

    go op_type [] = return op_type
    
    go _ _ = typeError "Operator has wrong representation"

-- | Given a function type and a list of argument types, compute the result of
-- applying the function to the arguments.
computeAppliedType :: SourcePos 
                   -> ReturnType
                   -> [ReturnType]
                   -> TCM ReturnType
computeAppliedType pos op_type arg_types =
  traceShow (text "CAT" <+> vcat (pprReturnType op_type : map pprReturnType arg_types)) $
  apply op_type arg_types
  where
    apply (BoxRT ::: op_type) (arg_t:arg_ts) = do
      result <- applyType op_type arg_t Nothing
      case result of
        Just op_type' -> apply op_type' arg_ts
        Nothing -> typeError $ "Error in application at " ++ show pos
    
    apply op_type [] = return op_type

    apply _ _ = typeError "Operator has wrong representation"

typeInferFun :: FunM -> TCM FunTM
typeInferFun fun@(FunM (Fun { funInfo = info
                            , funTyParams = ty_params
                            , funParams = params
                            , funReturn = RetM return_type
                            , funBody = body})) =
  assumeTyParams $ \new_ty_params -> assumeParams $ \new_params -> do
    ti_body <- typeInferExp body

    -- Inferred type must match return type
    checkReturnType noSourcePos return_type (getExpType ti_body)
    
    -- Create the function's type
    let ty = functionType fun
    
    let new_fun =
          Fun { funInfo = info
              , funTyParams = new_ty_params
              , funParams = new_params
              , funReturn = RetTM return_type
              , funBody = ti_body
              }
    return $ FunTM $ RTypeAnn (BoxRT ::: ty) new_fun
  where
    assumeTyParams = withMany assumeTyPat ty_params
    assumeParams = withMany assumePat params

typeInferLetE :: ExpInfo -> PatM -> ExpM -> ExpM -> TCM ExpTM
typeInferLetE inf pat expression body = do
  ti_pat <- type_infer_pattern pat
  ti_exp <- assumeDefiningLetPattern pat $ typeInferExp expression

  -- Expression type must match pattern type
  checkReturnType noSourcePos (getExpType ti_exp) (patType pat)

  -- Assume the pattern while inferring the body; result is the body's type
  ti_body <- assumeUsingLetPattern pat $ typeInferExp body
  let return_type = getExpType ti_body
      new_exp = LetE inf ti_pat ti_exp ti_body
  return $ ExpTM $ RTypeAnn return_type new_exp
  where
    type_infer_pattern (MemVarP v pt) = return $ TypedMemVarP v pt
    type_infer_pattern (LocalVarP v ty repr) = do
      repr' <- typeInferExp repr
      return $ TypedLocalVarP v ty repr'

typeInferLetrecE :: ExpInfo -> [Def Mem] -> ExpM -> TCM ExpTM
typeInferLetrecE inf defs body =
  typeCheckDefGroup defs $ \defs' -> do
    ti_body <- typeInferExp body
    let new_exp = LetrecE inf defs' ti_body
    return $ ExpTM $ RTypeAnn (getExpType ti_body) new_exp

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
  let alt_subst_types = [rt | AltTM (RTypeAnn rt _) <- ti_alts]
  zipWithM (checkReturnType pos) alt_subst_types (tail alt_subst_types)

  -- The expression's type is the type of an alternative
  let result_type = case head ti_alts of AltTM (RTypeAnn rt _) -> rt
  return $! ExpTM $! RTypeAnn result_type $ CaseE inf ti_scr ti_alts

typeCheckAlternative :: SourcePos -> ReturnType -> AltM -> TCM AltTM
typeCheckAlternative pos scr_type (AltM (Alt { altConstructor = con
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
          [(ty, kind) | TypTM (RTypeAnn (_ ::: kind) ty) <- arg_vals]
        existential_vars = [(v, k) | TyPatM v k <- ex_fields]
    in instantiatePatternType pos con_ty argument_types existential_vars

  -- Verify that applied type matches constructor type
  checkReturnType pos scr_type con_scr_type

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
      let ret_repr ::: ret_type = getExpType ti_body
      when (ret_type `typeMentionsAny` Set.fromList [v | TyPatTM v _ <- ex_fields']) $
        typeError "Existential type variable escapes"

      let new_alt = Alt con arg_vals ex_fields' fields' ti_body
      return $ AltTM $ RTypeAnn (getExpType ti_body) new_alt
  where
    check_number_of_fields atypes fs
      | length atypes /= length fields =
        internalError $ "typeCheckAlternative: Wrong number of fields in pattern (expected " ++
        show (length atypes) ++ ", got " ++ show (length fields) ++ ")"
      | otherwise = return ()

    check_arg expected_rtype (MemVarP _ (given_prepr ::: given_type)) =
      let given_rrepr = paramReprToReturnRepr given_prepr
      in checkReturnType pos expected_rtype (given_rrepr ::: given_type)

bindParamTypes params m = foldr bind_param_type m params
  where
    bind_param_type (TypedMemVarP param (param_repr ::: param_ty)) m =
      assume param (paramReprToReturnRepr param_repr ::: param_ty) m

-- | Verify that the given paramater matches the expected parameter
checkAltParam pos expected_type (MemVarP field_var (given_repr ::: given_type)) = do
  let gtype = paramReprToReturnRepr given_repr ::: given_type
  checkReturnType pos expected_type gtype
  return (TypedMemVarP field_var (given_repr ::: given_type))

typeCheckDefGroup :: [Def Mem] -> ([Def TM] -> TCM b) -> TCM b
typeCheckDefGroup defs k = assumeDefs defs $ do
  k =<< mapM typeCheckDef defs
  where
    -- To typecheck a definition, check the function it contains
    typeCheckDef (Def v fun) = do
      fun_val <- typeInferFun fun
      return $ Def v fun_val

typeCheckExport :: Export Mem -> TCM (Export TM)
typeCheckExport (Export pos spec f) = do
  f' <- typeInferFun f
  return $ Export pos spec f'

typeCheckModule (Module module_name defs exports) = do
  global_type_env <- readInitGlobalVarIO the_memTypes
  withTheNewVarIdentSupply $ \varIDs ->
    let env = TCEnv varIDs global_type_env
    in do (defs', exports') <- runReaderT (typeCheckDefGroups defs exports) env
          return $ Module module_name defs' exports'
  where
    typeCheckDefGroups (defs:defss) exports = 
      typeCheckDefGroup defs $ \defs' -> do
        (defss', exports') <- typeCheckDefGroups defss exports
        return (defs' : defss', exports')
      
    typeCheckDefGroups [] exports = do 
      exports' <- mapM typeCheckExport exports
      return ([], exports')
