
{-# LANGUAGE ScopedTypeVariables, TypeFamilies, EmptyDataDecls,
             FlexibleInstances, DeriveDataTypeable #-}
module SystemF.Typecheck
       (Typed, TypedRec, TypeAnn(..),
        SFType(TypedSFType),
        fromTypedSFType,
        SFExpOf(TypedSFExp), FunOf(TypedSFFun),
        AltOf(TypedSFAlt),
        Pat(..),
        TRType, TRExp, TRAlt, TRFun,
        mapTypeAnn, traverseTypeAnn,
        functionType,
        typeCheckModule)
where

import Control.Applicative(Const(..))
import Control.Exception
import Control.Monad
import Control.Monad.Reader
import Data.Typeable(Typeable)
import Data.Maybe
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.Supply
import Gluon.Common.SourcePos
import Gluon.Core(Structure(..), Rec)
import Gluon.Core.Level

import GlobalVar
import Globals
import SystemF.Print
import SystemF.Syntax
import Builtins.Builtins
import Type.Var
import Type.Eval
import Type.Environment
import Type.Type
import Type.Rename
import Type.Compare

-- | Set to True for debugging
printTypeAssertions :: Bool
printTypeAssertions = False

{-
assertEqualTypesV :: SourcePos -> RType -> RType -> PureTC ()
assertEqualTypesV pos expected actual =
  assertEqualTypes pos (verbatim expected) (verbatim actual)

assertEqualTypes :: SourcePos -> RecType (Subst Rec) -> RecType (Subst Rec)
                 -> PureTC ()
assertEqualTypes pos expected actual = debug $ do
  tcAssertEqual pos expected actual
  where
    debug x
      | printTypeAssertions =
          let message = text "assertEqualTypes" $$
                        text "Expected:" <+> Gluon.pprExp (substFully expected) $$
                        text "Actual:  " <+> Gluon.pprExp (substFully actual)
          in traceShow message x
      | otherwise = x
-}

data TypeAnn t a =
  TypeAnn { typeAnnotation :: Type
          , typeAnnValue :: t a
          }

mapTypeAnn :: (t a -> s b) -> TypeAnn t a -> TypeAnn s b
mapTypeAnn f (TypeAnn t x) = TypeAnn t (f x)

traverseTypeAnn :: Monad m =>
                   (t a -> m (s b)) -> TypeAnn t a -> m (TypeAnn s b)
traverseTypeAnn f (TypeAnn t x) = do
  y <- f x
  return $ TypeAnn t y

class HasType a where getTypeAnn :: a -> Type

data Typed a deriving(Typeable)

instance Structure a => Structure (Typed a)

data instance SFType (Typed Rec) = TypedSFType (TypeAnn SFType Rec)
newtype instance SFExpOf (Typed s) s' = TypedSFExp (TypeAnn (SFExpOf s) s')
newtype instance AltOf (Typed s) s' = TypedSFAlt (TypeAnn (AltOf s) s')
newtype instance FunOf (Typed s) s' = TypedSFFun (TypeAnn (FunOf s) s')

data instance Pat (Typed Rec) =
    TypedWildP TRType
  | TypedVarP Var TRType
  | TypedTupleP [Pat TypedRec]

type TypedRec = Typed Rec
type TRType = SFType TypedRec
type TRExp = SFRecExp TypedRec
type TRAlt = RecAlt TypedRec
type TRFun = Fun TypedRec
type TRPat = Pat TypedRec

instance HasType (SFType TypedRec) where
  getTypeAnn (TypedSFType x) = typeAnnotation x

instance HasType (SFExpOf TypedRec TypedRec) where
  getTypeAnn (TypedSFExp x) = typeAnnotation x

instance HasType (AltOf TypedRec TypedRec) where
  getTypeAnn (TypedSFAlt x) = typeAnnotation x

instance HasType (FunOf TypedRec TypedRec) where
  getTypeAnn (TypedSFFun x) = typeAnnotation x

fromTypedSFType :: SFType TypedRec -> Type 
fromTypedSFType (TypedSFType (TypeAnn _ (SFType t))) = t

withMany :: (a -> (b -> c) -> c) -> [a] -> ([b] -> c) -> c
withMany f xs k = go xs k
  where
    go (x:xs) k = f x $ \y -> go xs $ \ys -> k (y:ys)
    go []     k = k []

tyPatType :: RTyPat -> Type
tyPatType (TyPat _ t) = fromSFType t

patType :: RPat -> Type
patType (WildP t)  = fromSFType t
patType (VarP _ t) = fromSFType t
patType (TupleP ps) = let size = length ps
                          con = VarT $ pyonTupleTypeCon size
                          field_types = map patType ps
                      in typeApp con field_types

functionType :: RFun -> Type 
functionType (Fun { funTyParams = ty_params
                  , funParams = params
                  , funReturnType = ret
                  }) =
  let ty_param_reprs = [ValPT (Just v) ::: fromSFType k | TyPat v k <- ty_params]
      param_reprs = [ValPT Nothing ::: patType p | p <- params]
      ret_repr = ValRT ::: fromSFType ret
  in pureFunType (ty_param_reprs ++ param_reprs) ret_repr
      
-------------------------------------------------------------------------------
-- Type-checking environment

data TCEnv = TCEnv 
             { tcVarIDSupply :: !(IdentSupply Var)
             , tcTypeEnv     :: TypeEnv
             }

type TCM a = ReaderT TCEnv IO a

typeError = error

assume :: Var -> ReturnRepr ::: Type -> TCM a -> TCM a 
assume v t m = local add_to_env m
  where
    add_to_env env = env {tcTypeEnv = insertType v t $ tcTypeEnv env}

lookupVar :: Var -> TCM Type
lookupVar v = do
  env <- asks tcTypeEnv
  case lookupType v env of
    Just (_ ::: t) -> return t
    Nothing -> internalError $ "lookupVar: No type for variable: " ++ show v

tcLookupDataCon :: Var -> TCM DataConType
tcLookupDataCon v = do
  env <- asks tcTypeEnv
  case lookupDataCon v env of
    Just dct -> return dct
    Nothing -> internalError $ "lookupVar: No type for data constructor: " ++ show v

checkType :: SourcePos -> Type -> Type -> TCM Bool
checkType pos expected given = ReaderT $ \env -> do
  compareTypes (tcVarIDSupply env) pos (tcTypeEnv env) expected given

assumePat :: RPat -> (Pat TypedRec -> TCM b) -> TCM b
assumePat p k =
  case p
  of WildP p_ty -> k . TypedWildP =<< typeInferType p_ty
     VarP v p_ty -> do
       p_ty' <- typeInferType p_ty
       assume v (ValRT ::: fromSFType p_ty) $ k (TypedVarP v p_ty')
     TupleP pats -> withMany assumePat pats $ \pats' -> k (TypedTupleP pats')

assumeTyPat :: RTyPat -> (TyPat TypedRec -> TCM b) -> TCM b
assumeTyPat (TyPat v t) k = do
  t' <- typeInferType t
  assume v (ValRT ::: fromSFType t) $ k (TyPat v t')

-- Assume a function definition.  Do not check the function definition's body.
assumeDef :: RDef -> TCM a -> TCM a
assumeDef (Def v fun) = assume v (ValRT ::: functionType fun)

assumeDefs defs m = foldr assumeDef m defs

applyType op_type arg_type arg = ReaderT $ \env -> do
  applied <- typeOfApp (tcVarIDSupply env) noSourcePos (tcTypeEnv env)
             op_type arg_type arg
  return $ case applied
           of Just (_ ::: t) -> Just t
              Nothing -> Nothing

typeInferType :: RType -> TCM (SFType TypedRec)
typeInferType (SFType ty) =
  case ty
  of VarT v -> return_type =<< lookupVar v
     AppT op arg -> do
         -- Get type of op and argument
         op' <- typeInferType (SFType op)
         arg' <- typeInferType (SFType arg)
         let inferred_arg = fromTypedSFType arg'
             
         -- Get type of application
         applied <- applyType (getTypeAnn op') (getTypeAnn arg') (Just inferred_arg)
         case applied of
           Nothing -> typeError "Error in type application"
           Just result_t -> return_type result_t

     FunT (param ::: dom) (ret ::: rng) -> do
       -- Check that types are valid
       typeInferType (SFType dom)
       assume_param param dom $ typeInferType (SFType rng)

       case getLevel rng of
         TypeLevel -> return_type pureT
         KindLevel -> return_type kindT
  where
    assume_param (ValPT (Just v)) t k = assume v (ValRT ::: t) k
    assume_param _ _ k = k
    
    return_type inferred_type =
      return $ TypedSFType (TypeAnn inferred_type (SFType ty))

typeInferExp :: RExp -> TCM TRExp
typeInferExp expression =
    case expression
    of VarE {expInfo = inf, expVar = v} ->
         typeInferVarE inf v
       LitE {expInfo = inf, expLit = l} ->
         checkLiteralType inf l
       AppE {expInfo = inf, expOper = op, expTyArgs = ts, expArgs = args} ->
         typeInferAppE inf op ts args
       LamE {expInfo = inf, expFun = f} -> do
         ti_fun <- typeInferFun f
         return $ TypedSFExp $ TypeAnn (getTypeAnn ti_fun) (LamE inf ti_fun)
       LetE {expInfo = inf, expBinder = pat, expValue = e, expBody = body} ->
         typeInferLetE inf pat e body
       LetrecE {expInfo = inf, expDefs = defs, expBody = body} ->
         typeInferLetrecE inf defs body
       CaseE {expInfo = inf, expScrutinee = scr, expAlternatives = alts} ->
         typeInferCaseE inf scr alts
         
-- To infer a variable's type, just look it up in the environment
typeInferVarE :: ExpInfo -> Var -> TCM TRExp
typeInferVarE inf var = do
  ty <- lookupVar var
  return $ TypedSFExp $ TypeAnn ty (VarE inf var)

-- Use the type that was attached to the literal value, but also verify that
-- it's a valid type
checkLiteralType :: ExpInfo -> Lit -> TCM TRExp
checkLiteralType inf l = do
  -- Check that type is valid
  let literal_type = literalType l
  _ <- typeInferType (SFType literal_type)
  
  if isValidLiteralType literal_type l
    then return $ TypedSFExp $ TypeAnn literal_type (LitE inf l)
    else typeError "Not a valid literal type"

isValidLiteralType ty lit =
  -- Get the type constructor
  case fromVarApp ty
  of Just (v, args) ->
       -- Based on the literal, check whether the type constructor is 
       -- acceptable
       case lit
       of IntL _ _ -> v `isPyonBuiltin` the_int
          FloatL _ _ -> v `isPyonBuiltin` the_float
          BoolL _ -> v `isPyonBuiltin` the_bool
          NoneL -> v `isPyonBuiltin` the_NoneType
     Nothing ->
       -- Literals cannot have other types 
       False

typeInferAppE inf op ty_args args = do
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
  return $ TypedSFExp $ TypeAnn result_type new_exp

computeInstantiatedType :: SourcePos -> Type -> [TRType] -> TCM Type
computeInstantiatedType inf op_type args = go op_type args
  where
    go op_type (TypedSFType (TypeAnn arg_kind arg) : args) = do
      -- Apply operator to argument
      app_type <- applyType op_type arg_kind (Just $ fromSFType arg)
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
      result <- applyType op_type arg_t Nothing
      case result of
        Just op_type' -> apply op_type' arg_ts
        Nothing -> typeError $ "Error in application at " ++ show pos
    
    apply op_type [] = return op_type

typeInferFun :: RFun -> TCM TRFun
typeInferFun fun@(Fun { funInfo = info
                      , funTyParams = ty_params
                      , funParams = params
                      , funReturnType = return_type
                      , funBody = body}) =
  assumeTyParams $ \new_ty_params -> assumeParams $ \new_params -> do
    ti_body <- typeInferExp body
    ti_return_type <- typeInferType return_type
    
    -- Inferred type must match return type
    checkType noSourcePos (fromSFType return_type) (getTypeAnn ti_body)
    
    -- Create the function's type
    let ty = functionType fun
    
    let new_fun =
          Fun { funInfo = info
              , funTyParams = new_ty_params
              , funParams = new_params
              , funReturnType = ti_return_type
              , funBody = ti_body
              }
    return $ TypedSFFun $ TypeAnn ty new_fun
  where
    assumeTyParams = withMany assumeTyPat ty_params
    assumeParams = withMany assumePat params

typeInferLetE :: ExpInfo -> RPat -> RExp -> RExp -> TCM TRExp
typeInferLetE inf pat expression body = do
  ti_exp <- typeInferExp expression
  
  -- Expression type must match pattern type
  checkType noSourcePos (getTypeAnn ti_exp) (patType pat)

  -- Assume the pattern while inferring the body; result is the body's type
  assumePat pat $ \pat' -> do
    ti_body <- typeInferExp body
    let new_exp = LetE inf pat' ti_exp ti_body
    return $ TypedSFExp $ TypeAnn (getTypeAnn ti_body) new_exp

typeInferLetrecE :: ExpInfo -> [RDef] -> RExp -> TCM TRExp
typeInferLetrecE inf defs body =
  typeCheckDefGroup defs $ \defs' -> do
    ti_body <- typeInferExp body
    let new_exp = LetrecE inf defs' ti_body
    return $ TypedSFExp $ TypeAnn (getTypeAnn ti_body) new_exp

typeInferCaseE :: ExpInfo -> RExp -> [Alt Rec] -> TCM TRExp
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
  zipWithM (checkType pos) alt_subst_types (tail alt_subst_types)

  -- The expression's type is the type of an alternative
  let result_type = getTypeAnn $ head ti_alts
  return $! TypedSFExp $! TypeAnn result_type $ CaseE inf ti_scr ti_alts

typeCheckAlternative :: SourcePos -> Type -> Alt Rec -> TCM TRAlt
typeCheckAlternative pos scr_type (Alt { altConstructor = con
                                       , altTyArgs = types
                                       , altParams = fields
                                       , altBody = body}) = do
  -- Process arguments
  arg_vals <- mapM typeInferType types

  -- Apply constructor to type arguments
  con_ty <- tcLookupDataCon con
  (arg_types, _ ::: con_scr_type) <- instantiatePatternType pos con_ty arg_vals
  
  -- Verify that applied type matches constructor type
  checkType pos scr_type con_scr_type

  -- Verify that fields have the expected types
  check_number_of_fields arg_types fields
  fields' <- zipWithM (checkAltParam pos) arg_types fields

  -- Match the resulting type against the function type
  -- field1 -> field2 -> ... -> scr_type
  ti_body <- bindParamTypes fields' $ typeInferExp body

  let new_alt = Alt con arg_vals fields' ti_body
  return $ TypedSFAlt $ TypeAnn (getTypeAnn ti_body) new_alt
  where
    check_number_of_fields atypes fs
      | length atypes /= length fields =
        internalError $ "typeCheckAlternative: Wrong number of fields in pattern (expected " ++
        show (length atypes) ++ ", got " ++ show (length fields) ++ ")"
      | otherwise = return ()


bindParamTypes params m = foldr bind_param_type m params
  where
    bind_param_type (TypedVarP param param_ty) m =
      assume param (ValRT ::: fromTypedSFType param_ty) m

-- | Verify that the given paramater matches the expected parameter
checkAltParam pos (_ ::: expected_type) (VarP field_var given_type) = do 
  gt <- typeInferType given_type
  checkType pos expected_type (fromTypedSFType gt)
  return (TypedVarP field_var gt)

-- | Instantiate a data constructor's type in a pattern, given the
--   pattern's type arguments.
instantiatePatternType :: SourcePos
                       -> DataConType
                       -> [SFType TypedRec]
                       -> TCM ([ReturnRepr ::: Type], ReturnRepr ::: Type)
instantiatePatternType pos con_ty arg_vals 
  | length (dataConPatternParams con_ty) /= length arg_vals =
      internalError "instantiateConType"
  | otherwise = do
      subst <- instantiate_arguments emptySubstitution $
               zip (dataConPatternParams con_ty) arg_vals
      
      -- Apply substitution to field and range types
      let fields = [repr ::: substitute subst t
                   | repr ::: t <- dataConPatternArgs con_ty]
          range = case dataConPatternRange con_ty
                  of repr ::: t -> repr ::: substitute subst t
      return (fields, range)
  where
    -- Instantiate the type by substituing arguments for the constructor's
    -- type parameters
    instantiate_arguments subst ((param, arg) : args) = do
      -- Apply substitution to parameter
      let (param_repr ::: param_type) = substituteBinding subst param
          arg_val = fromTypedSFType arg
          arg_type = getTypeAnn arg
          
      -- Does argument type match parameter type?
      checkType pos param_type arg_type
      
      -- Update the substitution
      let subst' = case param_repr
                   of ValPT (Just param_var) ->
                        insertSubstitution param_var arg_val subst
      
      instantiate_arguments subst' args
    
    instantiate_arguments subst [] = return subst

typeCheckDefGroup :: [RDef] -> ([Def TypedRec] -> TCM b) -> TCM b
typeCheckDefGroup defs k = assumeDefs defs $ do
  -- Check all defined function bodies
  xs <- mapM typeCheckDef defs

  -- Run the continuation in this environment
  k xs
  where
    -- To typecheck a definition, check the function it contains
    typeCheckDef (Def v fun) = do
      fun_val <- typeInferFun fun
      return $ Def v fun_val


typeCheckExport :: Export Rec -> TCM (Export TypedRec) 
typeCheckExport (Export pos spec f) = do
  f' <- typeInferFun f
  return $ Export pos spec f'

typeCheckModule (Module module_name defs exports) = do
  global_type_env <- readInitGlobalVarIO the_systemFTypes
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
