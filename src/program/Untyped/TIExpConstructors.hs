{-| Smart constructors for type-annotated expressions.

This is in a separate module to avoid cyclic imports.

-}

{-# LANGUAGE FlexibleContexts, ConstraintKinds #-}
module Untyped.TIExpConstructors where

import Control.Concurrent.MVar
import Control.Monad
import Control.Monad.Trans
import Data.IORef

import Common.Error
import Common.SourcePos
import Common.Supply
import qualified SystemF.Syntax as SF
import qualified Builtins.Builtins as SF
import SystemF.Syntax (ExpInfo, DefGroup)
import Untyped.Kind
import Untyped.Syntax as Untyped
import Untyped.TIExp
import Untyped.TIMonad
import Untyped.Type
import Untyped.TypeUnif
import Untyped.Unif
import qualified Type.Type as SF
import qualified Type.Var as SF
import Export

-------------------------------------------------------------------------------
-- Type smart constructors

-- | Inject a System F type into 'TIType'
delayType :: SF.Type -> TIType
delayType t = DelayedType (return t)

-- | Convert a kind to a 'TIType'
mkKind :: Kind -> TIType
mkKind k = delayType $ convertKind k

convertKind :: Kind -> SF.Kind
convertKind Star = SF.boxT
convertKind (k1 :-> k2) = convertKind k1 `SF.FunT` convertKind k2

mkType :: HMType -> TIType
mkType ty = DelayedType $ convertHMType ty

-- | Make the type of an uncurried function from @domain@ to @range@.
--
-- Depending on the calling convention indicated by the range, a stream
-- function or action function is generated.
functionType :: [SF.Type]      -- ^ domain
             -> SF.Type        -- ^ range
             -> SF.Type        -- ^ System F type
functionType domain range = foldr SF.FunT range domain

forallType :: SF.Var -> SF.Type -> SF.Type -> SF.Type
forallType v dom rng = SF.AllT (v SF.::: dom) rng

convertHMType ty = go =<< normalize ty
  where
    go (VarTy v) = liftM SF.VarT $ tyVarToSystemF v
    go (ConTy c) = return $ SF.VarT (tyConSFVar c)

    -- Function types should only appear in an AppTy term
    go (FunTy _) = internalError "Unexpected function type constructor"

    go (TupleTy n) = return $ SF.VarT $ SF.tupleTypeCon n

    go ty@(AppTy _ _) = do
      (operator, arguments) <- uncurryApp ty
      arg_types <- mapM convertHMType arguments
      case operator of
        -- Special-case function type applications
        FunTy n
          | length arg_types == n + 1 ->
              let fun_params = init arg_types
                  fun_result = last arg_types
              in return $ functionType fun_params fun_result
          | otherwise ->
              -- This should never happen, because type inference operates on
              -- uncurried functions
              fail "Wrong number of arguments to function after type inference"
        _ -> do
          oper_type <- convertHMType operator 
          return $ SF.typeApp oper_type arg_types

    go (TFunAppTy op ts) = do
      let sf_op = tyConSFVar op
      sf_ts <- mapM convertHMType ts
      return $ SF.typeApp (SF.VarT sf_op) sf_ts

    go (AnyTy k) = return $ SF.AnyT $ convertKind k

-- | Assign a type to a free type variable.  This is done after type inference 
--   is complete, so that unifiable variables can be translated to System F.
tyVarToSystemF :: TyVar -> TE SF.Var
tyVarToSystemF v = do
  con <- newTyVar (uVarName v) (uVarKind v)
  unifyUVar v (ConTy con)
  return $ tyConSFVar con

mkPredicate :: Predicate -> TIType
mkPredicate prd = DelayedType $ convertPredicate prd

convertPredicate (IsInst cls ty) = do
  ty' <- convertHMType ty
  return $ SF.varApp (tyConSFVar cls) [ty']

convertPredicate (IsEqual t1 t2) = do
  -- Create a coercion value
  t1' <- convertHMType t1
  t2' <- convertHMType t2
  return $ SF.typeApp (SF.CoT SF.boxT) [t1', t2']

mkTyScheme :: TyScheme -> TIType
mkTyScheme scm = DelayedType $ convertTyScheme scm

convertTyScheme (Qualified qvars cst ty) = do
  let qvars' = map tyConSFVar qvars
  cst' <- mapM convertPredicate cst
  ty' <- convertHMType ty
  let constrained_type = functionType cst' ty'
      parametric_type = foldr mkFun constrained_type (zip qvars qvars')
  return parametric_type
  where
    mkFun (v, sf_v) ty =
      forallType sf_v (convertKind (tyConKind v)) ty

-------------------------------------------------------------------------------
-- Expression smart constructors

mkWildP :: TIType -> TIPat
mkWildP ty = TIWildP ty

mkVarP :: SF.Var -> TIType -> TIPat
mkVarP v ty = TIVarP v ty

mkTupleP :: [TIPat] -> TIPat
mkTupleP fs = TITupleP fs

mkVarE :: SourcePos -> TIRepr -> SF.Var -> TIExp
mkVarE pos repr v = VarTE (tiInfo pos repr) v

mkConE :: SourcePos -> TIRepr -> SF.Var -> [TIType] -> [TIType]
       -> [TISize] -> Maybe SF.Var -> [TIExp] -> TIExp
mkConE pos repr c ty_args ex_types size_params m_tyob_con fields =
  let con = TIConInst c ty_args ex_types
  in ConTE (tiInfo pos repr) con size_params m_tyob_con fields

mkTupleE :: SourcePos -> TIRepr -> [TIType] -> [TISize] -> [TIExp] -> TIExp
mkTupleE pos repr elt_types size_params fields =
  let n_elts = length fields
      con = TIConInst (SF.tupleCon n_elts) elt_types []
  in ConTE (tiInfo pos repr) con size_params Nothing fields

-- | Create the expression
--   list @n @t (fiInt @n n) (stuckBox @(arr n t) (array @t e1 e2 ...))
mkListE :: SourcePos -> TIType -> TIRepr -> [TIExp] -> TIExp
mkListE pos elt_type elt_repr elts =
  let n = length elts

      -- The list size as a type
      size = delayType (SF.IntT $ fromIntegral n)

      -- The array type
      array_type = DelayedType $ do
        sf_elt_type <- case elt_type of DelayedType t -> t
        return $ SF.varApp SF.arrV [SF.IntT $ fromIntegral n, sf_elt_type]

      -- Indexed integer 
      fiint_repr = TICoreRepr (SF.coreBuiltin SF.The_repr_FIInt) [size] []
      integer = mkConE pos fiint_repr fiint_con [size] [] [] Nothing
                [mkIntLitE pos n]

      -- Array expression
      array_repr = TICoreRepr (SF.coreBuiltin SF.The_frontend_repr_arr) 
                   [size, elt_type] [Left (mkIntLitE pos n), Right elt_repr]
      array_size = TISize array_type array_repr
      array = ArrayTE (tiInfo pos array_repr) elt_type elts
      array_box = mkConE pos TIBoxed
                  (SF.coreBuiltin SF.The_stuckBox)
                  [array_type] [] [array_size]
                  (Just $ SF.coreBuiltin SF.The_frontend_repr_stuckBox)
                  [array]

      -- List object
      list_repr = TICoreRepr (SF.coreBuiltin SF.The_frontend_repr_list) [elt_type] []
  in mkConE pos list_repr
     (SF.coreBuiltin SF.The_make_list) [elt_type] [size]
     [] Nothing [integer, array_box]
  where
    sf_int_type = SF.intT
    fiint_con = SF.coreBuiltin SF.The_fiInt

mkIntLitE pos n =
  let repr = TICoreRepr (SF.coreBuiltin SF.The_repr_int) [] []
      sf_int_type = SF.intT
  in LitTE (tiInfo pos repr) $ SF.IntL (fromIntegral n) sf_int_type

mkFloatLitE pos n =
  let repr = TICoreRepr (SF.coreBuiltin SF.The_repr_float) [] []
      sf_float_type = SF.floatT
  in LitTE (tiInfo pos repr) $ SF.FloatL n sf_float_type

mkNoneE :: SourcePos -> TIExp
mkNoneE pos = mkLitE pos Untyped.NoneL

mkLitE :: SourcePos -> Untyped.Lit -> TIExp
mkLitE pos l =
  case l
  of Untyped.IntL n      -> mkIntLitE pos n
     Untyped.FloatL n    -> mkFloatLitE pos n
     Untyped.BoolL True  -> sf_constructor b_repr SF.The_True
     Untyped.BoolL False -> sf_constructor b_repr SF.The_False
     Untyped.NoneL       -> sf_constructor n_repr SF.The_None
  where
    sf_constructor repr c =
      mkConE pos repr (SF.coreBuiltin c) [] [] [] Nothing []

    b_repr = TICoreRepr (SF.coreBuiltin SF.The_repr_bool) [] []
    n_repr = TICoreRepr (SF.coreBuiltin SF.The_repr_NoneType) [] []

mkBuiltinCallE :: SourcePos -> TIRepr -> SF.BuiltinThing
               -> [TIType] -> [TIExp] -> TIExp
{-# INLINE mkBuiltinCallE #-}
mkBuiltinCallE pos repr thing ts args =
  let oper_repr = if null args
                  then repr     -- Same representation as result
                  else TIBoxed -- It's a function
  in mkAppE pos repr (mkVarE pos oper_repr (SF.coreBuiltin thing)) ts args

mkAppE :: SourcePos -> TIRepr -> TIExp -> [TIType] -> [TIExp] -> TIExp
mkAppE pos repr oper ts args = AppTE (tiInfo pos repr) oper ts args

mkUndefinedE :: SourcePos -> TIRepr -> TIType -> TIExp
mkUndefinedE pos repr ty =
  mkBuiltinCallE pos repr SF.The_fun_undefined [ty] [mkNoneE noSourcePos]

mkCoerceE :: SourcePos -> TIRepr -> TIType -> TIType -> TIExp -> TIExp
mkCoerceE pos repr from_ty to_ty e =
  CoerceTE (tiInfo pos repr) from_ty to_ty e

mkIfE :: SourcePos -> TIExp -> TIExp -> TIExp -> TIExp
mkIfE pos cond tr fa =
  let true_decon = TIDeConInst (SF.coreBuiltin SF.The_True) [] []
      false_decon = TIDeConInst (SF.coreBuiltin SF.The_False) [] []
      true_alt = TIAlt true_decon Nothing [] tr
      false_alt = TIAlt false_decon Nothing [] fa
  in CaseTE pos cond [] [true_alt, false_alt]

-- | Create a call of a polymorphic function with no constraint arguments.
mkPolyCallE :: SourcePos -> TIRepr -> TIExp -> [TIType] -> [TIExp] -> TIExp
mkPolyCallE _   _    oper []      []    = oper
mkPolyCallE pos repr oper ty_args args = mkAppE pos repr oper ty_args args

mkLetE :: SourcePos -> TIPat -> TIExp -> TIExp -> TIExp
mkLetE pos lhs rhs body = LetTE pos lhs rhs body

mkFunE :: SourcePos -> TIFun -> TIExp
mkFunE pos fun = LamTE (tiInfo pos TIBoxed) fun

mkLetrecE :: SourcePos -> SF.DefGroup TIDef -> TIExp -> TIExp
mkLetrecE pos defs body =
  LetfunTE pos defs body

mkCaseTE :: SourcePos -> TIExp -> [TISize] -> [TIAlt] -> TIExp
mkCaseTE pos scrutinee size_params alts =
  CaseTE pos scrutinee size_params alts

mkTupleCaseE :: SourcePos -> TIExp -> [TISize] -> [TIPat] -> TIExp -> TIExp
mkTupleCaseE pos scrutinee size_params patterns body =
  let pattern_types = [t | ~(TIVarP _ t) <- patterns]
      decon = TIDeConInst (SF.tupleCon $ length patterns) pattern_types []
  in mkCaseTE pos scrutinee size_params
     [TIAlt decon Nothing patterns body]

-- | Create a case expression to deconstruct a class dictionary
mkCaseOfDict :: (MonadIO m, Supplies m SF.VarID) =>
                SourcePos -> Class -> HMType -> Constraint -> [ClassMethod]
             -> TIExp -> m (TIExp -> TIExp, [SF.Var], [SF.Var])
mkCaseOfDict pos cls ty constraint methods dict 
  | clsIsAbstract cls =
      internalError "mkCaseOfDict: Cannot deconstruct an abstract class"

  | otherwise = do
      let dict_con = clsSFDictCon cls
          ty_arg = mkType ty
          dict_type = DelayedType $ do t <- case ty_arg of DelayedType m -> m
                                       return $ SF.varApp dict_con [t]
          superclass_types = map mkPredicate constraint
          method_types = map (mkClassMethodBinder ty_arg) methods

      -- Create variables to bind to each field
      dict_vars <- forM superclass_types $ \_ -> SF.newAnonymousVar SF.ObjectLevel
      method_vars <- forM method_types $ \_ -> SF.newAnonymousVar SF.ObjectLevel

      let dict_patterns = zipWith TIVarP dict_vars superclass_types
      let method_patterns = zipWith TIVarP method_vars method_types
      let field_patterns = dict_patterns ++ method_patterns

      let decon = (TIDeConInst dict_con [ty_arg] [])
          mk_expr body =
            mkCaseTE pos dict []
            [TIAlt decon (Just dict_type) field_patterns body]

      return (mk_expr, dict_vars, method_vars)

-- | Create the type of an instantiated class method
mkClassMethodBinder :: TIType -> ClassMethod -> TIType
mkClassMethodBinder ty_arg cm = 
  case cm
  of ClassMethod scm -> mkTyScheme scm
     AbstractClassMethod ty -> DelayedType $ do
       -- Instantiate by applying the method's type to the
       -- class parameter's type
       sf_ty_arg <- case ty_arg of DelayedType t -> t
       return $ SF.AppT ty sf_ty_arg

mkDictE :: SourcePos -> Class -> TIType -> [TIExp] -> SF.Var -> [TIExp]
        -> TIExp
mkDictE pos cls inst_type scs tyob_con methods =
  -- Apply the dictionary constructor to the instance type and all arguments
  -- Dictionary type must not have size parameters
  mkConE pos TIBoxed (clsSFDictCon cls) [inst_type] [] [] (Just tyob_con)
  (scs ++ methods)

-- | Create a mixed System F and type-inferred expression. 
--   After the given types and expressions are converted to System F,
--   they will be applied to the function to create an expression.
mkMkExpE :: SourcePos -> TIRepr -> ([SF.Type] -> [SF.ExpSF] -> SF.ExpSF)
         -> [TIType] -> [TIExp] -> TIExp
mkMkExpE pos repr f ty_args args =
  MkExpTE (tiInfo pos repr) f ty_args args

mkAnnotation :: FunctionAnn -> SF.DefAnn
mkAnnotation (FunctionAnn _ inline) =
  let insert_inline_ann d = d {SF.defAnnInlineRequest = if inline
                                                        then SF.InlAggressively
                                                        else SF.InlConservatively}
  in insert_inline_ann SF.defaultDefAnn

{-
-- | Create an abstract class instance from a variable
varAbstractClassInstance :: SF.Var -> ClassInstance
varAbstractClassInstance v = AbstractClassInstance instantiate
  where
    instantiate ty_args args =
      let fun_repr = polyThingRepr TIBoxed ty_args args
          fun = mkVarE noSourcePos fun_repr v
      in mkPolyCallE noSourcePos TIBoxed fun ty_args args
-}

  