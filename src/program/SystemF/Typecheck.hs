
{-# LANGUAGE ScopedTypeVariables, TypeFamilies, EmptyDataDecls,
             FlexibleInstances, DeriveDataTypeable #-}
module SystemF.Typecheck
       (Typed, TypedRec, TypeAnn(..),
        SFExpOf(TypedSFExp), Gluon.ExpOf(TypedSFType), FunOf(TypedSFFun),
        AltOf(TypedSFAlt),
        TRType, TRExp, TRAlt, TRFun,
        mapTypeAnn, traverseTypeAnn,
        functionType,
        typeCheckModule)
where

import Control.Applicative(Const(..))
import Control.Exception
import Control.Monad
import Data.Typeable(Typeable)
import Data.Maybe
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Gluon.Common.Label
import Gluon.Common.SourcePos
import qualified Gluon.Core as Gluon
import Gluon.Core.Rename
import Gluon.Core(Level(..), WRExp, asWhnf, fromWhnf)
import qualified Gluon.Core.Builtins.Effect as Gluon.Builtins.Effect
import qualified Gluon.Eval.Error as Gluon
import qualified Gluon.Eval.Eval as Gluon
import Gluon.Eval.Environment
import qualified Gluon.Eval.Typecheck as Gluon
import Gluon.Eval.Typecheck(TrivialStructure, tcAssertEqual)

import Globals
import SystemF.Print
import SystemF.Builtins
import SystemF.Syntax

-- | Set to True for debugging
printTypeAssertions :: Bool
printTypeAssertions = False

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
                    
{-
data Worker a =
  Worker
  { doType :: !(WRExp -> PureTC (TypeOf a a))
  , doExp  :: !(SFExp a -> WRExp -> PureTC (SFRecExp a))
  , doFun  :: !(SourcePos -> [TyPat a] -> [Pat a] -> TypeOf a a -> SFRecExp a -> WRExp -> PureTC (Fun a))
  }

data instance SFExpOf TrivialStructure s = TrivialSFExp
data instance FunOf TrivialStructure s = TrivialFun

noWork :: Worker TrivialStructure
noWork = Worker { doType = \_ -> return Gluon.TrivialExp
                , doExp = \_ _ -> return TrivialSFExp
                , doFun = \_ _ _ _ _ _ -> return TrivialFun
                }
-}

data TypeAnn t a =
  TypeAnn { typeAnnotation :: WRExp
          , typeAnnValue :: t a
          }

mapTypeAnn :: (t a -> s b) -> TypeAnn t a -> TypeAnn s b
mapTypeAnn f (TypeAnn t x) = TypeAnn t (f x)

traverseTypeAnn :: Monad m =>
                   (t a -> m (s b)) -> TypeAnn t a -> m (TypeAnn s b)
traverseTypeAnn f (TypeAnn t x) = do
  y <- f x
  return $ TypeAnn t y

class HasType a where
  getTypeAnn :: a -> WRExp

data Typed a deriving(Typeable)

instance Gluon.Structure a => Gluon.Structure (Typed a)

newtype instance Gluon.ExpOf (Typed s) (Typed s') =
  TypedSFType (TypeAnn (TypeOf s) s')
newtype instance SFExpOf (Typed s) s' = TypedSFExp (TypeAnn (SFExpOf s) s')
newtype instance AltOf (Typed s) s' = TypedSFAlt (TypeAnn (AltOf s) s')
newtype instance FunOf (Typed s) s' = TypedSFFun (TypeAnn (FunOf s) s')

type TypedRec = Typed Rec
type TRType = RecType TypedRec
type TRExp = SFRecExp TypedRec
type TRAlt = RecAlt TypedRec
type TRFun = Fun TypedRec

instance HasType (SFExpOf TypedRec TypedRec) where
  getTypeAnn (TypedSFExp x) = typeAnnotation x

instance HasType (AltOf TypedRec TypedRec) where
  getTypeAnn (TypedSFAlt x) = typeAnnotation x

instance HasType (FunOf TypedRec TypedRec) where
  getTypeAnn (TypedSFFun x) = typeAnnotation x

{-
annotateTypes :: Worker (Typed Rec)
annotateTypes =
  Worker { doType = \t -> return (TypedSFType $ fromWhnf t)
         , doExp = \e t -> return (TypedSFExp $ TypeAnn t e)
         , doFun = \pos ty_params params rt body ty -> 
            return (TypedSFFun $ TypeAnn ty $ Fun (Gluon.mkSynInfo pos ObjectLevel) ty_params params rt body)
         }
-}

-- Endomorphism concatenation
catEndo xs k = foldr ($) k xs

withMany :: (a -> (b -> c) -> c) -> [a] -> ([b] -> c) -> c
withMany f xs k = go xs k
  where
    go (x:xs) k = f x $ \y -> go xs $ \ys -> k (y:ys)
    go []     k = k []

makeActionType return_type = return_type

boolType = Gluon.mkInternalConE $ pyonBuiltin the_bool

tyPatType :: RTyPat -> RType
tyPatType (TyPat _ t) = t

patType :: RPat -> RType
patType (WildP t)  = t
patType (VarP _ t) = t
patType (TupleP ps) = let size = length ps
                          con = case getPyonTupleType (length ps)
                                of Just n -> n
                                   Nothing -> error "Unsupported tuple size"
                          field_types = map patType ps
                      in Gluon.mkInternalConAppE con field_types

functionType :: RFun -> RType 
functionType (Fun { funTyParams = ty_params
                  , funParams = params
                  , funReturnType = ret 
                  }) =
  -- Create a dependent type for each type parameter
  catEndo (map makeTyFun ty_params) $
  -- Create an arrow type for each value parameter
  catEndo (map makeParamArrow params) $
  -- Create the return type
  ret
  where
    makeParamArrow p t = Gluon.mkInternalArrowE False (patType p) t
    makeTyFun (TyPat v t) t2 = Gluon.mkInternalFunE False v t t2
      
assumePat :: RPat -> (Pat TypedRec -> PureTC b) -> PureTC b
assumePat p k = 
  case p
  of WildP p_ty -> do ty' <- evalType p_ty
                      k (WildP ty')
     VarP v p_ty -> do ty' <- evalType p_ty
                       assumePure v p_ty $ k (VarP v ty')
     TupleP pats -> withMany assumePat pats $ \pats' -> k (TupleP pats')
     
assumeTyPat :: RTyPat -> (TyPat TypedRec -> PureTC b) -> PureTC b
assumeTyPat (TyPat v t) k = do 
  ty' <- evalType t
  assumePure v t $ k (TyPat v ty')

-- Assume a function definition.  Do not check the function definition's body.
assumeDef :: RDef -> PureTC a -> PureTC a
assumeDef (Def v fun) = assumePure v (functionType fun)

-- | Infer a type's kind
evalType :: RType -> PureTC TRType
evalType t = do
  k <- Gluon.typeInferExp t
  t' <- Gluon.evalFully' t
  return $ TypedSFType $ TypeAnn k (fromWhnf t')

typeInferExp :: RExp -> PureTC TRExp
typeInferExp expression =
    case expression
    of VarE {expInfo = inf, expVar = v} ->
         typeInferVarE inf v
       ConE {expInfo = inf, expCon = c} -> do
         ty <- Gluon.evalFully =<< Gluon.getConstructorType c
         return $ TypedSFExp $ TypeAnn ty (ConE inf c)
       LitE {expInfo = inf, expLit = l, expType = t} ->
         checkLiteralType inf l t
       TyAppE {expInfo = inf, expOper = op, expTyArg = arg} ->
         typeInferTyAppE inf op arg
       CallE {expInfo = inf, expOper = op, expArgs = args} ->
         typeInferCallE inf op args
       FunE {expInfo = inf, expFun = f} -> do
         ti_fun <- typeInferFun f
         return $ TypedSFExp $ TypeAnn (getTypeAnn ti_fun) (FunE inf ti_fun)
       LetE {expInfo = inf, expBinder = pat, expValue = e, expBody = body} ->
         typeInferLetE inf pat e body
       LetrecE {expInfo = inf, expDefs = defs, expBody = body} ->
         typeInferLetrecE inf defs body
       CaseE {expInfo = inf, expScrutinee = scr, expAlternatives = alts} ->
         typeInferCaseE inf scr alts
         
-- To infer a variable's type, just look it up in the environment
typeInferVarE :: ExpInfo -> Var -> PureTC TRExp
typeInferVarE inf var = do
  lookup_type <- getType' noSourcePos var
  ty <- liftEvaluation $ Gluon.evalFully' lookup_type
  return $ TypedSFExp $ TypeAnn ty (VarE inf var)

-- Use the type that was attached to the literal value, but also verify that
-- it's a valid type
checkLiteralType :: ExpInfo -> Lit -> RType
                 -> PureTC TRExp
checkLiteralType inf l t = do
  t' <- Gluon.evalFully' t
  k <- Gluon.typeInferExp t
  let t'' = TypedSFType $ TypeAnn k (fromWhnf t')
  
  if isValidLiteralType t' l
    then return $ TypedSFExp $ TypeAnn t' (LitE inf l t'')
    else throwError $ OtherErr "Not a valid literal type"

isValidLiteralType ty lit =
  -- Get the type constructor
  case Gluon.unpackWhnfAppE ty
  of Just (con, args) ->
       -- Based on the literal, check whether the type constructor is 
       -- acceptable
       case lit
       of IntL _ -> con `isPyonBuiltin` the_int
          FloatL _ -> con `isPyonBuiltin` the_float
          BoolL _ -> con `isPyonBuiltin` the_bool
          NoneL -> con `isPyonBuiltin` the_NoneType
     Nothing ->
       -- Literals cannot have other types 
       False
                                     
typeInferTyAppE :: ExpInfo -> RExp -> RType -> PureTC TRExp
typeInferTyAppE inf op arg = do
  ti_op <- typeInferExp op
  arg_type <- Gluon.typeInferExp arg
  arg_val <- evalType arg

  -- Apply operator to argument
  case fromWhnf $ getTypeAnn ti_op of
    Gluon.FunE {Gluon.expMParam = param, Gluon.expRange = range} -> do
      -- Operand type must match
      assertEqualTypesV (getSourcePos inf)
         (Gluon.binder'Type param) 
         (fromWhnf arg_type)

      -- Result type is the range, after substituting operand in argument
      result <- liftEvaluation $
                Gluon.evalFully $
                assignBinder' param arg $
                verbatim range
      return $ TypedSFExp $ TypeAnn result (TyAppE inf ti_op arg_val)
      
    _ -> throwError $ Gluon.NonFunctionApplicationErr (getSourcePos inf) (fromWhnf $ getTypeAnn ti_op)

typeInferCallE :: ExpInfo -> RExp -> [RExp] -> PureTC TRExp
typeInferCallE inf op args = do
  -- Infer types of parameters
  ti_op <- typeInferExp op
  ti_args <- mapM typeInferExp args

  -- Compute result type
  result_type <- computeAppliedType 
                 (getSourcePos inf)
                 (verbatim $ fromWhnf $ getTypeAnn ti_op) 
                 (map (fromWhnf . getTypeAnn) ti_args)
  
  -- The result type must be in the 'Action' or 'Stream' monads.
  -- If 'Action', strip off the constructor.
  -- Ignore the effect type.
  {-
  ty <- case Gluon.unpackWhnfAppE result_type
        of Just (con, [_, arg]) 
             | con `isPyonBuiltin` the_Action ->
                 return $ asWhnf arg
             | con `isPyonBuiltin` the_Stream ->
                 return result_type
           _ -> throwError $ OtherErr "Incorrect function return type, \
                                      \or wrong number of arguments"
  -}
  let new_exp = CallE inf ti_op ti_args
  return $ TypedSFExp $ TypeAnn result_type new_exp

-- | Given a function type and a list of argument types, compute the result of
-- applying the function to the arguments.
computeAppliedType :: SourcePos 
                   -> Gluon.RecExp SubstRec 
                   -> [RType] 
                   -> PureTC WRExp
computeAppliedType pos op_type arg_types = apply op_type arg_types
  where
    apply op_type (arg_t:arg_ts) = do
      -- Operator must be a function type
      op_type' <- Gluon.evalHead op_type
      case fromWhnf op_type' of
        Gluon.FunE { Gluon.expMParam = Gluon.Binder' Nothing dom ()
                   , Gluon.expRange = rng} -> do
          -- parameter type must match argument type
          assertEqualTypes pos dom (verbatim arg_t)
          
          -- continue with range
          apply rng arg_ts
        
        Gluon.FunE {} -> throwError $ OtherErr "Unexpected dependent type"
          
        _ -> throwError $ Gluon.NonFunctionApplicationErr pos (Gluon.substFully op_type)

    apply op_type [] = Gluon.evalFully op_type

typeInferFun :: RFun -> PureTC TRFun
typeInferFun fun@(Fun { funInfo = info
                      , funTyParams = ty_params
                      , funParams = params
                      , funReturnType = return_type
                      , funBody = body}) =
  assumeTyParams $ \new_ty_params -> assumeParams $ \new_params -> do
    ti_body <- typeInferExp body
    return_type_val <- evalType return_type
    
    -- Return type must match inferred type
    assertEqualTypesV noSourcePos (fromWhnf $ getTypeAnn ti_body) return_type
    
    -- Create the function's type
    ty <- Gluon.evalFully' $ functionType fun
    
    let new_fun =
          Fun { funInfo = info
              , funTyParams = new_ty_params
              , funParams = new_params
              , funReturnType = return_type_val
              , funBody = ti_body
              }
    return $ TypedSFFun $ TypeAnn ty new_fun
  where
    assumeTyParams = withMany assumeTyPat ty_params
    assumeParams = withMany assumePat params

typeInferLetE :: ExpInfo -> RPat -> RExp -> RExp -> PureTC TRExp
typeInferLetE inf pat expression body = do
  ti_exp <- typeInferExp expression
  
  -- Expression type must match pattern type
  assertEqualTypesV noSourcePos (fromWhnf $ getTypeAnn ti_exp) (patType pat)

  -- Assume the pattern while inferring the body; result is the body's type
  assumePat pat $ \pat' -> do
    ti_body <- typeInferExp body
    return $ TypedSFExp $ TypeAnn (getTypeAnn ti_body) (LetE inf pat' ti_exp ti_body)

typeInferLetrecE :: ExpInfo -> [RDef] -> RExp -> PureTC TRExp
typeInferLetrecE inf defs body =
  typeCheckDefGroup defs $ \defs' -> do
    ti_body <- typeInferExp body
    return $ TypedSFExp $ TypeAnn (getTypeAnn ti_body) (LetrecE inf defs' ti_body)

typeInferCaseE :: ExpInfo -> RExp -> [Alt Rec] -> PureTC TRExp
typeInferCaseE inf scr alts = do
  let pos = getSourcePos inf

  -- Get the scrutinee's type
  ti_scr <- typeInferExp scr
  let scr_type = fromWhnf $ getTypeAnn ti_scr
  
  when (null alts) $
    throwError $ OtherErr "Empty case statement"

  -- Match against each alternative
  ti_alts <- mapM (typeCheckAlternative pos scr_type) alts
    
  -- All alternatives must match
  let alt_subst_types = map (verbatim . fromWhnf . getTypeAnn) ti_alts
  zipWithM (assertEqualTypes pos) alt_subst_types (tail alt_subst_types)

  -- The expression's type is the type of an alternative
  let result_type = getTypeAnn $ head ti_alts
  return $! TypedSFExp $! TypeAnn result_type $ CaseE inf ti_scr ti_alts

typeCheckAlternative :: SourcePos -> Gluon.RExp -> Alt Rec -> PureTC TRAlt
typeCheckAlternative pos scr_type (Alt { altConstructor = con
                                       , altTyArgs = types
                                       , altParams = fields
                                       , altBody = body}) = do
  -- Process arguments
  arg_vals <- mapM evalType types
  
  -- Apply constructor to type arguments
  con_ty <- Gluon.getConstructorType con
  fo_type <- computeTypeApplicationType pos con_ty types
  
  -- Match the resulting type against the function type
  -- field1 -> field2 -> ... -> scr_type
  ti_body <- bindParamTypes (fromWhnf fo_type) fields $ typeInferExp body

  -- Construct new field expresions
  fields' <- forM fields $ \(Gluon.Binder v ty ()) -> do
    ty' <- evalType ty
    return $ Gluon.Binder v ty' ()

  return $ TypedSFAlt $ TypeAnn (getTypeAnn ti_body) $ Alt con arg_vals fields' ti_body
  where
    -- Bind parameter variables to the constructor's parameter types
    bindParamTypes con_type fields k = go con_type fields
      where
        go match_type (Gluon.Binder field_var field_type () : fields) =
          case match_type
          of Gluon.FunE { Gluon.expMParam = Gluon.Binder' Nothing dom ()
                        , Gluon.expRange = rng} -> do
               assumePure field_var dom $ go rng fields
             Gluon.FunE {} ->
               throwError $ OtherErr "Unexpected dependent type"
             _ -> throwError $ Gluon.NonFunctionApplicationErr pos match_type
        go result_type [] = do
          -- This must match the scrutinee type
          assertEqualTypesV pos scr_type result_type
          k

-- | Determine the type of the result of an application.
-- The operator's type (not the operator itself) is taken as a parameter,
-- along with the argument values.
--
-- The worker is also used on to each parameter
computeTypeApplicationType
  :: SourcePos 
  -> Gluon.RecExp SubstRec      -- ^ Type of the operator to apply
  -> [RType]                    -- ^ Parameters to apply
  -> PureTC WRExp               -- ^ Compute the result type
computeTypeApplicationType pos op_type args = apply op_type args
  where
    apply op_type (arg:args) = do
      -- Operator must be a function type
      op_type' <- Gluon.evalHead op_type
      case fromWhnf op_type' of
        Gluon.FunE { Gluon.expMParam = binder@(Gluon.Binder' _ dom ())
                   , Gluon.expRange = rng} -> do
          -- Get the argument's type
          arg_type <- Gluon.typeInferExp arg
          
          -- parameter type must match argument type
          assertEqualTypes pos dom (verbatim $ fromWhnf arg_type)
          
          -- update the range type
          let binder' = Gluon.mapBinder' id substFully binder
              rng' = assignBinder' binder' arg rng
          
          -- Continue with range
          apply rng' args
          
        _ -> throwError $ NonFunctionApplicationErr pos (substFullyUnder $ fromWhnf op_type')
        
    apply op_type [] = Gluon.evalFully op_type

typeCheckDefGroup :: [RDef] -> ([Def TypedRec] -> PureTC b) -> PureTC b
typeCheckDefGroup defs k =
  -- Assume all defined function types
  catEndo (map assumeDef defs) $ do
    -- Check all defined function bodies
    xs <- mapM typeCheckDef defs
    
    -- Run the continuation in this environment
    k xs
  where
    -- To typecheck a definition, check the function it contains
    typeCheckDef (Def v fun) = do
      fun_val <- typeInferFun fun
      return $ Def v fun_val

typeCheckModule (Module defs exports) =
  withTheVarIdentSupply $ \varIDs ->
    runPureTCIO varIDs $ do
      defs' <- typeCheckDefGroups defs
      return $ Module defs' exports
  where
    typeCheckDefGroups (defs:defss) = 
      typeCheckDefGroup defs $ \defs' -> 
      liftM (defs':) $ typeCheckDefGroups defss
      
    typeCheckDefGroups [] = return []
