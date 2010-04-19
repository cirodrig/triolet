
{-# LANGUAGE ScopedTypeVariables, TypeFamilies #-}
module Pyon.SystemF.Typecheck
       (Worker(..), typeCheckModule, typeCheckModulePython)
where

import Control.Applicative(Const(..))
import Control.Exception
import Control.Monad
import Data.Maybe

import Gluon.Common.Label
import Gluon.Common.SourcePos
import qualified Gluon.Core as Gluon
import Gluon.Core.Rename
import Gluon.Core(WRExp, asWhnf, fromWhnf)
import qualified Gluon.Core.Builtins.Effect as Gluon.Builtins.Effect
import qualified Gluon.Eval.Error as Gluon
import qualified Gluon.Eval.Eval as Gluon
import Gluon.Eval.Environment
import qualified Gluon.Eval.Typecheck as Gluon
import Gluon.Eval.Typecheck(TrivialStructure, tcAssertEqual)

import PythonInterface.Python
import Pyon.Globals
import Pyon.SystemF.Print
import Pyon.SystemF.Builtins
import Pyon.SystemF.Syntax

data Worker a =
  Worker
  { doType :: !(WRExp -> PureTC (TypeOf a a))
  , doExp  :: !(SFExp a -> WRExp -> PureTC (SFRecExp a))
  , doFun  :: !([TyPat a] -> [Pat a] -> TypeOf a a -> SFRecExp a -> PureTC (Fun a))
  }

data instance SFExpOf TrivialStructure s = TrivialSFExp
data instance FunOf TrivialStructure s = TrivialFun

noWork :: Worker TrivialStructure
noWork = Worker { doType = \_ -> return Gluon.TrivialExp
                , doExp = \_ _ -> return TrivialSFExp
                , doFun = \_ _ _ _ -> return TrivialFun
                }

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

funType :: RFun -> RType 
funType (Fun { funTyParams = ty_params
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
      
assumePat :: Worker a -> RPat -> (Pat a -> PureTC b) -> PureTC b
assumePat worker p k = 
  case p
  of WildP p_ty -> do ty' <- doType worker =<< Gluon.evalFully' p_ty
                      k (WildP ty')
     VarP v p_ty -> do ty' <- doType worker =<< Gluon.evalFully' p_ty
                       assumePure v p_ty $ k (VarP v ty')
     TupleP pats -> withMany (assumePat worker) pats $ \pats' -> k (TupleP pats')
     
assumeTyPat :: Worker a -> RTyPat -> (TyPat a -> PureTC b) -> PureTC b
assumeTyPat worker (TyPat v t) k = do 
  ty' <- doType worker =<< Gluon.evalFully' t
  assumePure v t $ k (TyPat v ty')

-- Assume a function definition.  Do not check the function definition's body.
assumeDef :: RDef -> PureTC a -> PureTC a
assumeDef (Def v fun) = assumePure v (funType fun)

typeInferExp :: Worker a -> RExp -> PureTC (WRExp, SFRecExp a)
typeInferExp worker expression = do
  (e_type, new_exp) <-
    case expression
    of VarE {expInfo = inf, expVar = v} ->
         typeInferVarE inf v
       ConE {expInfo = inf, expCon = c} -> do
         ty <- Gluon.evalFully =<< Gluon.getConstructorType c
         return (ty, ConE inf c)
       LitE {expInfo = inf, expLit = l, expType = t} ->
         checkLiteralType worker inf l t
       UndefinedE {expInfo = inf, expType = t} -> do
         -- Evaluate the type; any type is acceptable
         t' <- Gluon.evalFully' t
         val <- doType worker t'
         return (t', UndefinedE inf val)
       TupleE {expInfo = inf, expFields = fs} ->
         typeInferTupleE worker inf fs
       TyAppE {expInfo = inf, expOper = op, expTyArg = arg} ->
         typeInferTyAppE worker inf op arg
       CallE {expInfo = inf, expOper = op, expArgs = args} ->
         typeInferCallE worker inf op args
       IfE {expInfo = inf, expCond = cond, expTrueCase = tr, expFalseCase = fa} ->
         typeInferIfE worker inf cond tr fa
       FunE {expInfo = inf, expFun = f} -> do
         (fun_type, fun_val) <- typeInferFun worker f
         return (fun_type, FunE inf fun_val)
       LetE {expInfo = inf, expBinder = pat, expValue = e, expBody = body} ->
         typeInferLetE worker inf pat e body
       LetrecE {expInfo = inf, expDefs = defs, expBody = body} ->
         typeInferLetrecE worker inf defs body
       CaseE {expInfo = inf, expScrutinee = scr, expAlternatives = alts} ->
         typeInferCaseE worker inf scr alts
  new_val <- doExp worker new_exp e_type
  return (e_type, new_val)
         
-- To infer a variable's type, just look it up in the environment
typeInferVarE :: ExpInfo -> Var -> PureTC (WRExp, SFExp a)
typeInferVarE inf var = do
  lookup_type <- getType' noSourcePos var
  ty <- liftEvaluation $ Gluon.evalFully' lookup_type
  return (ty, VarE inf var)

-- Use the type that was attached to the literal value, but also verify that
-- it's a valid type
checkLiteralType :: Worker a -> ExpInfo -> Lit -> RType 
                 -> PureTC (WRExp, SFExp a)
checkLiteralType worker inf l t = do
  t' <- liftEvaluation $ Gluon.evalFully' t
  t_val <- doType worker t'
  if isValidLiteralType t' l
    then return (t', LitE inf l t_val)
    else throwError $ OtherErr $ "Not a valid literal type " ++ show (Gluon.pprExp (fromWhnf t')) ++ "; " ++ show (pprLit l)

isValidLiteralType ty lit =
  -- Get the type constructor
  case Gluon.unpackWhnfAppE ty
  of Just (con, args) ->
       -- Based on the literal, check whether the type constructor is 
       -- acceptable
       case lit
       of IntL _ -> con `Gluon.isBuiltin` Gluon.the_Int
          FloatL _ -> con `Gluon.isBuiltin` Gluon.the_Float
          BoolL _ -> con `isPyonBuiltin` the_bool
          NoneL -> con `isPyonBuiltin` the_NoneType
     Nothing ->
       -- Literals cannot have other types 
       False
                                     
typeInferTupleE :: Worker a -> ExpInfo -> [RExp] -> PureTC (WRExp, SFExp a)
typeInferTupleE worker inf fs = do
  -- Infer types of all fields
  (f_types, f_vals) <- mapAndUnzipM (typeInferExp worker) fs

  -- Create a tuple type
  let size = length f_types
  case getPyonTupleType size
    of Nothing -> error "Unsupported tuple size"
       Just c -> let new_tuple = TupleE inf f_vals
                     ty = Gluon.mkInternalWhnfAppE c $ map fromWhnf f_types
                 in return (ty, new_tuple)

typeInferTyAppE :: Worker a -> ExpInfo -> RExp -> RType
                -> PureTC (WRExp, SFExp a)
typeInferTyAppE worker inf op arg = do
  (op_type, op_val) <- typeInferExp worker op
  arg_type <- Gluon.typeInferExp arg
  arg_val <- doType worker =<< Gluon.evalFully' arg

  -- Apply operator to argument
  case fromWhnf op_type of
    Gluon.FunE {Gluon.expMParam = param, Gluon.expRange = range} -> do
      -- Operand type must match
      tcAssertEqual (getSourcePos inf)
         (verbatim $ Gluon.binder'Type param) 
         (verbatim $ fromWhnf arg_type)
      
      -- Result type is the range, after substituting operand in argument
      result <- liftEvaluation $
                Gluon.evalFully $
                assignBinder' param arg $
                verbatim range
      return (result, TyAppE inf op_val arg_val)
      
    _ -> throwError $ Gluon.NonFunctionApplicationErr (getSourcePos inf) (fromWhnf op_type)

typeInferCallE :: Worker a -> ExpInfo -> RExp -> [RExp] 
               -> PureTC (WRExp, SFExp a)
typeInferCallE worker inf op args = do
  -- Infer types of parameters
  (op_type, op_val) <- typeInferExp worker op
  (arg_types, arg_vals) <- mapAndUnzipM (typeInferExp worker) args

  -- Compute result type
  result_type <- computeAppliedType 
                 (getSourcePos inf)
                 (verbatim $ fromWhnf op_type) 
                 (map fromWhnf arg_types)
  
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
  
  return (result_type, CallE inf op_val arg_vals)

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
          tcAssertEqual pos dom (verbatim arg_t)
          
          -- continue with range
          apply rng arg_ts
        
        Gluon.FunE {} -> throwError $ OtherErr "Unexpected dependent type"
          
        _ -> do op_type' <- Gluon.evalFully op_type
                throwError $ Gluon.NonFunctionApplicationErr pos (fromWhnf op_type')

    apply op_type [] = Gluon.evalFully op_type

typeInferIfE :: Worker a -> ExpInfo -> RExp -> RExp -> RExp
             -> PureTC (WRExp, SFExp a)
typeInferIfE worker inf cond if_true if_false = do
  -- Condition must be a bool
  (cond_t, cond_val) <- typeInferExp worker cond
  tcAssertEqual (getSourcePos inf) (verbatim boolType) (verbatim $ fromWhnf cond_t)
  
  -- True and false paths must be equal
  (if_true_t, if_true_val) <- typeInferExp worker if_true
  (if_false_t, if_false_val) <- typeInferExp worker if_false
  tcAssertEqual noSourcePos (verbatim $ fromWhnf if_true_t) (verbatim $ fromWhnf if_false_t)

  return (if_true_t, IfE inf cond_val if_true_val if_false_val)

typeInferFun :: Worker a -> RFun -> PureTC (WRExp, Fun a)
typeInferFun worker fun@(Fun { funTyParams = ty_params
                             , funParams = params
                             , funReturnType = return_type
                             , funBody = body}) =
  assumeTyParams $ \new_ty_params -> assumeParams $ \new_params -> do
    (body_type, body_val) <- typeInferExp worker body
    return_type_val <- doType worker =<< Gluon.evalFully' return_type
    
    -- Return type must match inferred type
    tcAssertEqual noSourcePos (verbatim $ fromWhnf body_type) 
                              (verbatim return_type)
    
    -- Create the function's type
    ty <- Gluon.evalFully' $ funType fun
    
    new_fun <-
      doFun worker new_ty_params new_params return_type_val body_val
    return (ty, new_fun)
  where
    assumeTyParams = withMany (assumeTyPat worker) ty_params
    assumeParams = withMany (assumePat worker) params

typeInferLetE :: Worker a -> ExpInfo -> RPat -> RExp -> RExp
              -> PureTC (WRExp, SFExp a)
typeInferLetE worker inf pat expression body = do
  (e_type, e_val) <- typeInferExp worker expression
  
  -- Expression type must match pattern type
  tcAssertEqual noSourcePos (verbatim $ fromWhnf e_type) (verbatim $ patType pat)

  -- Assume the pattern while inferring the body; result is the body's type
  assumePat worker pat $ \pat' -> do
    (body_type, body_val) <- typeInferExp worker body
    return (body_type, LetE inf pat' e_val body_val)

typeInferLetrecE :: Worker a -> ExpInfo -> [RDef] -> RExp
                 -> PureTC (WRExp, SFExp a)
typeInferLetrecE worker inf defs body =
  typeCheckDefGroup worker defs $ \defs' -> do
    (body_type, body_val) <- typeInferExp worker body
    return (body_type, LetrecE inf defs' body_val)

typeInferCaseE :: Worker a -> ExpInfo -> RExp -> [Alt Rec]
               -> PureTC (WRExp, SFExp a)
typeInferCaseE worker inf scr alts = do
  let pos = getSourcePos inf

  -- Get the scrutinee's type
  (scr_type, scr_val) <- typeInferExp worker scr
  
  when (null alts) $
    throwError $ OtherErr "Empty case statement"

  -- Match against each alternative
  (alt_types, alt_vals) <-
    mapAndUnzipM (typeCheckAlternative worker pos (fromWhnf scr_type)) alts
    
  -- All alternatives must match
  let alt_subst_types = map (verbatim . fromWhnf) alt_types
  zipWithM (tcAssertEqual pos) alt_subst_types (tail alt_subst_types)

  return (head alt_types, CaseE inf scr_val alt_vals)

typeCheckAlternative :: Worker a -> SourcePos -> Gluon.RExp -> Alt Rec
                     -> PureTC (WRExp, Alt a)
typeCheckAlternative worker pos scr_type (Alt { altConstructor = con
                                              , altTyArgs = types
                                              , altParams = fields
                                              , altBody = body}) = do
  -- Process arguments
  arg_vals <- mapM (doType worker <=< Gluon.evalFully') types
  
  -- Apply constructor to type arguments
  con_ty <- Gluon.getConstructorType con
  fo_type <- computeTypeApplicationType pos con_ty types
  
  -- Match the resulting type against the function type
  -- field1 -> field2 -> ... -> scr_type
  (body_ty, body_val) <-
    bindParamTypes (fromWhnf fo_type) fields $
    typeInferExp worker body

  return (body_ty, Alt con arg_vals fields body_val)
  where
    -- Bind parameter variables to the constructor's parameter types
    bindParamTypes con_type fields k = go con_type fields
      where
        go match_type (field:fields) =
          case match_type
          of Gluon.FunE { Gluon.expMParam = Gluon.Binder' Nothing dom ()
                        , Gluon.expRange = rng} ->
               assumePure field dom $ go rng fields
             Gluon.FunE {} ->
               throwError $ OtherErr "Unexpected dependent type"
             _ -> throwError $ Gluon.NonFunctionApplicationErr pos match_type
        go result_type [] = do
          -- This must match the scrutinee type
          tcAssertEqual pos (verbatim scr_type) (verbatim result_type)
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
          tcAssertEqual pos dom (verbatim $ fromWhnf arg_type)
          
          -- update the range type
          let binder' = Gluon.mapBinder' id substFully binder
              rng' = assignBinder' binder' arg rng
          
          -- Continue with range
          apply rng' args
          
        _ -> throwError $ NonFunctionApplicationErr pos (substFullyUnder $ fromWhnf op_type')
        
    apply op_type [] = Gluon.evalFully op_type

typeCheckDefGroup :: Worker a -> [RDef] -> ([Def a] -> PureTC b)
                  -> PureTC b
typeCheckDefGroup worker defs k =
  -- Assume all defined function types
  catEndo (map assumeDef defs) $ do
    -- Check all defined function bodies
    xs <- mapM typeCheckDef defs
    
    -- Run the continuation in this environment
    k xs
  where
    -- To typecheck a definition, check the function it contains
    typeCheckDef (Def v fun) = do
      (_, fun_val) <- typeInferFun worker fun
      return $ Def v fun_val

typeCheckModule worker (Module defs exports) =
  withTheVarIdentSupply $ \varIDs ->
    runPureTCIO varIDs $ do
      defs' <- typeCheckDefGroups defs
      return $ Module defs' exports
  where
    typeCheckDefGroups (defs:defss) = 
      typeCheckDefGroup worker defs $ \defs' -> 
      liftM (defs':) $ typeCheckDefGroups defss
      
    typeCheckDefGroups [] = return []
    
typeCheckModulePython mod = do
  result <- typeCheckModule noWork mod
  case result of
    Left errs -> do mapM_ (putStrLn . showTypeCheckError) errs
                    throwPythonExc pyRuntimeError "Type checking failed"
    Right _ -> return ()
