
module Pyon.SystemF.Typecheck
       (typeCheckModule, typeCheckModulePython)
where

import Control.Exception
import Data.Maybe
  
import Gluon.Common.Label
import Gluon.Common.SourcePos
import qualified Gluon.Core as Gluon
import Gluon.Core.Rename
import Gluon.Core(Whnf(Whnf, whnfExp), CWhnf)
import qualified Gluon.Eval.Error as Gluon
import qualified Gluon.Eval.Eval as Gluon
import Gluon.Eval.Environment
import qualified Gluon.Eval.Typecheck as Gluon
import Gluon.Eval.Typecheck(tcAssertEqual)

import PythonInterface.Python
import Pyon.Globals
import Pyon.SystemF.Print
import Pyon.SystemF.Builtins
import Pyon.SystemF.Syntax

-- Endomorphism concatenation
catEndo xs k = foldr ($) k xs

classDictCon EqClass = pyonBuiltin the_EqDict
classDictCon OrdClass = pyonBuiltin the_OrdDict
classDictCon TraversableClass = pyonBuiltin the_TraversableDict

classMethodType cls clsType index =
  case cls
  of EqClass ->
       case index
       of 0 -> binaryFunctionType
          1 -> binaryFunctionType
     OrdClass ->
       case index
       of 0 -> binaryFunctionType
          1 -> binaryFunctionType
          2 -> binaryFunctionType
          3 -> binaryFunctionType
     TraversableClass ->
       case index
       of 0 -> traverseType
  where
    traverseType = do
      a <- newTemporary Gluon.TypeLevel Nothing
      let a_exp = Gluon.mkInternalVarE a
          cls_exp = Gluon.mkInternalAppE clsType [a_exp]
          iter_exp = Gluon.mkInternalConAppE (pyonBuiltin the_Stream) [a_exp]
          ty = Gluon.mkInternalFunE False a Gluon.pureKindE $
               Gluon.mkInternalArrowE False cls_exp iter_exp
      return ty
    binaryFunctionType = do
      let return_bool = Gluon.mkInternalConAppE (pyonBuiltin the_Action) 
                        [Gluon.mkInternalConE (pyonBuiltin the_bool)]
          ty = Gluon.mkInternalArrowE False clsType $
               Gluon.mkInternalArrowE False clsType $
               return_bool
      return ty

boolType = Gluon.mkInternalConE $ pyonBuiltin the_bool

tyPatType :: TyPat -> PyonType
tyPatType (TyPat _ t) = t

patType :: Pat -> PyonType
patType (WildP t)  = t
patType (VarP _ t) = t
patType (TupleP ps) = let size = length ps
                          con = case getPyonTupleType (length ps)
                                of Just n -> n
                                   Nothing -> error "Unsupported tuple size"
                          field_types = map patType ps
                      in Gluon.mkInternalConAppE con field_types

funType :: Fun -> PyonType 
funType (Fun { funTyParams = ty_params
             , funParams = params
             , funMonad = monad
             , funReturnType = ret 
             }) =
  -- Create a dependent type for each type parameter
  catEndo (map makeTyFun ty_params) $
  -- Create an arrow type for each value parameter
  catEndo (map makeParamArrow params) $
  -- Create the return type
  return_type
  where
    makeParamArrow p t = Gluon.mkInternalArrowE False (patType p) t
    makeTyFun (TyPat v t) t2 = Gluon.mkInternalFunE False v t t2
    return_type
      | monad == pyonBuiltin the_Stream =
        ret
      | monad == pyonBuiltin the_Action = 
        Gluon.mkInternalConAppE (pyonBuiltin the_Action) [ret]
      | otherwise =
        error "funType: Invalid monad"
      
assumePat :: Pat -> PureTC a -> PureTC a
assumePat p k = 
  case p
  of WildP p_ty -> k
     VarP v p_ty -> assumePure v p_ty k
     TupleP pats -> foldr assumePat k pats
     
assumeTyPat :: TyPat -> PureTC a -> PureTC a
assumeTyPat (TyPat v t) k = assumePure v t k

-- Assume a function definition.  Do not check the function definition's body.
assumeDef :: Def -> PureTC a -> PureTC a
assumeDef (Def v fun) = assumePure v (funType fun)

typeInferExp :: Exp -> PureTC CWhnf
typeInferExp expression = do
  e_type <-
    case expression
    of VarE {expVar = v} ->
         typeInferVarE v
       ConE {expCon = c} ->
         Gluon.evalFully =<< Gluon.getConstructorType c
       LitE {expLit = l, expType = t} ->
         checkLiteralType l t
       UndefinedE {expType = t} ->
         -- Evaluate the type; any type is acceptable
         Gluon.evalFully' t
       TupleE {expFields = fs} ->
         typeInferTupleE fs
       TyAppE {expOper = op, expTyArg = arg} ->
         typeInferTyAppE op arg
       CallE {expOper = op, expArgs = args} ->
         typeInferCallE op args
       IfE {expCond = cond, expTrueCase = tr, expFalseCase = fa} ->
         typeInferIfE cond tr fa
       FunE {expFun = f} ->
         typeInferFun f
       LetE {expBinder = pat, expValue = e, expBody = body} ->
         typeInferLetE pat e body
       LetrecE {expDefs = defs, expBody = body} ->
         typeInferLetrecE defs body
       DictE { expClass = cls
             , expType = ty
             , expSuperclasses = scs
             , expMethods = ms} ->
         typeInferDictE cls ty scs ms
       MethodSelectE { expClass = cls
                     , expType = ty
                     , expMethodIndex = n
                     , expArg = e} ->
         typeInferMethodSelectE cls ty n e
  return e_type
         
-- To infer a variable's type, just look it up in the environment
typeInferVarE :: Var -> PureTC CWhnf
typeInferVarE var =
  liftEvaluation . Gluon.evalFully' =<< getType' noSourcePos var

-- Use the type that was attached to the literal value, but also verify that
-- it's a valid type
checkLiteralType :: Lit -> PyonType -> PureTC CWhnf
checkLiteralType l t = do
  t' <- liftEvaluation $ Gluon.evalFully' t
  if isValidLiteralType t' l
    then return t'
    else throwError $ OtherErr $ "Not a valid literal type " ++ show (Gluon.pprExp (whnfExp t')) ++ "; " ++ show (pprLit l)

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
                                     
typeInferTupleE fs = do         
  -- Infer types of all fields
  f_types <- mapM typeInferExp fs
  
  -- Create a tuple type
  let size = length f_types
  case getPyonTupleType size
    of Nothing -> error "Unsupported tuple size"
       Just c -> return $ Gluon.mkInternalWhnfAppE c $ map whnfExp f_types
       
typeInferTyAppE op arg = do
  Whnf op_type <- typeInferExp op
  Whnf arg_type <- Gluon.typeInferExp arg

  -- Apply operator to argument
  case op_type of
    Gluon.FunE {Gluon.expMParam = param, Gluon.expRange = range} -> do
      -- Operand type must match
      Gluon.tcAssertEqual noSourcePos (verbatim $ Gluon.binder'Type param) 
                                      (verbatim arg_type)
      
      -- Result value is the range, after substituting operand in argument
      result <- liftEvaluation $ Gluon.evalFully $ assignBinder' param arg $ 
                verbatim range
      return result
      
    _ -> throwError $ Gluon.NonFunctionApplicationErr noSourcePos op_type

typeInferCallE op args = do
  -- Infer types of parameters
  op_type <- typeInferExp op
  arg_types <- mapM typeInferExp args

  -- Compute result type
  result_type <- computeAppliedType (whnfExp op_type) (map whnfExp arg_types)
  
  -- The result type must be in the 'Action' or 'Stream' monads.
  -- If 'Action', strip off the constructor.
  case Gluon.unpackWhnfAppE result_type
    of Just (con, [arg]) 
         | con `isPyonBuiltin` the_Action ->
           return $ Whnf arg
         | con `isPyonBuiltin` the_Stream ->
           return result_type
       _ -> throwError $ OtherErr "Incorrect function return type, \
                                  \or wrong number of arguments"

-- | Given a function type and a list of argument types, compute the result of
-- applying the function to the arguments.
computeAppliedType :: PyonType -> [PyonType] -> PureTC CWhnf
computeAppliedType op_type arg_types = apply (verbatim op_type) arg_types
  where
    apply op_type (arg_t:arg_ts) = do
      -- Operator must be a function type
      op_type' <- Gluon.evalHead op_type
      case whnfExp op_type' of
        Gluon.FunE { Gluon.expMParam = Gluon.Binder' Nothing dom ()
                   , Gluon.expRange = rng} -> do
          -- parameter type must match argument type
          tcAssertEqual noSourcePos dom (verbatim arg_t)
          
          -- continue with range
          apply rng arg_ts
          
        _ -> do op_type' <- Gluon.evalFully op_type
                throwError $ Gluon.NonFunctionApplicationErr noSourcePos (whnfExp op_type')

    apply op_type [] = Gluon.evalFully op_type

typeInferIfE cond if_true if_false = do
  -- Condition must be a bool
  cond_t <- typeInferExp cond
  tcAssertEqual noSourcePos (verbatim boolType) (verbatim $ whnfExp cond_t)
  
  -- True and false paths must be equal
  if_true_t <- typeInferExp if_true
  if_false_t <- typeInferExp if_false
  tcAssertEqual noSourcePos (verbatim $ whnfExp if_true_t) (verbatim $ whnfExp if_false_t)

  return if_true_t

typeInferFun fun@(Fun { funTyParams = ty_params
                      , funParams = params
                      , funReturnType = return_type
                      , funBody = body}) =
  assumeTyParams $ assumeParams $ do
    body_type <- typeInferExp body
    
    -- Return type must match inferred type
    tcAssertEqual noSourcePos (verbatim $ whnfExp body_type) (verbatim return_type)
    
    -- Create the function's type
    liftEvaluation $ Gluon.evalFully' $ funType fun
  where
    assumeTyParams = catEndo $ map assumeTyPat ty_params    
    assumeParams = catEndo $ map assumePat params

typeInferLetE pat expression body = do
  e_type <- typeInferExp expression
  
  -- Expression type must match pattern type
  tcAssertEqual noSourcePos (verbatim $ whnfExp e_type) (verbatim $ patType pat)

  -- Assume the pattern while inferring the body; result is the body's type
  assumePat pat $ typeInferExp body

typeInferLetrecE defs body = typeCheckDefGroup defs $ typeInferExp body

typeInferDictE cls ty scs ms = do
  sc_types <- mapM typeInferExp scs
  m_types <- mapM typeInferExp ms
  
  -- TODO: check that superclass and method types are correct
  let return_type = ty -- Gluon.mkInternalConAppE (classDictCon cls) [ty]
  liftEvaluation $ Gluon.evalFully' return_type

typeInferMethodSelectE cls ty index arg = do
  -- The argument must be a dictionary of the given class
  arg_ty <- typeInferExp arg
  ty' <- liftEvaluation $ Gluon.evalFully' $ 
         Gluon.mkInternalConAppE (classDictCon cls) [ty]
  tcAssertEqual noSourcePos (verbatim $ whnfExp ty') (verbatim $ whnfExp arg_ty)
  
  -- Determine the return value based on the class type and method index
  return_type <- classMethodType cls ty index
  liftEvaluation $ Gluon.evalFully' return_type

typeCheckDefGroup :: [Def] -> PureTC a -> PureTC a
typeCheckDefGroup defs k =
  -- Assume all defined function types
  catEndo (map assumeDef defs) $ do
    -- Check all defined function bodies
    xs <- mapM typeCheckDef defs
    
    -- Run the continuation in this environment
    k
  where
    -- To typecheck a definition, check the function it contains
    typeCheckDef (Def v fun) = typeInferFun fun

typeCheckModule (Module defs) =
  withTheVarIdentSupply $ \varIDs -> do
    runPureTCIO varIDs $ typeCheckDefGroup defs $ return ()
    
typeCheckModulePython mod = do
  result <- typeCheckModule mod
  case result of
    Left errs -> do mapM_ (putStrLn . showTypeCheckError) errs
                    throwPythonExc pyRuntimeError "Type checking failed"
    Right _ -> return ()
