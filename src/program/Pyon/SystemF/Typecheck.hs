
{-# LANGUAGE ScopedTypeVariables, TypeFamilies #-}
module Pyon.SystemF.Typecheck
       (Worker(..), typeCheckModule, typeCheckModulePython)
where

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
  { doType :: !(WRExp -> PureTC (TypeOf a))
  , doExp  :: !(Exp a -> WRExp -> PureTC (ExpOf a))
  }

type instance ExpOf TrivialStructure = ()
type instance TypeOf TrivialStructure = ()

noWork :: Worker TrivialStructure
noWork = Worker { doType = \_ -> return ()
                , doExp = \_ _ -> return ()
                }

-- Endomorphism concatenation
catEndo xs k = foldr ($) k xs

withMany :: (a -> (b -> c) -> c) -> [a] -> ([b] -> c) -> c
withMany f xs k = go xs k
  where
    go (x:xs) k = f x $ \y -> go xs $ \ys -> k (y:ys)
    go []     k = k []

makeActionType return_type =
  Gluon.mkInternalConAppE (pyonBuiltin the_Action) 
  [Gluon.Builtins.Effect.empty, return_type]

classDictCon EqClass = pyonBuiltin the_EqDict
classDictCon OrdClass = pyonBuiltin the_OrdDict
classDictCon TraversableClass = pyonBuiltin the_TraversableDict
classDictCon AdditiveClass = pyonBuiltin the_AdditiveDict
classDictCon VectorClass = pyonBuiltin the_VectorDict

classMethodType cls clsType index =
  case cls
  of EqClass ->
       case index
       of 0 -> comparisonType
          1 -> comparisonType
     OrdClass ->
       case index
       of 0 -> comparisonType
          1 -> comparisonType
          2 -> comparisonType
          3 -> comparisonType
     TraversableClass ->
       case index
       of 0 -> traverseType
     AdditiveClass ->
       case index
       of 0 -> valueType
          1 -> binaryFunctionType
          2 -> binaryFunctionType
     VectorClass ->
       case index
       of 0 -> scaleType
          1 -> normType
  where
    traverseType = do
      a <- newTemporary Gluon.TypeLevel Nothing
      let a_exp = Gluon.mkInternalVarE a
          cls_exp = Gluon.mkInternalAppE clsType [a_exp]
          iter_exp = Gluon.mkInternalConAppE (pyonBuiltin the_Stream)
                     [ Gluon.Builtins.Effect.empty
                     , a_exp]
          ty = Gluon.mkInternalFunE False a Gluon.pureKindE $
               Gluon.mkInternalArrowE False cls_exp iter_exp
      return ty
    binaryFunctionType = do
      let ty = Gluon.mkInternalArrowE False clsType $
               Gluon.mkInternalArrowE False clsType $
               makeActionType $ clsType
      return ty
    comparisonType = do
      let return_bool = makeActionType $
                        Gluon.mkInternalConE (pyonBuiltin the_bool)
          ty = Gluon.mkInternalArrowE False clsType $
               Gluon.mkInternalArrowE False clsType $
               return_bool
      return ty
    valueType = return $ makeActionType clsType
    scaleType =
      let float_type = Gluon.mkInternalConE (Gluon.builtin Gluon.the_Float)
      in return $ Gluon.mkInternalArrowE False clsType $
                  Gluon.mkInternalArrowE False float_type $
                  makeActionType clsType
    normType =
      let float_type = Gluon.mkInternalConE (Gluon.builtin Gluon.the_Float)
      in return $ Gluon.mkInternalArrowE False clsType $
                  makeActionType float_type

boolType = Gluon.mkInternalConE $ pyonBuiltin the_bool

tyPatType :: RTyPat -> PyonType
tyPatType (TyPat _ t) = t

patType :: RPat -> PyonType
patType (WildP t)  = t
patType (VarP _ t) = t
patType (TupleP ps) = let size = length ps
                          con = case getPyonTupleType (length ps)
                                of Just n -> n
                                   Nothing -> error "Unsupported tuple size"
                          field_types = map patType ps
                      in Gluon.mkInternalConAppE con field_types

funType :: RFun -> PyonType 
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
      | monad == pyonBuiltin the_Stream = ret
      | monad == pyonBuiltin the_Action = makeActionType ret
      | otherwise = error "funType: Invalid monad"
      
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

typeInferExp :: Worker a -> RExp -> PureTC (WRExp, ExpOf a)
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
       DictE { expInfo = inf
             , expClass = cls
             , expType = ty
             , expSuperclasses = scs
             , expMethods = ms} ->
         typeInferDictE worker inf cls ty scs ms
       MethodSelectE { expInfo = inf
                     , expClass = cls
                     , expType = ty
                     , expMethodIndex = n
                     , expArg = e} ->
         typeInferMethodSelectE worker inf cls ty n e
  new_val <- doExp worker new_exp e_type
  return (e_type, new_val)
         
-- To infer a variable's type, just look it up in the environment
typeInferVarE :: ExpInfo -> Var -> PureTC (WRExp, Exp a)
typeInferVarE inf var = do
  lookup_type <- getType' noSourcePos var
  ty <- liftEvaluation $ Gluon.evalFully' lookup_type
  return (ty, VarE inf var)

-- Use the type that was attached to the literal value, but also verify that
-- it's a valid type
checkLiteralType :: Worker a -> ExpInfo -> Lit -> PyonType 
                 -> PureTC (WRExp, Exp a)
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
                                     
typeInferTupleE :: Worker a -> ExpInfo -> [RExp] -> PureTC (WRExp, Exp a)
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

typeInferTyAppE :: Worker a -> ExpInfo -> RExp -> PyonType
                -> PureTC (WRExp, Exp a)
typeInferTyAppE worker inf op arg = do
  (op_type, op_val) <- typeInferExp worker op
  arg_type <- Gluon.typeInferExp arg
  arg_val <- doType worker =<< Gluon.evalFully' arg

  -- Apply operator to argument
  case fromWhnf op_type of
    Gluon.FunE {Gluon.expMParam = param, Gluon.expRange = range} -> do
      -- Operand type must match
      tcAssertEqual noSourcePos (verbatim $ Gluon.binder'Type param) 
                                (verbatim $ fromWhnf arg_type)
      
      -- Result type is the range, after substituting operand in argument
      result <- liftEvaluation $
                Gluon.evalFully $
                assignBinder' param arg $
                verbatim range
      return (result, TyAppE inf op_val arg_val)
      
    _ -> throwError $ Gluon.NonFunctionApplicationErr noSourcePos (fromWhnf op_type)

typeInferCallE :: Worker a -> ExpInfo -> RExp -> [RExp] 
               -> PureTC (WRExp, Exp a)
typeInferCallE worker inf op args = do
  -- Infer types of parameters
  (op_type, op_val) <- typeInferExp worker op
  (arg_types, arg_vals) <- mapAndUnzipM (typeInferExp worker) args

  -- Compute result type
  result_type <- computeAppliedType (fromWhnf op_type) (map fromWhnf arg_types)
  
  -- The result type must be in the 'Action' or 'Stream' monads.
  -- If 'Action', strip off the constructor.
  -- Ignore the effect type.
  ty <- case Gluon.unpackWhnfAppE result_type
        of Just (con, [_, arg]) 
             | con `isPyonBuiltin` the_Action ->
                 return $ asWhnf arg
             | con `isPyonBuiltin` the_Stream ->
                 return result_type
           _ -> throwError $ OtherErr "Incorrect function return type, \
                                      \or wrong number of arguments"

  return (ty, CallE inf op_val arg_vals)

-- | Given a function type and a list of argument types, compute the result of
-- applying the function to the arguments.
computeAppliedType :: PyonType -> [PyonType] -> PureTC WRExp
computeAppliedType op_type arg_types = apply (verbatim op_type) arg_types
  where
    apply op_type (arg_t:arg_ts) = do
      -- Operator must be a function type
      op_type' <- Gluon.evalHead op_type
      case fromWhnf op_type' of
        Gluon.FunE { Gluon.expMParam = Gluon.Binder' Nothing dom ()
                   , Gluon.expRange = rng} -> do
          -- parameter type must match argument type
          tcAssertEqual noSourcePos dom (verbatim arg_t)
          
          -- continue with range
          apply rng arg_ts
          
        _ -> do op_type' <- Gluon.evalFully op_type
                throwError $ Gluon.NonFunctionApplicationErr noSourcePos (fromWhnf op_type')

    apply op_type [] = Gluon.evalFully op_type

typeInferIfE :: Worker a -> ExpInfo -> RExp -> RExp -> RExp
             -> PureTC (WRExp, Exp a)
typeInferIfE worker inf cond if_true if_false = do
  -- Condition must be a bool
  (cond_t, cond_val) <- typeInferExp worker cond
  tcAssertEqual noSourcePos (verbatim boolType) (verbatim $ fromWhnf cond_t)
  
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
    
    let new_fun = Fun { funTyParams = new_ty_params
                      , funParams = new_params
                      , funReturnType = return_type_val
                      , funMonad = funMonad fun
                      , funBody = body_val
                      }
    return (ty, new_fun)
  where
    assumeTyParams = withMany (assumeTyPat worker) ty_params
    assumeParams = withMany (assumePat worker) params

typeInferLetE :: Worker a -> ExpInfo -> RPat -> RExp -> RExp
              -> PureTC (WRExp, Exp a)
typeInferLetE worker inf pat expression body = do
  (e_type, e_val) <- typeInferExp worker expression
  
  -- Expression type must match pattern type
  tcAssertEqual noSourcePos (verbatim $ fromWhnf e_type) (verbatim $ patType pat)

  -- Assume the pattern while inferring the body; result is the body's type
  assumePat worker pat $ \pat' -> do
    (body_type, body_val) <- typeInferExp worker body
    return (body_type, LetE inf pat' e_val body_val)

typeInferLetrecE :: Worker a -> ExpInfo -> [RDef] -> RExp
                 -> PureTC (WRExp, Exp a)
typeInferLetrecE worker inf defs body =
  typeCheckDefGroup worker defs $ \defs' -> do
    (body_type, body_val) <- typeInferExp worker body
    return (body_type, LetrecE inf defs' body_val)

typeInferDictE :: Worker a -> ExpInfo -> PyonClass -> PyonType
               -> [RExp] -> [RExp]
               -> PureTC (WRExp, Exp a)
typeInferDictE worker inf cls ty scs ms = do
  (sc_types, sc_values) <- mapAndUnzipM (typeInferExp worker) scs
  (m_types, m_value) <- mapAndUnzipM (typeInferExp worker) ms
  
  -- TODO: check that superclass and method types are correct
  ty' <- Gluon.evalFully' ty
  let return_type_uneval = 
        Gluon.mkInternalConAppE (classDictCon cls) [fromWhnf ty']
  return_type <- liftEvaluation $ Gluon.evalFully' return_type_uneval
  ty_val <- doType worker ty'
  
  return (return_type, DictE inf cls ty_val sc_values m_value)

typeInferMethodSelectE :: Worker a -> ExpInfo -> PyonClass -> PyonType
                       -> Int -> RExp
                       -> PureTC (WRExp, Exp a)
typeInferMethodSelectE worker inf cls ty index arg = do
  -- The argument must be a dictionary of the given class
  (arg_ty, arg_val) <- typeInferExp worker arg
  ty' <- Gluon.evalFully' $ Gluon.mkInternalConAppE (classDictCon cls) [ty]
  tcAssertEqual noSourcePos (verbatim $ fromWhnf ty') (verbatim $ fromWhnf arg_ty)
  
  ty_val <- doType worker =<< Gluon.evalFully' ty
  
  -- Determine the return value based on the class type and method index
  return_type <- Gluon.evalFully' =<< classMethodType cls ty index
  return (return_type, MethodSelectE inf cls ty_val index arg_val)

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

typeCheckModule worker (Module defs) =
  withTheVarIdentSupply $ \varIDs -> do
    runPureTCIO varIDs $ typeCheckDefGroup worker defs $ \defs -> return $ Module defs
    
typeCheckModulePython mod = do
  result <- typeCheckModule noWork mod
  case result of
    Left errs -> do mapM_ (putStrLn . showTypeCheckError) errs
                    throwPythonExc pyRuntimeError "Type checking failed"
    Right _ -> return ()
