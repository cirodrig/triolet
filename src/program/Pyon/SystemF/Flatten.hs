
{-# LANGUAGE TypeFamilies, EmptyDataDecls, UndecidableInstances, TypeSynonymInstances, ScopedTypeVariables #-}
module Pyon.SystemF.Flatten
       (flatten)
where

import Control.Monad

import Gluon.Common.Error
import Gluon.Common.SourcePos
import Gluon.Common.Supply
import qualified Gluon.Core.Builtins.Effect as Gluon.Builtins.Effect
import Gluon.Core.Level
import qualified Gluon.Core as Gluon
import Gluon.Core(Rec, fromWhnf, asWhnf, SynInfo, internalSynInfo, Binder(..), Con(..))
import Gluon.Eval.Environment
import Gluon.Eval.Eval

import Pyon.Globals
import Pyon.SystemF.Builtins
import Pyon.SystemF.Syntax
import Pyon.SystemF.Typecheck
import Pyon.NewCore.Print
import qualified Pyon.NewCore.Syntax as NewCore

-- | Flatten a module to imperative form
flatten :: Module Rec -> IO (Either [TypeCheckError] (NewCore.Module Rec))
flatten mod = do
  tc_result <- typeCheckModule flattenWorker mod
  case tc_result of
    Left errs -> return (Left errs)
    Right (Module new_defs) -> do
      (_, converted_defs) <-
        withTheVarIdentSupply $ \varIDs ->
        case runEval varIDs $ runFloatBinds $ mapM (don'tFloat . flattenDefGroup) new_defs
        of Just x -> return x
           Nothing -> internalError "Flattening failed"
      return $ Right (NewCore.Module $ concat converted_defs)
  where
    makeNewModule new_defs = return $ NewCore.Module new_defs

-------------------------------------------------------------------------------
-- Expression structure used in flattening

data ConvertToNewCore

-- | Each expression is converted to a value or a statement. 
-- The expression's type is passed to the caller, and the caller decides
-- how to float bindings.
newtype instance SFExpOf ConvertToNewCore ConvertToNewCore = 
  FB {convertExp :: FloatBinds (NewCore.RType, NewCoreTerm)}

type ConvertingExp = SFRecExp ConvertToNewCore

-- | An expression may be translated to a value, a statement, or a \"do\".
-- An application of \"do\" becomes a special value.
data NewCoreTerm =
    NewCoreVal !NewCore.RVal
  | NewCoreStm !NewCore.RStm
  | NewCoreDo
    
isDo :: NewCoreTerm -> Bool
isDo NewCoreDo = True
isDo _ = False

-- | Types are not changed.
newtype instance Gluon.ExpOf ConvertToNewCore ConvertToNewCore =
  NewCoreType {newCoreType :: NewCore.RType}

data LetBinding = VarBinding Var NewCore.RStm 
                | PatBinding RPat NewCore.RStm
type LetBindings = [LetBinding]

-- | A monad for floating bindings out of an expression
newtype FloatBinds a =
  FloatBinds {runFloatBinds :: Eval (LetBindings, a)}

instance Monad FloatBinds where
  return x = FloatBinds $ return ([], x)
  m >>= k = FloatBinds $ do (bs1, x) <- runFloatBinds m
                            (bs2, y) <- runFloatBinds (k x)
                            return (bs1 ++ bs2, y)

instance Supplies FloatBinds Gluon.VarID where
  fresh = liftEvaluation fresh
  supplyToST f = liftEvaluation (supplyToST f)

instance EvalMonad FloatBinds where
  liftEvaluation m = FloatBinds $ do x <- m
                                     return ([], x)

-- | Bind a variable to a value.  The binding will be floated outward. 
floatVarBinding :: Var -> NewCore.RStm -> FloatBinds ()
floatVarBinding v stm = FloatBinds $ return ([VarBinding v stm], ())

-- | Bind a pattern to a value.  The binding will be floated outward. 
floatPatBinding :: RPat -> NewCore.RStm -> FloatBinds ()
floatPatBinding p stm = FloatBinds $ return ([PatBinding p stm], ())

-- | Do not permit bindings to be floated out of the expression.  If one
-- would be floated, then throw an error.
don'tFloat :: FloatBinds a -> FloatBinds a
don'tFloat m = FloatBinds $ do
  (bs, x) <- runFloatBinds m
  if null bs
    then return ([], x) 
    else internalError "Flattening failed: cannot bind here"

-- | Bind variables or patterns here.
reifyBindings :: FloatBinds (a, NewCore.RStm) -> FloatBinds (a, NewCore.RStm)
reifyBindings m = FloatBinds $ do
  (bs, (x, body)) <- runFloatBinds m
  statement <- makeBindings body bs
  return ([], (x, statement))

reifyBindings' m = liftM snd $ reifyBindings $ liftM ((,) ()) m

makeBindings body bs = foldM makeBinding body $ reverse bs
  where
    -- Attach the body's information to all created expressions
    statement_info = NewCore.stmInfo body
    statement_pos = getSourcePos statement_info
    
    makeBinding :: NewCore.RStm -> LetBinding -> Eval NewCore.RStm
    makeBinding body (VarBinding v rhs) =
      return $ NewCore.LetS statement_info (Just v) rhs body
    
    makeBinding body (PatBinding pat rhs) = do
      (lhs, body') <- deconstruct pat body
      return $ NewCore.LetS statement_info lhs rhs body'
      
    -- Deconstruct an expression based on a pattern.  Return an expression
    -- that does the deconstruction, and a variable that is used as a
    -- scrutinee in the case statement (if one is needed).  The caller should
    -- bind the variable to the value that the pattern is matched against.
    deconstruct (WildP _)   body = return (Nothing, body)
    deconstruct (VarP v _)  body = return (Just v, body)
    deconstruct (TupleP ps) body = do
      -- Deconstruct each tuple member
      (pat_vars, body') <- deconstructList ps body
      
      -- Every tuple field should be bound to a variable, even if it is unused
      pat_vars' <- mapM (maybe createPatternVariable return) pat_vars
    
      -- Put the result in a case expression
      let tuple_size = length ps
          con = getPyonTupleCon' tuple_size
          tuple_params = replicate tuple_size NewCore.RigidP ++
                         map NewCore.FlexibleP pat_vars'
          pattern = NewCore.ConP con tuple_params
          alt = NewCore.Alt statement_info pattern body'
      
      -- Scrutinee must be bound to a new variable
      scr_var <- createPatternVariable
      let scrutinee = NewCore.mkVarV statement_pos scr_var
          stmt = NewCore.CaseS statement_info scrutinee [alt]
      return (Just scr_var, stmt)

    -- Deconstruct all patterns in the list.
    deconstructList (pat:pats) body = do
      (vars, body') <- deconstructList pats body
      (var, body'') <- deconstruct pat body'
      return (var:vars, body'')
      
    deconstructList [] body = return ([], body)
    
    createPatternVariable = newTemporary ObjectLevel Nothing

statementReturningVar pos v =
  NewCore.ReturnS (Gluon.mkSynInfo pos ObjectLevel) $ NewCore.mkVarV pos v

-- | Convert the parameter to a value or a 'do' operator.  If the parameter
-- is a statement, then bind it to a variable.
-- Return a value, or Nothing if the parameter is a 'do' operator.
asValueOrDoWithType :: ConvertingExp
                    -> FloatBinds (NewCore.RType, Maybe NewCore.RVal)
asValueOrDoWithType m = convertExp m >>= toValue
  where
    toValue (ty, NewCoreVal value) = return (ty, Just value)
    toValue (ty, NewCoreStm statement) = do
      -- Create a new temporary variable
      temp_var <- liftEvaluation (newTemporary ObjectLevel Nothing)
      -- Add a binder for this variable
      floatVarBinding temp_var statement
      -- Use the variable in place of the old value
      return (ty, Just $ NewCore.mkVarV (getSourcePos statement) temp_var)
    toValue (ty, NewCoreDo) =
      return (ty, Nothing)

asValueWithType :: ConvertingExp
                -> FloatBinds (NewCore.RType, NewCore.RVal)
asValueWithType m = asValueOrDoWithType m >>= disallowDo
  where
    disallowDo (ty, Just v) = return (ty, v)
    disallowDo (ty, Nothing) =
      internalError "Cannot convert the 'do' operator to a value"

asValue :: ConvertingExp -> FloatBinds NewCore.RVal
asValue m = do x <- asValueWithType m
               return $ snd x

-- | Convert to a value or to the 'do' operator.  A Nothing return value 
-- indicates that this is the 'do' operator.
asValueOrDo :: ConvertingExp -> FloatBinds (Maybe NewCore.RVal)
asValueOrDo m = do x <- asValueOrDoWithType m 
                   return $ snd x

asStatementWithType :: ConvertingExp 
                    -> FloatBinds (NewCore.RType, NewCore.RStm)
asStatementWithType m = reifyBindings $ toStatement =<< convertExp m
  where 
    toStatement (ty, NewCoreVal value) =
      return (ty, NewCore.ReturnS (NewCore.valInfo value) value)
    toStatement (ty, NewCoreStm stm) = return (ty, stm)
    toValue (ty, NewCoreDo) =
      internalError "Cannot convert the 'do' operator to a statement"

asStatement :: ConvertingExp -> FloatBinds NewCore.RStm
asStatement m = liftM snd $ asStatementWithType m

flattenWorker :: Worker ConvertToNewCore
flattenWorker = Worker flattenType flattenExp

flattenType :: Gluon.WRExp -> PureTC (TypeOf ConvertToNewCore ConvertToNewCore)
flattenType t = return $ NewCoreType $ fromWhnf t

flattenExp :: SFExp ConvertToNewCore -> Gluon.WRExp -> PureTC ConvertingExp
flattenExp expression ty =
  liftEvaluation $ return $ FB $ flattenExp' expression (fromWhnf ty)

flattenExp' :: SFExp ConvertToNewCore -> Gluon.RExp -> FloatBinds (NewCore.RType, NewCoreTerm)
flattenExp' expression expression_type =
  case expression
  of VarE {expVar = v} ->
       returnValue $ NewCore.mkVarV pos v
     ConE {expCon = c}
       | c `isPyonBuiltin` the_oper_DO -> returnDo
       | otherwise -> returnValue $ NewCore.mkConV pos c
     LitE {expInfo = inf, expLit = l} ->
       case l
       of IntL n      -> returnValue $ NewCore.mkLitV pos (Gluon.IntL n)
          FloatL d    -> returnValue $ NewCore.mkLitV pos (Gluon.FloatL d)
          BoolL True  -> returnCon inf $ pyonBuiltin the_True
          BoolL False -> returnCon inf $ pyonBuiltin the_False
          NoneL       -> returnCon inf $ pyonBuiltin the_None
     UndefinedE {expInfo = inf, expType = NewCoreType t} ->
       let fun = NewCore.mkConV pos $ pyonBuiltin the_fun_undefined
           arg = NewCore.GluonV (Gluon.mkSynInfo (Gluon.getSourcePos inf) TypeLevel) t
       in returnStatement $ NewCore.CallS inf $ NewCore.AppV inf fun [arg]
     TupleE {expInfo = inf, expFields = fs} -> do
       (field_types :: [NewCore.RType], fields :: [NewCore.RVal]) <- mapAndUnzipM asValueWithType fs
       
       -- Create a tuple expression.  Apply the tuple constructor to all
       -- types and all fields.
       let con = NewCore.mkConV pos $ getPyonTupleCon' $ length fields
           field_type_values =
             [NewCore.GluonV (Gluon.expInfo t) t | t <- field_types]
       returnValue $ NewCore.AppV inf con (field_type_values ++ fields)
     TyAppE {expInfo = inf, expOper = op, expTyArg = NewCoreType arg} -> do
       op' <- asValueOrDo op
       case op' of
         Nothing  -> returnDo
         Just val ->
           let arg_value = NewCore.GluonV (Gluon.expInfo arg) arg
           in returnValue $ NewCore.AppV inf val [arg_value]
     CallE {expInfo = inf, expOper = op, expArgs = args} -> do
       (op_type, maybe_op) <- asValueOrDoWithType op
       case maybe_op of
         Nothing ->
           case args
           of [arg] -> do
                arg' <- asStatement arg
                returnValue $ NewCore.SDoV inf arg'
              _ -> internalError "Wrong number of arguments to 'do'"
         Just op' -> do
           args' <- mapM asValue args
       
           -- Based on the operator's type, decide whether to generate a 
           -- statement or a value.  Calls in the 'Action' monad become 
           -- statements.  Calls in the 'Stream' monad become values.
           let call = NewCore.AppV inf op' args'
           is_stm <- is_statement (Gluon.verbatim op_type)
           if is_stm
             then returnStatement $ NewCore.CallS inf call
             else returnValue call
     IfE { expInfo = inf
         , expCond = cond
         , expTrueCase = tr
         , expFalseCase = fa} -> do
       -- Translate to a 'case' statement.
       -- The condition is an expression; the true and false cases are
       -- statements.
       cond' <- asValue cond
       tr' <- asStatement tr
       fa' <- asStatement fa
       let true_alt = NewCore.Alt inf (NewCore.ConP (pyonBuiltin the_True) []) tr'
       let false_alt = NewCore.Alt inf (NewCore.ConP (pyonBuiltin the_False) []) fa'
       returnStatement $ NewCore.CaseS inf cond' [true_alt, false_alt]
     FunE {expInfo = inf, expFun = fun} -> do
       converted_fun <- flattenFun fun
       case converted_fun of
         Left action_fun  -> returnValue $ NewCore.ALamV inf action_fun
         Right stream_fun -> returnValue $ NewCore.SLamV inf stream_fun
     LetE { expInfo = inf
          , expBinder = pat
          , expValue = rhs
          , expBody = body} -> do
       rhs' <- asStatement rhs
       expr' <- reifyBindings' $ do floatPatBinding (convertPattern pat) rhs' 
                                    asStatement body
       returnStatement expr'
     LetrecE { expInfo = inf
             , expDefs = defs
             , expBody = body} -> do
       defs' <- flattenDefGroup defs
       body' <- asStatement body
       returnStatement $ NewCore.LetrecS inf defs' body'
{-     DictE { expInfo = inf
           , expClass = cls
           , expType = NewCoreType ty
           , expSuperclasses = scs
           , expMethods = ms} -> do
       let cls_con = pyonClassConstructor cls
       superclasses <- mapM asValue scs
       methods <- mapM asValue ms
       -- Arguments are the class type, superclasses, and methods
       let args = NewCore.GluonV inf ty : superclasses ++ methods
       returnValue $ NewCore.AppV inf (NewCore.mkConV pos cls_con) args
     MethodSelectE { expInfo = inf
                   , expClass = cls
                   , expType = NewCoreType ty
                   , expMethodIndex = n
                   , expArg = arg} -> do
       -- Construct a case statement that selects the desired method
       scrutinee <- asValue arg

       -- Create a variable for each flexible parameter
       let num_superclasses = pyonClassNumSuperclasses cls 
           num_methods = pyonClassNumMethods cls
       cls_params <- replicateM (num_superclasses + num_methods) $
                     newTemporary ObjectLevel Nothing
       let this_method_var = cls_params !! (num_superclasses + n)
           
       -- Build the case statement
       let cls_con = pyonClassConstructor cls
       let pat_params = NewCore.RigidP : map NewCore.FlexibleP cls_params
           alt = NewCore.Alt inf (NewCore.ConP cls_con pat_params) $
                 NewCore.ReturnS inf $ NewCore.mkVarV pos this_method_var
           stm = NewCore.CaseS inf scrutinee [alt]
       returnStatement stm -}
  where
    pos = getSourcePos expression
    
    -- Return True for Stream constructors, False for Action constructors
    is_statement t = return False {-do
      t' <- evalHead t
      case fromWhnf t' of
        Gluon.FunE {Gluon.expRange = t2} -> is_statement t2
        Gluon.AppE {Gluon.expOper = oper} -> do
          oper' <- evalHead oper
          case fromWhnf oper' of
            Gluon.ConE {Gluon.expCon = con}
              | con `isPyonBuiltin` the_Action -> return True
              | con `isPyonBuiltin` the_Stream -> return False
            _ -> internalError "Not a valid function type"
        _ -> internalError "Not a valid function type" -}
    
    returnValue v = return (expression_type, NewCoreVal v)
    returnStatement s = return (expression_type, NewCoreStm s)
    returnDo = return (expression_type, NewCoreDo)
    returnCon inf c = returnValue $ NewCore.GluonV inf $ Gluon.ConE inf c
{-
    -- Bind tuple field patterns.  Create a series of bindings.
    bindFieldPatterns inf (body :: NewCore.RStm) (pat:pats) (var:vars) =
      case pat
      of WildP _  -> bindFieldPatterns inf body pats vars
         VarP _ _ -> bindFieldPatterns inf body pats vars
         TupleP _ -> let expr = NewCore.ReturnS (internalSynInfo ObjectLevel) $
                                NewCore.mkVarV noSourcePos var
                     in do body' <- bindFieldPatterns inf body pats vars
                           bindPattern inf pat expr body'
    
    bindFieldPatterns _ body [] [] = return body

    -- Bind a pattern.
    -- Pattern matches are translated into a let followed by a case.
    bindPattern :: SynInfo -> Pat ConvertToNewCore -> NewCore.RStm -> NewCore.RStm 
                -> Eval NewCore.RStm
    bindPattern inf pat rhs body =
      case pat
      of WildP _   -> return $ NewCore.LetS inf Nothing rhs body
         VarP v _  -> return $ NewCore.LetS inf (Just v) rhs body
         TupleP ps -> do
           let tuple_size = length ps
               tuple_con = getPyonTupleType' tuple_size

           -- Create a temporary variable for each tuple field
           pattern_vars <- mapM makePatternVar ps
           let pattern = NewCore.ConP tuple_con $
                         replicate tuple_size NewCore.RigidP ++
                         map NewCore.FlexibleP pattern_vars

           -- Bind sub-patterns
           body' <- bindFieldPatterns inf body ps pattern_vars
           
           -- Bind RHS to a temporary variable
           temp_var <- newTemporary ObjectLevel Nothing
           return $ NewCore.LetS inf (Just temp_var) rhs body'
      where
        makePatternVar (VarP v _) = return v 
        makePatternVar _          = newTemporary ObjectLevel Nothing
-}
convertPattern :: Pat ConvertToNewCore -> Pat Rec
convertPattern (WildP ty) = WildP (newCoreType ty)
convertPattern (VarP v ty) = VarP v (newCoreType ty)
convertPattern (TupleP ps) = TupleP $ map convertPattern ps

convertTyParam (TyPat v ty) =
  return $ Binder v (newCoreType ty) ()

convertParam (WildP ty) = do
  v <- newTemporary ObjectLevel Nothing
  return $ Binder v (newCoreType ty) ()

convertParam (VarP v ty) = return $ Binder v (newCoreType ty) ()

convertParam (TupleP _) = internalError "Tuple parameters not implemented"

flattenDef :: Def ConvertToNewCore -> FloatBinds (NewCore.Def Rec)
flattenDef (Def name fun) = return . rebuild_def =<< flattenFun fun
  where
    inf = Gluon.internalSynInfo ObjectLevel
    rebuild_def (Left action_fun) =
      NewCore.Def inf name $ NewCore.ActionFunDef action_fun
    rebuild_def (Right stream_fun) =
      NewCore.Def inf name $ NewCore.StreamFunDef stream_fun
    
flattenDefGroup :: [Def ConvertToNewCore] -> FloatBinds [NewCore.Def Rec]
flattenDefGroup = mapM flattenDef

flattenFun :: Fun ConvertToNewCore 
           -> FloatBinds (Either (NewCore.ActionFun Rec) (NewCore.StreamFun Rec))
flattenFun fun = do
  -- Convert function parameters
  ty_params <- mapM convertTyParam (funTyParams fun) 
  val_params <- mapM convertParam (funParams fun)
  let params = ty_params ++ val_params :: [Binder Rec ()]
      
  -- Get the return type
  let rt = newCoreType $ funReturnType fun
      
  -- Assume it has no side effects
  let effect = Gluon.Builtins.Effect.empty
      
  -- Create either an action function or a stream function
  internalError "Not implemented: function flattening"
  {-
  if funMonad fun `isPyonBuiltin` the_Action
    then do body <- asStatement $ funBody fun
            return $ Left $ NewCore.Fun params rt effect body
    else do body <- don'tFloat $ asValue $ funBody fun
            return $ Right $ NewCore.Fun params rt effect body -}

  