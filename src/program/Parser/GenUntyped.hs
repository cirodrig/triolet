
module Parser.GenUntyped(convertToUntyped)
where

import Prelude hiding(mapM)
import Control.Monad hiding(forM, mapM)
import Control.Monad.Reader hiding(forM, mapM)
import Data.IORef
import qualified Data.Map as Map
import Data.Traversable

import qualified Language.Python.Common.AST as Python
import Parser.ParserSyntax
import Parser.SSA
import Common.Error
import Common.Label
import Common.SourcePos
import Common.Supply
import Common.MonadLogic
import qualified Untyped.Data as U
import qualified Untyped.Syntax as U
import qualified SystemF.Syntax as SF
import qualified Untyped.HMType as U
import qualified Untyped.Kind as U
import Untyped.Builtins
import Type.Level
import Type.Var(mkVar)
import qualified Type.Type
import qualified Builtins.Builtins
import Globals
import qualified Export

-- | During conversion, we keep an assignment from
-- parser variables to type variables
type Cvt a = ReaderT (Maybe U.Variable, Map.Map SSAVar U.ParserVarBinding) IO a

envReturnVar = fst
envMap = snd
modifyEnvMap f (v, m) = (v, f m)
modifyEnvReturnVar f (v, m) = (f v, m)

getReturnVar :: Cvt U.Variable
getReturnVar = ReaderT $ \env ->
  case envReturnVar env
  of Just v -> return v
     Nothing -> internalError "getReturnVar"

withNewReturnVar :: Cvt a -> Cvt a
withNewReturnVar m = do
  v <- newVariable ""
  local (modifyEnvReturnVar (const (Just v))) m

lookupKind :: SSAVar -> Cvt U.Kind
lookupKind v = ReaderT $ \env ->
  case Map.lookup v $ envMap env
  of Just (U.KindBinding k) -> return k
     Just _ -> error $ "Not a kind variable: " ++ varName v
     Nothing -> internalError $ "Unknown variable: " ++ varName v

lookupType :: SSAVar -> Cvt U.TyCon
lookupType v = ReaderT $ \env ->
  case Map.lookup v $ envMap env
  of Just (U.TypeBinding t) -> return t
     Just _ -> error $ "Not a type variable: " ++ varName v
     Nothing -> internalError $ "Unknown variable: " ++ varName v

lookupObject :: SSAVar -> Cvt U.Variable
lookupObject v = ReaderT $ \env ->
  case Map.lookup v $ envMap env
  of Just (U.ObjectBinding v) -> return v
     Just _ -> error $ "Not a value variable: " ++ varName v
     Nothing -> internalError $ "Unknown variable: " ++ varName v

withBinding :: SSAVar -> U.ParserVarBinding -> Cvt a -> Cvt a
withBinding v b = local (modifyEnvMap $ Map.insert v b)

-- | Convert an expression to a kind
doKind :: SSAExpr -> Cvt U.Kind
doKind expr =
  case expr
  of Binary pos (Python.Arrow {}) l r ->
       liftM2 (U.:->) (doKind l) (doKind r)
     Variable pos v ->
       lookupKind v
     
-- | Convert a function domain, which is 'None', a single type, 
-- or a product of types.
doFunDomain :: SSAExpr -> Cvt [U.HMType]
doFunDomain (Literal _ NoneLit) = return []
doFunDomain expr =
  case expr
  of Binary pos (Python.Multiply {}) l r -> do
       l' <- doFunDomain l
       r' <- doType r
       return (l' ++ [r'])
     _ -> do
       t <- doType expr
       return [t]

doType :: SSAExpr -> Cvt U.HMType
doType expr =
  case expr
  of Variable pos v -> liftM U.ConTy $ lookupType v
     Binary pos (Python.Arrow {}) l r ->
       liftM2 U.functionType (doFunDomain l) (doType r)
     Tuple pos ts ->
       liftM U.tupleType $ mapM doType ts
     Call pos op args -> do
       op' <- doType op
       args' <- mapM doType args
       return $ foldl U.appTy op' args'

withForallAnnotation :: ForallAnnotation SSAID
                     -> ([U.TyCon] -> Cvt a) -> Cvt a
withForallAnnotation ann m = withMany with_ann ann m
  where
    with_ann (v, kind_ann) k = do
      -- Determine the variable's kind
      kind <- case kind_ann
              of Nothing -> return U.Star
                 Just e  -> doKind e
      
      -- Create a type variable
      let lab = case varName v
                of "" -> Nothing
                   nm -> Just $ pyonLabel (ModuleName "pyonfile") nm
      tyvar <- liftIO $ U.newRigidTyVar kind lab

      -- Add to environment
      withBinding v (U.TypeBinding tyvar) $ k tyvar

withMaybeForallAnnotation Nothing k = k Nothing
withMaybeForallAnnotation (Just a) k = withForallAnnotation a $ k . Just

-- | Create a new untyped variable with the given name
newVariable :: String -> Cvt U.Variable
newVariable name = do
  sfvar_id <- liftIO $ withTheNewVarIdentSupply supplyValue
  let sfvar = Just $ mkVar sfvar_id p_label ObjectLevel
  liftIO $ U.newVariable u_label sfvar
  where
    (u_label, p_label) =
      if null name
      then (Nothing, Nothing)
      else (Just $ pyonLabel (ModuleName "pyonfile") name,
            Just $ pyonLabel (ModuleName "pyonfile") name)

-------------------------------------------------------------------------------

convertVariable :: SSAVar -> (U.Variable -> Cvt a) -> Cvt a
convertVariable v k = do
  v' <- newVariable (varName v)
  withBinding v (U.ObjectBinding v') $ k v'

convertParameter :: SSAParameter -> (U.Pattern -> Cvt a) -> Cvt a
convertParameter param k =
  case param
  of Parameter v ann -> do
       ann' <- mapM doType ann
       convertVariable v $ \v' ->
         k $ U.VariableP (U.Ann noSourcePos) v' ann'
     TupleParam ps ->
       withMany convertParameter ps $ \ps' -> do
         k $ U.TupleP (U.Ann noSourcePos) ps'

convertParameters = withMany convertParameter

convertDefGroup :: [Func SSAID] -> ([U.FunctionDef] -> Cvt a) -> Cvt a
convertDefGroup defs k =
  withMany convertVariable (map funcName defs) $ \fun_names -> do
    k =<< zipWithM convert_def fun_names defs
  where
    convert_def nm func =
      -- Convert type parameters
      withMaybeForallAnnotation (funcAnnotation func) $ \qvars ->
      -- Convert parameters
      convertParameters (funcParams func) $ \params -> do
        -- Convert return type
        ret_type <- mapM doType $ funcReturnAnnotation func
        
        -- Convert body
        let mk_fallthrough _ =
              internalError "Control flow leaves function body"
        body <- withNewReturnVar $ doSuite (funcBody func) mk_fallthrough
        
        return $ U.FunctionDef nm $
          U.Function (U.Ann (funcPos func)) qvars params ret_type body
      
doVar :: SourcePos -> SSAVar -> Cvt U.Expression
doVar pos v = 
  case varID v
  of (_, SSAUndef) ->
       -- This variable has no definition.  Create an undefined expression.
       return $ U.UndefinedE (U.Ann pos)
     _ -> do
       v' <- lookupObject v
       return $ U.VariableE (U.Ann pos) v'

doExpr :: SSAExpr -> Cvt U.Expression
doExpr expr =
  case expr
  of Variable pos v -> doVar pos v
     Literal pos l ->
       let make_literal lit = U.LiteralE (U.Ann pos) lit
           l' = case l
                of IntLit n ->
                     -- Generate a call to 'fromInt' to cast to any valid value
                     let oper = tiBuiltin the___fromint__
                     in callVariable pos oper [make_literal (U.IntL n)]
                   FloatLit f ->
                     -- Generate a call to 'fromFloat' to cast to any valid value
                     let oper = tiBuiltin the___fromfloat__
                     in callVariable pos oper [make_literal (U.FloatL f)]
                   ImaginaryLit d ->
                     -- Generate a call to 'makeComplex' and 'fromFloat'
                     let oper1 = tiBuiltin the___fromfloat__
                         oper2 = tiBuiltin the_complex
                         real = callVariable pos oper1 [make_literal (U.FloatL 0)]
                         imag = callVariable pos oper1 [make_literal (U.FloatL d)]
                     in callVariable pos oper2 [real, imag]
                   BoolLit b -> make_literal $ U.BoolL b
                   NoneLit -> make_literal U.NoneL
       in return l'
     Tuple pos es -> do
       es' <- mapM doExpr es
       return $ U.TupleE (U.Ann pos) es'
     Unary pos op e -> do
       e' <- doExpr e
       return $ callVariable pos (convertUnaryOperator op) [e']
     Binary pos op l r -> do
       l' <- doExpr l
       r' <- doExpr r
       return $ callVariable pos (convertBinaryOperator op) [l', r']
     Subscript pos base index -> do
       base' <- doExpr base
       index' <- doExpr index
       return $ callVariable pos (tiBuiltin the_safeSubscript) [base', index']
     ListComp pos iter -> do
       iter' <- doIterator iter
       -- Currently we have to explicitly insert __build__ where we want it 
       return $ iter' -- callVariable pos (tiBuiltin the___build__) [iter']
     Generator pos iter -> do
       doIterator iter
     Call pos op args -> do
       op' <- doExpr op
       args' <- mapM doExpr args
       return $ U.CallE (U.Ann pos) op' args'
     Cond pos c t f -> do
       c' <- doExpr c
       t' <- doExpr t
       f' <- doExpr f
       return $ U.IfE (U.Ann pos) c' t' f'
     Let pos b rhs body -> do
       rhs' <- doExpr rhs
       convertParameter b $ \b' -> do
         body' <- doExpr body
         return $ U.LetE (U.Ann pos) b' rhs' body'
     Lambda pos params body ->
       convertParameters params $ \params' -> do
         body' <- doExpr body
         let fun = U.Function (U.Ann pos) Nothing params' Nothing body'
         return $ U.FunE (U.Ann pos) fun

doIterator :: SSAIterFor Expr -> Cvt U.Expression
doIterator (IterFor pos params dom body) = do
  dom' <- doExpr dom
  -- Currently we have to explicitly insert __iter__ where we want it
  let iterator = dom' -- callVariable pos (tiBuiltin the___iter__) [dom']
  convertParameters params $ \[param'] ->
    case body
    of CompBody simple_body -> do
         -- When body is a simple expression, convert
         -- "FOO for x in BAR" to map(lambda x. FOO, bar).
         --
         -- This works for a broader range of types than the general case.
         body_expr <- doExpr simple_body
         let body_fun =
               U.Function (U.Ann pos) Nothing [param'] Nothing body_expr
         return $ callVariable pos (tiBuiltin the_map)
           [U.FunE (U.Ann pos) body_fun, iterator]
         
       _ -> do
         -- Convert "FOO for x in BAR" to bind(bar, lambda x. FOO)
         body' <- doComprehension body 
         let body_fun = U.Function (U.Ann pos) Nothing [param'] Nothing body'
         return $ callVariable pos (tiBuiltin the_iterBind)
           [iterator, U.FunE (U.Ann pos) body_fun]

doGuard :: SSAIterIf Expr -> Cvt U.Expression
doGuard (IterIf pos cond body) = do
  -- Convert "FOO if BAR" to guard(BAR, FOO)
  cond' <- doExpr cond
  body' <- doComprehension body
  return $ callVariable pos (tiBuiltin the_guard) [cond', body']

doComprehension (CompFor iter) = doIterator iter
doComprehension (CompIf iter) = doGuard iter
doComprehension (CompBody e) = do
  e' <- doExpr e
  return $ callVariable noSourcePos (tiBuiltin the_do) [e']

doSuite :: [SSAStmt]
        -> ([U.Expression] -> Cvt U.Expression)
        -> Cvt U.Expression
doSuite [] _ = internalError "doSuite: Empty suite"

doSuite [control_stm] consume_result = 
  produceValue control_stm consume_result

doSuite (stm:stms) consume_result =
  doStmt stm $ doSuite stms consume_result

-- | Convert a statement to an expression.  The extra parameter is a
-- computation that converts the part of the AST dominated by this 
-- statement (i.e., the following statements in the same block).
doStmt :: SSAStmt -> Cvt U.Expression -> Cvt U.Expression
doStmt statement rest =
  case statement
  of ExprStmt pos e -> do
       e' <- doExpr e
       body <- rest
       return $ U.LetE (U.Ann pos) (U.WildP (U.Ann noSourcePos)) e' body

     Assign pos lhs rhs -> do
       convertParameter lhs $ \lhs' -> do
         rhs' <- doExpr rhs
         body <- rest
         return $ U.LetE (U.Ann pos) lhs' rhs' body
         
     If pos c t f (Just join_point) -> doIf pos c t f join_point rest
     If _   _ _ _ Nothing           -> internalError "doStmt"
     
     DefGroup pos defs ->
       convertDefGroup defs $ \defs' -> do
         body <- rest
         return $ U.LetrecE (U.Ann pos) defs' body
     
     FallThrough {} -> internalError "doStmt: Unexpected control flow"
     Return {}      -> internalError "doStmt: Unexpected control flow"

doIf pos c t f join_point rest
  | joinReturn join_point == False = do
    -- There is no escaping control flow.  Generate an if-else expression:
    --
    -- > let (x, y) = (if c then t else f) in next
    --
    let return_value live_outs =
          return $ U.TupleE (U.Ann pos) live_outs
    
    c' <- doExpr c
    t' <- doSuite t return_value
    f' <- doSuite f return_value
    let if_expr = U.IfE (U.Ann pos) c' t' f'
               
    consumeValue join_point $ \params -> do
      rest' <- rest
      return $ U.LetE (U.Ann pos) (U.TupleP (U.Ann pos) params) if_expr rest'

  | joinFallthrough join_point == FTOne = do
    -- There is one fallthrough path.  Inline the continuation into
    -- the fallthrough path.
    c' <- doExpr c
           
    -- Bind each live-out variable with a 'let' expression, 
    -- then run the code that follows the if statement
    let make_join live_outs =
          consumeValue join_point $ \pats -> do
            rest' <- rest
            return $ foldr make_let rest' $ zip pats live_outs
                   
        make_let (pat, rhs) body = U.LetE (U.Ann pos) pat rhs body
               
    t' <- doSuite t make_join
    f' <- doSuite f make_join
    return $ U.IfE (U.Ann pos) c' t' f'
  | otherwise = do
    -- Generate a local function for the continuation
    --
    -- > let k (x1, x2 ... xn) = successor
    -- > in if c then t else f
    
    -- Create the continuation function
    cont_var <- newVariable ""
    cont_fun <- consumeValue join_point $ \params -> do
          rest' <- rest
          return $ U.Function (U.Ann pos) Nothing params Nothing rest'

    -- At the end of the if/else branches, call the continuation function
    let make_join live_outs = return $ callVariable pos cont_var live_outs
    c' <- doExpr c
    t' <- doSuite t make_join
    f' <- doSuite f make_join
    
    let if_expr = U.IfE (U.Ann pos) c' t' f'
    return $ U.LetrecE (U.Ann pos) [U.FunctionDef cont_var cont_fun] if_expr

doExport :: ExportItem SSAID -> Cvt U.Export
doExport (ExportItem { exportPos = pos 
                     , exportSpec = spec
                     , exportVar = v
                     , exportType = ty}) = do
  -- Variable must actually be a variable
  vexp <- doVar pos v
  let v' = case vexp
           of U.VariableE {U.expVar = v'} -> v'
              _ -> internalError "doExport"
  
  uty <- doType ty
  return $ U.Export (U.Ann pos) spec v' uty

-- | Generate a list of parameter expressions corresponding to the set of 
-- live-in variables at a control flow join point.
consumeValue :: JoinNode -> ([U.Pattern] -> Cvt a) -> Cvt a
consumeValue (IfJoin {joinPhis = phis}) k =
  withMany consume_phi (Map.toList phis) k
  where
    consume_phi (pvar, Phi assign_version _) =
      convertParameter (Parameter (setVersion pvar assign_version) Nothing)

consumeValue (ReturnJoin {joinPhi = phi}) k = do
  v <- getReturnVar
  k [U.VariableP (U.Ann noSourcePos) v Nothing]

-- | Pass the live-out values of the statement (which must be a control flow
-- transfer statement) to the code that will execute next.  The fall-through
-- path is given as a parameter.
produceValue :: SSAStmt
             -> ([U.Expression] -> Cvt U.Expression)
             -> Cvt U.Expression
produceValue (Return {stmtRhs = e}) _ =
  -- Ignore the fall-through path and return a value.
  doExpr e

produceValue (FallThrough { stmtPos = pos
                          , stmtID = stm_id
                          , stmtSuccessor = succ_ref}) consume_value = do
  -- Get the join point's phi nodes
  msuccessor <- liftIO $ readIORef succ_ref
  successor <- case msuccessor
               of Just s -> return s
                  Nothing ->
                    internalError "produceValue: No control flow information"
  
  -- For each SSA variable, get the corresponding live-out variable
  live_outs <-
    forM (Map.toList $ joinPhis successor) $ \(pvar, Phi _ inputs) ->
    case lookup stm_id inputs
    of Just input_version -> doVar pos (setVersion pvar input_version)
       Nothing -> internalError "produceValue"

  -- Generate the fall-through control flow transfer
  consume_value live_outs

callVariable pos op args =
  U.CallE (U.Ann pos) (U.VariableE (U.Ann pos) op) args

convertUnaryOperator op = 
  case op
  of Python.Minus {} -> tiBuiltin the___negate__
     _ -> internalError "convertUnaryOperator: Unrecognized operator"

convertBinaryOperator op =
  case op
  of Python.Exponent {}          -> tiBuiltin the___power__
     Python.LessThan {}          -> tiBuiltin the___lt__
     Python.GreaterThan {}       -> tiBuiltin the___gt__
     Python.Equality {}          -> tiBuiltin the___eq__
     Python.GreaterThanEquals {} -> tiBuiltin the___ge__
     Python.LessThanEquals {}    -> tiBuiltin the___le__
     Python.NotEquals {}         -> tiBuiltin the___ne__
     Python.Xor {}               -> tiBuiltin the___xor__
     Python.BinaryAnd {}         -> tiBuiltin the___and__
     Python.BinaryOr {}          -> tiBuiltin the___or__
     Python.Multiply {}          -> tiBuiltin the___mul__
     Python.Plus {}              -> tiBuiltin the___add__
     Python.Minus {}             -> tiBuiltin the___sub__
     Python.Divide {}            -> tiBuiltin the___div__
     Python.FloorDivide {}       -> tiBuiltin the___floordiv__
     Python.Modulo {}            -> tiBuiltin the___mod__
     _ -> internalError "convertBinaryOperator: Unrecognized operator"

convertModule :: Module SSAID -> Cvt U.Module
convertModule (Module module_name defss exports) =
  withMany convertDefGroup defss $ \defss' -> do
    exports' <- mapM doExport exports
    return $ U.Module (ModuleName module_name) defss' exports'

convertToUntyped :: [(SSAVar, U.ParserVarBinding)]
                 -> Module SSAID 
                 -> IO U.Module
convertToUntyped predefined_vars mod =
  let global_scope = Map.fromList predefined_vars
  in runReaderT (convertModule mod) (Nothing, global_scope)
