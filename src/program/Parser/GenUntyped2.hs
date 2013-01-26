
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Parser.GenUntyped2
where

import Prelude hiding(mapM, sequence)

import Control.Monad.State hiding(mapM, sequence)
import Control.Monad.RWS hiding(mapM, sequence)
import Control.Monad.Trans
import qualified Compiler.Hoopl as Hoopl
import Data.List
import Data.Traversable
import qualified Data.Map as Map

import qualified Language.Python.Common.AST as Python
import Common.Error
import Common.Label
import Common.Identifier
import Common.SourcePos
import Common.Supply
import Parser.ParserSyntax hiding(Stmt(..))
import Parser.Control
import Parser.SSA2(SSAVar, SSAID, SSATree(..))
import qualified Untyped.Data as U
import Untyped.Builtins2
import qualified Untyped.Syntax as U
import qualified Untyped.TIMonad as U
import qualified Untyped.Type as U
import qualified Untyped.Kind as U
import qualified Untyped.TypeUnif as U
import qualified Untyped.Variable as U
import Type.Level
import qualified Type.Type as Type

-- | A mapping from SSA variable to untyped variable
type GenScope = Map.Map SSAVar ParserVarBinding

externUntypedScope :: [(SSAVar, ParserVarBinding)] -> GenScope
externUntypedScope = Map.fromList

noAnnotation :: U.Ann
noAnnotation = U.Ann noSourcePos

type GenEnv = U.Environment

newtype Gen a = Gen {runGen :: RWST GenEnv () GenScope IO a}
              deriving(Monad, MonadIO)

instance Supplies Gen (Ident Type.Var) where
  fresh = Gen $ do s <- asks U.envSFVarIDSupply
                   liftIO $ supplyValue s

-- | This 'EnvMonad' instance is so that type functions can be evaluated
instance U.EnvMonad Gen where
  getEnvironment = Gen ask
  getsEnvironment f = Gen (asks f)
  withEnvironment f (Gen m) = Gen (local f m)

runGenEnv :: U.Environment -> GenScope -> Gen a -> IO (a, GenScope)
runGenEnv env scope m = do
  (x, s, _) <- runRWST (runGen m) env scope
  return (x, s)

modifyScope :: (GenScope -> GenScope) -> Gen ()
modifyScope f = Gen $ modify f

inLocalScope :: Gen a -> Gen a
inLocalScope (Gen m) = Gen $ do
  s <- get
  x <- m
  put s
  return x

lookupVar' :: (ParserVarBinding -> a) -> SSAVar -> Gen a
lookupVar' f v = do
  env <- Gen get
  return $! case Map.lookup v env
            of Nothing -> internalError "lookupVar: Unknown variable"
               Just v  -> f v

lookupVar = lookupVar' id

lookupKindVar :: SSAVar -> Gen U.Kind
lookupKindVar v = lookupVar' from_kind v
  where
    from_kind (KindBinding k) = k
    from_kind _ = internalError "lookupKindVar: Not a kind"

lookupTypeVar :: SSAVar -> Gen U.TyCon
lookupTypeVar v = lookupVar' from_type v
  where
    from_type (TypeBinding t) = t
    from_type _ = internalError "lookupTypeVar: Not a type"
    
lookupObjVar :: SSAVar -> Gen U.Variable
lookupObjVar v = lookupVar' from_obj v
  where
    from_obj (ObjectBinding t) = t
    from_obj _ = internalError "lookupObjVar: Not a value"

lookupObjVarAsExpression :: U.Ann -> SSAVar -> Gen U.Expression
lookupObjVarAsExpression ann v = do
  v' <- lookupObjVar v
  return $ U.VariableE ann v'

-- | Translate an SSA variable to a fresh untyped variable
createNewObjectVariable :: String -> Gen U.Variable
createNewObjectVariable name = do
  sfvar_id <- fresh
  let sfvar = Just $ Type.mkVar sfvar_id p_label ObjectLevel
  liftIO $ U.newVariable u_label sfvar
  where
    (u_label, p_label) =
      if null name
      then (Nothing, Nothing)
      else (Just $ plainLabel (ModuleName "trioletfile") name,
            Just $ plainLabel (ModuleName "trioletfile") name)

defineVar :: SSAVar -> Gen U.Variable
defineVar v = do
  v' <- createNewObjectVariable (varName v)
  modifyScope $ Map.insert v (ObjectBinding v')
  return v'

defineTyVar :: SSAVar -> U.Kind -> Gen U.TyCon
defineTyVar v kind = do
  -- Create a type variable
  let lab = case varName v
            of "" -> Nothing
               nm -> Just $ plainLabel (ModuleName "trioletfile") nm
  tyvar <- U.newTyVar lab kind
  modifyScope $ Map.insert v (TypeBinding tyvar)
  return tyvar
    
-------------------------------------------------------------------------------
-- Kind translation

kind :: LExpr SSAID -> Gen U.Kind
kind expr =
  case unLoc expr
  of Binary (Python.Arrow {}) l r ->
       (U.:->) `liftM` kind l `ap` kind r
     Variable v ->
       lookupKindVar v

-------------------------------------------------------------------------------
-- Type translation

-- | Translate a function domain, which is 'None', a single type, 
-- or a product of types.
funDomain :: LExpr SSAID -> Gen [U.HMType]
funDomain e = typeExps $ from_product e
  where
    -- Multiplication is left-associative, but we want a
    -- right-associative expression.  Thus, we build and then reverse a list. 
    from_product (Loc _ (Literal NoneLit)) = []
    from_product xs = reverse $ from_product' xs

    from_product' (Loc _ (Binary (Python.Multiply {}) l r)) =
      r : from_product' l
    from_product' e = [e]

typeExps es = mapM typeExp es

typeExp :: LExpr SSAID -> Gen U.HMType
typeExp (Loc pos e) =
  case e
  of Variable v ->
       U.ConTy `liftM` lookupTypeVar v
     Binary (Python.Arrow {}) l r ->
       U.functionTy `liftM` funDomain l `ap` typeExp r
     Tuple ts ->
       U.tupleTy `liftM` typeExps ts
     Call (Loc _ (Variable op_v)) args -> do
       -- Special case handling of type functions
       con <- lookupTypeVar op_v
       args' <- typeExps args
       return $ U.appTyCon con args'
     Call op args -> do
       op' <- typeExp op
       args' <- typeExps args
       return $ U.appTys op' args'

-------------------------------------------------------------------------------
-- Expression translation

-- | Create a pattern matching a value of type 'NoneType'.  The variable is
--   ignored.
noneTypePattern :: Gen [U.Pattern]
noneTypePattern = do
  v <- createNewObjectVariable ""
  return [U.VariableP noAnnotation v (Just nonetype)]
  where
    nonetype = U.ConTy $ builtinTyCon TheTC_NoneType

callVariable pos op args =
  U.CallE (U.Ann pos) (U.VariableE (U.Ann pos) op) args

withForallAnnotation :: ForallAnnotation SSAID
                     -> ([U.TyCon] -> Gen a) -> Gen a
withForallAnnotation ann k = inLocalScope $ do
  k =<< mapM forall_var ann
  where
    forall_var (v, kind_ann) = do
      -- Determine the variable's kind; default is 'Star'
      kind <- maybe (return U.Star) kind kind_ann

      -- Create a type variable
      defineTyVar v kind

withMaybeForallAnnotation Nothing k = k Nothing
withMaybeForallAnnotation (Just a) k = withForallAnnotation a $ k . Just

withParameter :: Parameter SSAID -> (U.Pattern -> Gen a) -> Gen a
withParameter param k = inLocalScope $ parameter param >>= k

withParameters :: [Parameter SSAID] -> ([U.Pattern] -> Gen a) -> Gen a
withParameters params k = inLocalScope $ parameters params >>= k

parameters xs = mapM parameter xs

parameter (Parameter v ann) = do
  ann' <- mapM typeExp ann
  v' <- defineVar v
  return $ U.VariableP noAnnotation v' ann'

parameter (TupleParam ps) = do
  ps' <- mapM parameter ps
  return $ U.TupleP noAnnotation ps'

defGroup :: [LCFunc SSAID] -> Gen [U.FunctionDef]
defGroup defs = do
  -- Convert all function names
  fun_names <- mapM defineVar $ map (sigName . cfSignature . unLoc) defs

  -- Convert function bodies
  zipWithM functionDef fun_names defs

literal :: SourcePos -> Literal -> U.Expression
literal pos l = 
  case l
  of IntLit n ->
       -- Generate a call to 'fromInt' to cast to any valid value
       let oper = builtinVar TheV___fromint__
       in callVariable pos oper [make_literal (U.IntL n)]
     FloatLit f ->
       -- Generate a call to 'fromFloat' to cast to any valid value
       let oper = builtinVar TheV___fromfloat__
       in callVariable pos oper [make_literal (U.FloatL f)]
     ImaginaryLit d ->
       internalError "Imaginary numbers not supported"
       {-
       -- Generate a call to 'makeComplex' and 'fromFloat'
       let oper1 = builtinVar TheV___fromfloat__
           oper2 = builtinVar TheV_complex
           real = callVariable pos oper1 [make_literal (U.FloatL 0)]
           imag = callVariable pos oper1 [make_literal (U.FloatL d)]
       in callVariable pos oper2 [real, imag]-}
     BoolLit b -> make_literal $ U.BoolL b
     NoneLit -> make_literal U.NoneL
  where
    make_literal l = U.LiteralE (U.Ann pos) l

exprs = mapM expr

expr :: LExpr SSAID -> Gen U.Expression
expr (Loc pos e) =
  case e
  of Variable v ->
       lookupObjVarAsExpression (U.Ann pos) v
     Literal l ->
       return $ literal pos l
     Tuple es ->
       U.TupleE (U.Ann pos) `liftM` exprs es
     List es ->
       U.ListE (U.Ann pos) `liftM` exprs es
     Unary op e -> do
       e' <- expr e
       let op' = convertUnaryOperator op
       return $ callVariable pos op' [e']
     Binary op e1 e2 -> do
       e1' <- expr e1
       e2' <- expr e2
       let op' = convertBinaryOperator op
       return $ callVariable pos op' [e1', e2']
     Subscript base indices -> do
       base' <- expr base
       indices' <- exprs indices
       let index_expr =
             case indices'
             of [i] -> i
                is  -> U.TupleE (U.Ann pos) is
       return $ callVariable pos (builtinVar TheV___getitem__) [base', index_expr]
     Slicing base subs -> do
       base' <- expr base
       subs' <- mapM slice subs
       let slice_expr =
             case subs'
             of [i] -> i
                is  -> U.TupleE (U.Ann pos) is
       return $ callVariable pos (builtinVar TheV___getslice__) [base', slice_expr]
     ListComp iter -> do
       iter' <- iterator iter
       return $ callVariable pos (builtinVar TheV_build) [iter']
     Generator iter ->
       iterator iter
     Call e es ->
       U.CallE (U.Ann pos) `liftM` expr e `ap` exprs es
     Cond c t f ->
       U.IfE (U.Ann pos) `liftM` expr c `ap` expr t `ap` expr f
     Let b rhs body -> do
       rhs' <- expr rhs
       withParameter b $ \b' -> do
         body' <- expr body
         return $ U.LetE (U.Ann pos) b' rhs' body'
     Lambda params body ->
       withParameters params $ \params' -> do
         body' <- expr body
         let fun = U.Function (U.Ann pos) Nothing params' Nothing body'
         return $ U.FunE (U.Ann pos) fun

slice (SliceSlice pos l u s) = do
  (has_l, l') <- maybe_expr expr zero l
  (has_u, u') <- maybe_expr expr zero u
  (has_has_s, (has_s, s')) <-
    maybe_expr (maybe_expr expr zero) (false, zero) s
  return $ callVariable pos (builtinVar TheV_make_sliceObject)
    [has_l, l', has_u, u', has_has_s, has_s, s']
  where
    maybe_expr :: (a -> Gen b) -> b -> Maybe a -> Gen (U.Expression, b)
    maybe_expr translate _ (Just e) = do
      e' <- translate e
      return (true, e')
    
    maybe_expr _ default_value Nothing =
      return (false, default_value)

    true = U.LiteralE (U.Ann pos) (U.BoolL True)
    false = U.LiteralE (U.Ann pos) (U.BoolL False)
    zero = U.LiteralE (U.Ann pos) (U.IntL 0)

slice (ExprSlice e) = do
  e' <- expr e
  v <- createNewObjectVariable ""
  let l = U.VariableE noAnnotation v
      u = callVariable noSourcePos (builtinVar TheV___add__) [l, one]
      s = callVariable noSourcePos (builtinVar TheV_make_sliceObject)
          [true, l, true, u, false, false, zero]
  return $ U.LetE noAnnotation (U.VariableP noAnnotation v Nothing) e' s
  where
    true = U.LiteralE (U.Ann noSourcePos) (U.BoolL True)
    false = U.LiteralE (U.Ann noSourcePos) (U.BoolL False)
    zero = U.LiteralE (U.Ann noSourcePos) (U.IntL 0)
    one = U.LiteralE (U.Ann noSourcePos) (U.IntL 1)

iterator (IterFor pos params source body) = do
  source' <- expr source
  let iterator = callVariable pos (builtinVar TheV_iter) [source']
  withParameters params $ \[param'] ->
    case body
    of CompBody simple_body -> do
         -- When body is a simple expression, convert
         -- "FOO for x in BAR" to map(lambda x. FOO, bar).
         --
         -- This works for a broader range of types than the general case.
         body_expr <- expr simple_body
         let body_fun =
               U.Function (U.Ann pos) Nothing [param'] Nothing body_expr
         return $ callVariable pos (builtinVar TheV_map)
           [U.FunE (U.Ann pos) body_fun, iterator]
    
       _ -> do
         -- Convert "FOO for x in BAR" to bind(bar, lambda x. FOO)
         body' <- comprehension body 
         let body_fun = U.Function (U.Ann pos) Nothing [param'] Nothing body'
         return $ callVariable pos (builtinVar TheV_iterBind)
           [iterator, U.FunE (U.Ann pos) body_fun]

iterIf (IterIf pos cond body) = do
  -- Convert "FOO if BAR" to guard(BAR, FOO)
  cond' <- expr cond
  body' <- comprehension body
  return $ callVariable pos (builtinVar TheV_guard) [cond', body']

iterLet (IterLet pos target rhs body) = do
  rhs' <- expr rhs
  withParameter target $ \target' -> do
    body' <- comprehension body
    return $ U.LetE (U.Ann pos) target' rhs' body'

comprehension (CompFor iter) = iterator iter
comprehension (CompIf iter) = iterIf iter
comprehension (CompLet iter) = iterLet iter
comprehension (CompBody e) = do
  e' <- expr e
  return $ callVariable noSourcePos (builtinVar TheV_do) [e']

convertUnaryOperator op = 
  case op
  of Python.Minus {} -> builtinVar TheV___negate__
     Python.Not {} -> builtinVar TheV_not
     _ -> internalError "convertUnaryOperator: Unrecognized operator"

convertBinaryOperator op =
  case op
  of Python.And {}               -> builtinVar TheV_and
     Python.Or {}               -> builtinVar TheV_or
     Python.Exponent {}          -> builtinVar TheV___power__
     Python.LessThan {}          -> builtinVar TheV___lt__
     Python.GreaterThan {}       -> builtinVar TheV___gt__
     Python.Equality {}          -> builtinVar TheV___eq__
     Python.GreaterThanEquals {} -> builtinVar TheV___ge__
     Python.LessThanEquals {}    -> builtinVar TheV___le__
     Python.NotEquals {}         -> builtinVar TheV___ne__
     Python.Xor {}               -> builtinVar TheV___xor__
     Python.BinaryAnd {}         -> builtinVar TheV___and__
     Python.BinaryOr {}          -> builtinVar TheV___or__
     Python.Multiply {}          -> builtinVar TheV___mul__
     Python.Plus {}              -> builtinVar TheV___add__
     Python.Minus {}             -> builtinVar TheV___sub__
     Python.Divide {}            -> builtinVar TheV___div__
     Python.FloorDivide {}       -> builtinVar TheV___floordiv__
     Python.Modulo {}            -> builtinVar TheV___mod__
     Python.ShiftLeft {}         -> builtinVar TheV___lshift__
     Python.ShiftRight {}        -> builtinVar TheV___rshift__
     _ -> internalError "convertBinaryOperator: Unrecognized operator"

-------------------------------------------------------------------------------
-- Function translation

type BlockMap = Hoopl.LabelMap U.Variable

-- | During function translation, keep a mapping from labels to local function
--   names.  All blocks except the entry point are added to the map.
type FGen a = StateT BlockMap Gen a

-- | An expression with a hole in it
type MkExpression = U.Expression -> U.Expression

type BodyStmt = LStmt SSAID Hoopl.O Hoopl.O
type FlowStmt = LStmt SSAID Hoopl.O Hoopl.C

defineLabel :: Hoopl.Label -> FGen U.Variable
defineLabel lab = StateT $ \s -> do 
  v <- createNewObjectVariable ""
  let s' = Hoopl.mapInsert lab v s
  return (v, s')

lookupLabel :: Hoopl.Label -> FGen U.Variable
lookupLabel lab = StateT $ \s ->
  case Hoopl.mapLookup lab s
  of Just v  -> return (v, s)
     Nothing -> internalError "lookupLabel"

-- | Run a computation without exposing its modifications to the scope.
--   Both variable definitions and label definitions are hidden.
inLocalLabelScope :: FGen a -> FGen a
inLocalLabelScope (StateT m) = StateT $ \s -> do
  (x, _) <- inLocalScope (m s)
  return (x, s)

-- | Begin translating a function body.  The block map is initially empty.
enterBody :: FGen a -> Gen a
enterBody m = evalStateT m Hoopl.mapEmpty

-- | Begin translating a subexpression that doesn't involve labels 
leaveBody :: Gen a -> FGen a
leaveBody = lift

-- | Translate a function definition
functionDef :: U.Variable -> LCFunc SSAID -> Gen U.FunctionDef
functionDef func_name (Loc pos func) =
  -- Convert type parameters
  withMaybeForallAnnotation ann $ \qvars -> do
    ret_type <- mapM typeExp r_ann
    -- Convert parameters
    withParameters params $ \u_params -> do
      -- Convert body
      body <- enterBody $ ssaTreeExp (cfBody func)
      let annotation = U.FunctionAnn (funInline pragma)
          function = U.Function (U.Ann pos) qvars u_params ret_type body
      return $ U.FunctionDef func_name annotation function
  where
    FunSig _ ann pragma params r_ann = cfSignature func

-- | Translate a dominator tree into an expression.
--   Child nodes are translated to letrec-defined functions.
ssaTreeExp :: SSATree SSAID -> FGen U.Expression
ssaTreeExp (SSATree block children) = do
  let (_, statements, Hoopl.JustC last) = Hoopl.blockToNodeList block
  ssaBlock statements last children

ssaBlock statements last children = do
  exprs <- leaveBody $ mapM stmt statements
  local_blocks <- ssaTreeChildren children
  tail <- ssaTail last

  -- Build an expression from these pieces
  return $ foldr ($) (local_blocks tail) exprs

-- | Translate dominator tree children to local functions
ssaTreeChildren :: [[SSATree SSAID]] -> FGen MkExpression

-- No children translate to nothing
ssaTreeChildren [] = return id  

ssaTreeChildren (g:gs) = do
  g' <- ssaTreeChildGroup g
  gs' <- ssaTreeChildren gs
  return (g' . gs')

ssaTreeChildGroup children = do
  -- Define a label for each target
  target_vars <- mapM defineLabel target_labels

  -- Convert children to function definitions
  children' <- sequence $
               zipWith5 ssaTreeChild target_vars target_params
               middles lasts child_subtrees

  -- Create a letrec expression
  return $ U.LetrecE noAnnotation children'
  where
    (target_labels, target_params, middles, lasts, child_subtrees) =
      unzip5 [(label, params, m, l, t)
             | SSATree b t <- children
             , let (Hoopl.JustC f, m, Hoopl.JustC l) =
                     Hoopl.blockToNodeList b
             , let LStmt (Loc _ (Target label (Just params))) = f]

-- | Translate a subtree to a local function
ssaTreeChild :: U.Variable -> [SSAVar] -> [BodyStmt] -> FlowStmt
             -> [[SSATree SSAID]] -> FGen U.FunctionDef
ssaTreeChild var params middle last children = inLocalLabelScope $ do
  -- Translate phi parameters to variables.
  -- There must be at least one parameter.
  patterns <-
    leaveBody $ if null params
                then noneTypePattern
                else do ps <- mapM defineVar params
                        return [U.VariableP noAnnotation p Nothing | p <- ps]

  -- Translate block to a function body
  body <- ssaBlock middle last children

  -- Create function
  let function = U.Function noAnnotation Nothing patterns Nothing body
  return $ U.FunctionDef var (U.FunctionAnn False) function

ssaTail :: FlowStmt -> FGen U.Expression
ssaTail (LStmt (Loc pos s)) =
  case s
  of If cond t f -> do
       cond' <- leaveBody $ expr cond
       t_call <- ssaFlow pos t
       f_call <- ssaFlow pos f
       return $ U.IfE ann cond' t_call f_call
     Jump f -> do
       ssaFlow pos f
     Return e -> do
       leaveBody $ expr e
  where
    ann = U.Ann pos

-- | Translate control flow to a function call
ssaFlow :: SourcePos -> Flow SSAID -> FGen U.Expression
ssaFlow pos (Flow label (Just args)) = do
  callee_var <- lookupLabel label
  let callee = U.VariableE (U.Ann pos) callee_var

  -- Must pass at least one argument
  arguments <-
    if null args
    then return [U.LiteralE (U.Ann pos) U.NoneL]
    else leaveBody $ mapM (lookupObjVarAsExpression (U.Ann pos)) args

  return $ U.CallE (U.Ann pos) callee arguments

stmt :: BodyStmt -> Gen MkExpression
stmt (LStmt (Loc pos s)) =
  case s
  of Assign param rhs -> do
       rhs' <- expr rhs
       param' <- parameter param
       return $ U.LetE ann param' rhs'
     DefGroup defs _ -> do
       defs' <- defGroup defs
       return $ U.LetrecE ann defs'
     Assert es -> do
       -- Translate to "if e then ... else __undefined__"
       es' <- mapM expr es
       let make_if test e = U.IfE ann test e (U.UndefinedE ann)
       return $ \body -> foldr make_if body es'
     Require v e -> do
       v' <- lookupObjVar v
       e' <- typeExp e
       return $ U.TypeAssertE ann v' e'
  where
    ann = U.Ann pos

export :: ExportItem SSAID -> Gen U.Export
export (ExportItem pos spec v ty) = do
  v' <- lookupObjVar v
  ty' <- typeExp ty
  return $ U.Export (U.Ann pos) spec v' ty'

genGroup :: U.Environment -> GenScope -> [LCFunc SSAID]
         -> IO (U.DefGroup, GenScope)
genGroup env scope xs =
  runGenEnv env scope $ defGroup xs

genExport :: U.Environment -> GenScope -> ExportItem SSAID
          -> IO (U.Export, GenScope)
genExport env scope x = 
  runGenEnv env scope $ export x
