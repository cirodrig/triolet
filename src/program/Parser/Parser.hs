{- AST parsing and name resolution.
--
-- The exported parsing functions in this module first call the
-- Language.Python parser, then apply name resolution rules to
-- assign variables a globally unique ID.
--
-- Some errors related to name resolution, such as undefined variable
-- names and redefinitions of parameter variables, are detected here. 
-}

{-# LANGUAGE FlexibleInstances #-}
module Parser.Parser(convertStatement, convertModule, parseModule)
where

import Prelude hiding(mapM, sequence)

import Control.Applicative
import Control.Monad hiding(mapM, sequence)
import Data.Function
import qualified Data.Graph.Inductive as Graph
import qualified Data.Graph.Inductive.Query.DFS as Graph
import Data.List
import Data.Maybe
import Data.Map(Map)
import qualified Data.Map as Map
import Data.Set(Set)
import qualified Data.Set as Set
import Data.Traversable

import qualified Language.Python.Version3.Parser as Py
import qualified Language.Python.Common.AST as Py
import qualified Language.Python.Common.Pretty as Py
import qualified Language.Python.Common.SrcLocation as Py
import Language.Python.Common.PrettyAST()
import PythonInterface.Python(PyPtr)
import Parser.ParserSyntax

import Gluon.Common.SourcePos(SourcePos, noSourcePos, fileSourcePos)

toSourcePos :: Py.SrcSpan -> SourcePos
toSourcePos pos =
  fileSourcePos (Py.span_filename pos) (Py.startRow pos) (Py.startCol pos)

type PyIdent = Py.IdentSpan

data Binding =
    Local                       -- A locally defined variable
    { bIsDef :: Bool
    , bName  :: Var
    }
  | Param                       -- A variable defined as a function parameter
    { bIsDef :: Bool            -- Always true
    , bName  :: Var
    }
  | Nonlocal                    -- A nonlocal variable (indicated by a keyword)
    { bIsDef :: Bool
    }
  | Global                      -- A global variable (indicated by a keyword)
    { bIsDef :: Bool
    }
    deriving(Show)

-- A map from variable names to bindings
type Bindings = Map.Map String Binding

-- List of predefined variables.  Each variable's name, ID, and Python object
-- is given.  The PyPtr values are borrowed references.
type PredefinedVars = [(String, Int, PyPtr)]

-- Given a binding and the set of nonlocal uses and defs, produce scope
-- information for the variable.
toScopeVar :: NameSet -> NameSet -> Binding -> Maybe ScopeVar
toScopeVar nonlocalUses nonlocalDefs binding =
    case binding
    of Local _ v  -> Just $ toVar False v
       Param _ v  -> Just $ toVar True  v
       Nonlocal _ -> Nothing
       Global _   -> Nothing
    where
      toVar isParam v =
          let use = varName v `Set.member` nonlocalUses
              def = varName v `Set.member` nonlocalDefs
          in ScopeVar
                 { scopeVar       = v
                 , isParameter    = isParam
                 , hasNonlocalUse = use || def
                 , hasNonlocalDef = def
                 }

-- Given a binding at global scope, produce scope information.
-- Global variables are always assumed to be nonlocally used and modified.
toGlobalScopeVar :: Binding -> Maybe ScopeVar
toGlobalScopeVar binding =
    case binding
    of Local _ v  -> Just $ ScopeVar { scopeVar = v
                                     , isParameter = False
                                     , hasNonlocalUse = True
                                     , hasNonlocalDef = True
                                     }
       Param _ v  -> error "Unexpected parameter variable at global scope"
       Nonlocal _ -> Nothing      -- Error, will be reported if there are any
                                 -- defs or uses of the variable
       Global _   -> error "Unexpected 'global' declaration at global scope" 

-- A name resolution scope.
-- The value of 'finalMembers' is the value of 'currentMembers' after the
-- scope is fully processed. 
data Scope =
    Scope { finalMembers   :: Bindings
          , currentMembers :: !Bindings
          }
    deriving(Show)

-- A stack of scopes.
type Scopes = [Scope]

emptyScope :: Scopes
emptyScope = []

-- A set of variable names
type NameSet = Set.Set String

-- Some errors are generated lazily
type Err = String
type Errors = [Err] -> [Err]

noError :: Errors
noError = id

oneError :: Err -> Errors
oneError = (:)

identName id = Py.ident_string id

-------------------------------------------------------------------------------
-- The process of converting to a Pyon AST.
--
-- Keeps track of the current context and thread a name supply through the
-- computation.
-- Computation may fail.
-- Computation may also lazily generate errors, which are stored in a list.

data CvtState = S !Int !Scopes Errors

newtype Cvt a = Cvt {run :: CvtState -> Cvt' a}

-- Running a Cvt returns a new state,
-- the free variable references that were used but not def'd in the conversion,
-- the free variable references that were def'd in the conversion,
-- and a return value.
data Cvt' a = OK { state       :: !CvtState
                 , uses        :: NameSet
                 , defs        :: NameSet
                 , returnValue :: a
                 }
            | Fail String

-- Add some uses and defs to the output of a cvt step
joinCvtResults :: NameSet -> NameSet -> Cvt a -> Cvt a
joinCvtResults u d m = Cvt $ \s ->
    case run m s
    of OK s' u2 d2 x    -> OK s' (Set.union u u2) (Set.union d d2) x
       failure@(Fail _) -> failure

ok :: CvtState -> a -> Cvt' a
ok s x = OK s Set.empty Set.empty x

instance Monad Cvt where
    return x = Cvt $ \s -> OK s Set.empty Set.empty x
    fail msg = Cvt $ \_ -> Fail msg
    m >>= k  = Cvt $ \s -> case run m s
                           of OK s' u1 d1 x -> run (joinCvtResults u1 d1 (k x)) s'
                              Fail msg      -> Fail msg

instance Functor Cvt where
    fmap f m = Cvt $ \s -> case run m s
                           of OK s' u d x -> OK s' u d (f x)
                              Fail msg    -> Fail msg

instance Applicative Cvt where
    pure  = return
    (<*>) = ap

-- Run a computation in a nested scope.  This adds a scope to the stack at
-- the beginning of the computation and removes it at the end.
--
-- The 'Locals' parameter is the set of local variables for this scope.
-- It must not be used strictly.
--
-- We do things slightly differently at global scope, since there's no next
-- scope to propagate to.
enter_ :: Bool -> (Locals -> Cvt a) -> Cvt a
enter_ isGlobalScope f = Cvt $ \initialState ->
    let -- Run the local computation in a modified environment
        (final, localUses, localDefs, result) =
            case run (f locals) $ addNewScope final initialState
            of OK finalState localUses localDefs x ->
                   let (final, finalState') = removeNewScope finalState
                   in (final, localUses, localDefs, Right (finalState', x))
               Fail str ->
                   (Map.empty, Set.empty, Set.empty, Left str)

        -- The local variables are the 'Local' and 'Param' bindings from the
        -- scope
        convertToScopeVar =
            if isGlobalScope
            then toGlobalScopeVar
            else toScopeVar localUses localDefs
        locals = Locals $ mapMaybe convertToScopeVar $ Map.elems final

        -- Nonlocal variables, plus uses that are not satisfied locally,
        -- propagate upward
        boundHere = Set.fromList $ mapMaybe localBindingName $ Map.elems final
        usesNotBoundHere = Set.fromList $
                           Map.keys $
                           Map.filter isNonlocalUse final
        defsNotBoundHere = Set.fromList $
                           Map.keys $
                           Map.filter isNonlocalDef final
        nonlocalUses = Set.union
                       (localUses `Set.difference` boundHere)
                       usesNotBoundHere
        nonlocalDefs = Set.union
                       (localDefs `Set.difference` boundHere)
                       defsNotBoundHere
    in case result
       of Right (finalState, resultValue) ->
              OK finalState nonlocalUses nonlocalDefs resultValue
          Left str -> Fail str
    where
      -- Put a new scope on the stack.  The new scope contains the final value
      -- of its dictionary.
      addNewScope finalScope (S ns scopes errs) =
          S ns (Scope finalScope Map.empty : scopes) errs

      -- Remove the scope at the top of the stack.
      -- Save its final dictionary, which will be inserted when the scope was
      -- created.
      removeNewScope (S ns (Scope _ finalScope : scopes) errs) =
          (finalScope, S ns scopes errs)

      localBindingName (Local _ v) = Just $ varName v
      localBindingName (Param _ v) = Just $ varName v
      localBindingName _           = Nothing

      isNonlocalUse (Nonlocal False) = True
      isNonlocalUse _                = False

      isNonlocalDef (Nonlocal True) = True
      isNonlocalDef _               = False

enter = enter_ False
enterGlobal = enter_ True

withScopes :: (Scopes -> (a, Errors)) -> Cvt a
withScopes f = Cvt $ \(S ns scopes errs) ->
                         let (x, errs') = f scopes
                         in ok (S ns scopes (errs' . errs)) x

updateScopes :: (Scopes -> (Scopes, Errors)) -> Cvt ()
updateScopes f = Cvt $ \(S ns scopes errs) ->
                           let (scopes', errs') = f scopes
                           in ok (S ns scopes' (errs' . errs)) ()

newID :: Cvt Int
newID = Cvt $ \(S n s errs) -> ok (S (n+1) s errs) n

logErrors :: Errors -> Cvt ()
logErrors es = Cvt $ \(S ns scopes errs) -> ok (S ns scopes (es . errs)) ()

logError :: Maybe Err -> Cvt ()
logError e = logErrors (toErrors e)
    where
      toErrors Nothing  = noError
      toErrors (Just e) = oneError e

runAndGetErrors :: Cvt a -> Int -> (Int, Either [String] a)
runAndGetErrors m nextName =
    case run m (S nextName emptyScope noError)
    of Fail msg -> (nextName, Left [msg])
       OK (S nextName' _ errs) _ _ x ->
           case errs []
           of [] -> (nextName', Right x)
              xs -> (nextName', Left xs)

-------------------------------------------------------------------------------
-- Low-level editing of bindings

-- Look up a variable in the environment.  The result must be used lazily.
lookupVar :: PyIdent -> Cvt Var
lookupVar name = withScopes $ \s -> lookup s
    where
      lookup (s:ss) = case Map.lookup (identName name) $ finalMembers s
                      of Just (Local _ v) -> (v, noError)
                         Just (Param _ v) -> (v, noError)
                         _                -> lookup ss

      lookup [] = (noVariable, oneError msg)

      msg = "Undefined variable '" ++ identName name ++ "'"

      noVariable = error "Invalid variable due to parse error"

-- Look up a binding in the current, incomplete local scope.
lookupCurrentLocalBinding :: PyIdent -> Cvt (Maybe Binding)
lookupCurrentLocalBinding name =
    withScopes $ \s -> (lookup (head s), noError)
    where
      lookup s = Map.lookup (identName name) $ currentMembers s

-- Insert or modify a binding
addLocalBinding :: PyIdent -> Binding -> Cvt ()
addLocalBinding name binding =
    updateScopes $ \s -> (addBinding s, noError)
    where
      addBinding (s:ss) = addBindingToScope s : ss

      addBindingToScope s =
        s {currentMembers = Map.insert (identName name) binding $
                            currentMembers s}

-- Insert a binding with the specified ID.  This should only be used at
-- global scope before parsing a module.
defineGlobal :: (String, Int, PyPtr) -> Cvt ()
defineGlobal (nm, id, python_var) =
  let v = makePredefinedVar nm id python_var
      binding = Local True v
  in addLocalBinding (Py.Ident nm Py.SpanEmpty) binding

defineGlobals xs = mapM_ defineGlobal xs

-- Indicate that a definition was seen
signalDef :: PyIdent -> Cvt ()
signalDef id = Cvt $ \s -> OK s Set.empty (Set.singleton $ identName id) ()

-- Indicate that a use was seen
signalUse :: PyIdent -> Cvt ()
signalUse id = Cvt $ \s -> OK s (Set.singleton $ identName id) Set.empty ()

-------------------------------------------------------------------------------
-- High-level editing of bindings

-- Record that a binding has a definition 
markAsDefinition :: PyIdent -> Binding -> Cvt ()
markAsDefinition name b
    | bIsDef b = return ()
    | otherwise = addLocalBinding name (b {bIsDef = True})

-- Create a new variable from an identifier.
-- This is different from all other variables created by newVar.
newVar :: PyIdent -> Cvt Var
newVar id = makeVar (identName id) <$> newID

-- Process a definition of an identifier.  Return the corresponding variable,
-- which must be used lazily.
definition :: PyIdent -> Cvt Var
definition name = do
  signalDef name
  -- Insert a new binding if appropriate
  mb <- lookupCurrentLocalBinding name
  case mb of
    Just b  -> markAsDefinition name b
    Nothing -> do v' <- newVar name
                  addLocalBinding name (Local True v')

  -- Look up the actual binding for this variable.
  -- The binding that was inserted may not be the actual binding.
  lookupVar name

-- Process a parameter definition.
-- Unlike ordinary definitions, parameters cannot be redefined.
-- Return the corresponding variable.
parameterDefinition :: PyIdent -> Cvt Var
parameterDefinition name = do
  signalDef name
  mb <- lookupCurrentLocalBinding name
  case mb of
    Just _  -> parameterRedefined name
    Nothing -> do v <- newVar name
                  addLocalBinding name (Param True v)
                  return v

parameterRedefined :: PyIdent -> Cvt a
parameterRedefined name =
    let msg = "Parameter variable '" ++ identName name ++ "' redefined"
    in fail msg

-- Record that a variable is globally or nonlocally defined.  If this
-- conflicts with an existing definition, report an error.
globalDeclaration, nonlocalDeclaration :: PyIdent -> Cvt ()
globalDeclaration name = do
  b <- lookupCurrentLocalBinding name
  case b of
    Just (Local isDef v) -> -- override local binding
                            addLocalBinding name (Global isDef)
    Just (Param _ _)   -> parameterRedefined name
    Just (Nonlocal _)  -> fail msg
    Just (Global _)    -> return () -- no change
    Nothing            -> addLocalBinding name (Global False)
    where
      msg = "Variable '" ++ identName name ++ "' cannot be declared both global and nonlocal"

nonlocalDeclaration name = do
  b <- lookupCurrentLocalBinding name
  case b of
    Just (Local isDef v) -> -- override local binding
                            addLocalBinding name (Nonlocal isDef)
    Just (Param _ _)  -> parameterRedefined name
    Just (Nonlocal _) -> return () -- no change
    Just (Global _)   -> fail message
    Nothing           -> addLocalBinding name (Nonlocal False)
    where
      message = "Variable '" ++ identName name ++ "' cannot be declared both global and nonlocal"

-- Look up a use of a variable
use name = do
  signalUse name
  lookupVar name

-------------------------------------------------------------------------------
-- Conversions for Python 3 Syntax

type PyExpr = Py.ExprSpan
type PyStmt = Py.StatementSpan
type PyComp a = Py.ComprehensionSpan a

expression :: PyExpr -> Cvt Expr
expression expr =
    case expr
    of Py.Var {Py.var_ident = ident} -> 
         Variable source_pos <$> use ident
       Py.Int {Py.int_value = n} -> 
         pure (Literal source_pos (IntLit n))
       Py.Float {Py.float_value = d} ->
         pure (Literal source_pos (FloatLit d))
       Py.Bool {Py.bool_value = b} ->
         pure (Literal source_pos (BoolLit b))
       Py.None {} -> 
         pure(Literal source_pos NoneLit)
       Py.Tuple {Py.tuple_exprs = es} -> 
         Tuple source_pos <$> traverse expression es
       Py.Call {Py.call_fun = f, Py.call_args = xs} -> 
         Call source_pos <$> expression f <*> traverse argument xs
       Py.CondExpr { Py.ce_true_branch = tr
                   , Py.ce_condition = c
                   , Py.ce_false_branch = fa} -> 
         let mkCond tr c fa = Cond source_pos c tr fa
         in mkCond <$> expression tr <*> expression c <*> expression fa
       Py.BinaryOp { Py.operator = op
                   , Py.left_op_arg = l
                   , Py.right_op_arg = r} -> 
         Binary source_pos op <$> expression l <*> expression r
       Py.UnaryOp {Py.operator = op, Py.op_arg = arg} -> 
         Unary source_pos op <$> expression arg
       Py.Lambda {Py.lambda_args = args, Py.lambda_body = body} -> 
         enter $ \_ -> Lambda source_pos <$> traverse parameter args 
                                         <*> expression body

       -- Generators and list comprehensions have a separate scope
       Py.Generator {Py.gen_comprehension = comp} -> 
         enter $ \locals -> Generator source_pos locals <$> 
                            comprehension expression comp
       Py.ListComp {Py.list_comprehension = comp} -> 
         enter $ \locals -> ListComp source_pos <$>
                            comprehension expression comp
                            
       Py.Paren {Py.paren_expr = e} -> expression e
       _ -> fail $ "Cannot translate expression:\n" ++ Py.prettyText expr
    where
      source_pos = toSourcePos $ Py.expr_annot expr

-- Convert an optional expression into an expression or None
maybeExpression :: SourcePos -> Maybe PyExpr -> Cvt Expr
maybeExpression _   (Just e) = expression e
maybeExpression pos Nothing  = pure (noneExpr pos)

comprehension :: (a -> Cvt b) -> PyComp a -> Cvt (IterFor b)
comprehension convertBody comprehension =
    compFor $ Py.comprehension_for comprehension
    where
      compFor cf = mkIter <$> expression (Py.comp_in_expr cf)
                          <*> traverse exprToParam (Py.comp_for_exprs cf)
                          <*> compIter (Py.comp_for_iter cf)
          where
            pos = toSourcePos $ Py.comp_for_annot cf
            mkIter e params body = IterFor pos params e body

      compIf ci = IterIf pos <$> expression (Py.comp_if ci)
                             <*> compIter (Py.comp_if_iter ci)
        where
          pos = toSourcePos $ Py.comp_if_annot ci

      compBody = convertBody (Py.comprehension_expr comprehension)

      compIter Nothing =
        CompBody <$> compBody
      compIter (Just (Py.IterFor {Py.comp_iter_for = cf})) = 
        CompFor <$> compFor cf
      compIter (Just (Py.IterIf {Py.comp_iter_if = ci})) = 
        CompIf <$> compIf ci

noneExpr pos = Literal pos NoneLit

argument :: Py.ArgumentSpan -> Cvt Expr
argument (Py.ArgExpr {Py.arg_py_annotation = Just _}) = 
  error "Type annotation not allowed here"
argument (Py.ArgExpr {Py.arg_expr = e, Py.arg_py_annotation = Nothing}) = 
  expression e
argument _ = error "Unsupported argument type"

parameter :: Py.ParameterSpan -> Cvt Parameter
parameter (Py.Param {Py.param_name = name, Py.param_py_annotation = ann}) =
  Parameter <$> parameterDefinition name <*> traverse expression ann

parameters xs = traverse parameter xs

exprToParam :: PyExpr -> Cvt Parameter
exprToParam e@(Py.Var name _) =
  Parameter <$> parameterDefinition name <*> pure Nothing
exprToParam e@(Py.Tuple es _) =
  TupleParam <$> traverse exprToParam es
exprToParam (Py.Paren e _) = exprToParam e
exprToParam _                 = error "Unsupported variable binding"

exprToLHS :: PyExpr -> Cvt Parameter
exprToLHS e@(Py.Var name _) = Parameter <$> definition name <*> pure Nothing
exprToLHS e@(Py.Tuple es _) = TupleParam <$> traverse exprToLHS es
exprToLHS (Py.Paren e _) = exprToLHS e
exprToLHS _                 = error "Unsupported assignment target"

-- Convert a single statement.
singleStatement :: PyStmt -> Cvt [Stmt]
singleStatement stmt =
    case stmt
    of {- Py.For targets generator bodyClause _ ->
           let mkFor generator targets bodyClause =
                   For targets generator bodyClause
           in addLabel $ mkFor <$> expression generator
                               <*> traverse exprToLHS targets
                               <*> suite bodyClause -}
       Py.StmtExpr {Py.stmt_expr = e} ->
         singleton . ExprStmt source_pos <$> expression e
       Py.Conditional {Py.cond_guards = guards, Py.cond_else = els} ->
         foldr ifelse (suite els) guards
       Py.Assign {Py.assign_to = dsts, Py.assign_expr = src} -> 
         assignments (reverse dsts) (expression src)
       Py.Return {Py.return_expr = me} -> 
         -- Process, then discard statements after the return
         singleton <$> Return source_pos <$> maybeExpression source_pos me
       Py.Pass {} -> pure []
       Py.NonLocal {Py.nonLocal_vars = xs} -> 
         [] <$ mapM_ nonlocalDeclaration xs
       Py.Global {Py.global_vars = xs} -> 
         [] <$ mapM_ globalDeclaration xs
       _ -> fail $ "Cannot translate statement:\n" ++ Py.prettyText stmt
    where
      source_pos = toSourcePos $ Py.stmt_annot stmt
      -- An if-else clause
      ifelse (guard, ifTrue) ifFalse = 
          singleton <$> (If source_pos <$> expression guard 
                                       <*> suite ifTrue 
                                       <*> ifFalse)

      singleton x = [x]

defStatements :: [PyStmt] -> Cvt Stmt
defStatements stmts =
  let pos = toSourcePos $ Py.stmt_annot (head stmts)
  in DefGroup pos <$> traverse funDefinition stmts

-- For each assignment in a multiple-assignment statement,
-- assign to one variable, then use that variable as the source value
-- for the next assignment.
assignments :: [PyExpr] -> Cvt Expr -> Cvt [Stmt]
assignments (v:vs) src = (:) <$> assign v src
                             <*> assignments vs (expression v)
    where
      assign v src = 
        let pos = toSourcePos $ Py.expr_annot v
        in Assign pos <$> exprToLHS v <*> src

assignments [] src = pure []

-- Convert a suite of statements.  A suite must have at least one statement.
suite :: [PyStmt] -> Cvt Suite
suite ss = let groups = groupBy ((==) `on` isDefStatement) ss
           in concat <$> traverse suiteComponent groups
    where
      suiteComponent ss
          | isDefStatement (head ss) = fmap (:[]) $ defStatements ss
          | otherwise                = concat <$> traverse singleStatement ss

isDefStatement (Py.Fun {}) = True
isDefStatement (Py.Decorated {Py.decorated_def = Py.Fun {}}) = True
isDefStatement _           = False

isExportStatement (Py.Export {}) = True
isExportStatement _ = False

topLevel :: [PyStmt] -> Cvt ([Func], [ExportItem])
topLevel xs = do
  items <- traverse topLevelFunction xs
  let (functions, exports) = partitionEither items
  return (functions, concat exports)
  where
    partitionEither xs = part xs id id
      where
        part (Left y : xs)  ys zs = part xs ((y:) . ys) zs
        part (Right z : xs) ys zs = part xs ys ((z:) . zs)
        part []             ys zs = (ys [], zs [])

    topLevelFunction stmt
      | isDefStatement stmt = do x <- funDefinition stmt
                                 return (Left x)
      | isExportStatement stmt = do xs <- exportStatement stmt
                                    return (Right xs)
      | otherwise =
          fail "Only functions and exports permitted at global scpoe"

-- Process an export statement
exportStatement :: PyStmt -> Cvt [ExportItem]
exportStatement stmt@(Py.Export {Py.export_items = items,
                                 Py.stmt_annot = ann}) =
  -- Export each item
  mapM export_item items 
  where
    export_item item = do
      var <- use item
      return $ ExportItem (toSourcePos ann) var

-- Unpack a function definition into decorator and real definition
funDefinition :: PyStmt -> Cvt Func
funDefinition stmt@(Py.Fun {}) = funDefinition' [] stmt
funDefinition (Py.Decorated { Py.decorated_decorators = decorators
                            , Py.decorated_def = stmt@(Py.Fun {})}) = 
  funDefinition' decorators stmt

-- A function can be decorated with a list of type variable parameters,
-- specified with a 'forall' annotation. 
-- Each parameter consists of a variable and an optional kind expression.
data Decorators = Decorators (Maybe [(PyIdent, Maybe Expr)])

funDefinition' decorators (Py.Fun { Py.fun_name = name
                                  , Py.fun_args = params
                                  , Py.fun_result_annotation = result
                                  , Py.fun_body = body
                                  , Py.stmt_annot = annotation}) = do
  Decorators forall_decorator <- extractDecorators decorators
  nameVar <- definition name
  let pos = toSourcePos annotation
  enter $ \_ -> do
    qvars <- traverse (mapM qvarDefinition) forall_decorator
    params' <- parameters params
    result' <- traverse expression result
    body' <- suite body
    return $ Func pos nameVar qvars params' result' body'
    
  where
    qvarDefinition (qvar_name, qvar_kind) = do
      qvar <- parameterDefinition qvar_name
      return (qvar, qvar_kind)

extractDecorators decorators =
  foldM extract (Decorators Nothing) decorators
  where
    extract (Decorators oldQvars)
            (Py.Decorator { Py.decorator_name = name
                          , Py.decorator_args = arguments
                          , Py.decorator_annot = annot
                          })
      | name `isName` "forall" =
        if isJust oldQvars
        then error "Only one 'forall' permitted per function"
        else do args <- readArguments arguments
                case sequence args
                  of Just varNames -> return $ Decorators (Just varNames)
                     Nothing -> error "Invalid parameter to forall"
      | otherwise =
        error "Unrecognized decorator"

    name `isName` s = case name of [ident] -> identName ident == s
                                   _ -> False
    
    readArguments args = mapM readArgument args 
    readArgument (Py.ArgExpr { Py.arg_expr = Py.Var {Py.var_ident = ident}
                             , Py.arg_py_annotation = annot}) = do
      annot_expr <- traverse expression annot
      return $ Just (ident, annot_expr)
    readArgument _ = return Nothing

-------------------------------------------------------------------------------
-- Definition group partitioning

-- Partition the top-level definitions into a sequence of definition groups.
-- A definition may only refer to other definitions in its group and to
-- definitions in previous definition groups.  Basically, we search for SCCs.
definitionGroups :: [Func] -> [[Func]]
definitionGroups fs =
    -- Find strongly-connected components of the reference graph.
    -- The root belongs at the head of the list.
    let g = Graph.mkGraph nodes edges :: Graph.Gr Func ()
        components = reverse $ Graph.scc g
    -- Build the list of functions
    in map (map labelOf) components
    where
      nodes :: [Graph.LNode Func]
      nodes = zip [0..] fs

      labelMap = Map.fromList nodes
      labelOf nodeID = labelMap Map.! nodeID

      -- Map from function name to graph node ID
      nodeMap :: Map Int Int
      nodeMap = Map.fromList [(varID (funcName f), n) | (n, f) <- nodes]
          where
            funcName (Func _ name _ _ _ _) = name

      nodeOf varID = Map.lookup varID nodeMap

      -- There is an edge from F to G if F refers to G by name
      edges :: [Graph.UEdge]
      edges = do (fromNode, f) <- nodes
                 v <- Set.toList $ mentionedVars f
                 toNode <- maybeToList $ nodeOf v
                 return (fromNode, toNode, ())

class MentionsVars a where
    -- Get the set of variable IDs mentioned in the term.
    -- We don't care whether the variable is in-scope or not.
    mentionedVars :: a -> Set Int

instance MentionsVars a => MentionsVars [a] where
    mentionedVars xs = Set.unions $ map mentionedVars xs

instance MentionsVars Stmt where
    mentionedVars s =
        case s
        of ExprStmt _ e -> mentionedVars e
           Assign _ _ e -> mentionedVars e
           Return _ e   -> mentionedVars e
           If _ e s1 s2 -> mentionedVars e `Set.union`
                           mentionedVars s1 `Set.union`
                           mentionedVars s2
           DefGroup _ fs -> mentionedVars fs

instance MentionsVars Func where
    mentionedVars (Func _ _ _ _ _ s) = mentionedVars s

instance MentionsVars Expr where
    mentionedVars e =
        case e
        of Variable _ v -> Set.singleton (varID v)
           Literal _ _ -> Set.empty
           Tuple _ es -> mentionedVars es
           Unary _ _ e -> mentionedVars e
           Binary _ _ e1 e2 -> mentionedVars e1 `Set.union` mentionedVars e2
           ListComp _ it -> mentionedVars it
           Generator _ _ it -> mentionedVars it
           Call _ e es -> mentionedVars (e:es)
           Cond _ e1 e2 e3 -> mentionedVars [e1, e2, e3]
           Lambda _ _ e -> mentionedVars e

instance MentionsVars (IterFor Expr) where
    mentionedVars (IterFor _ _ e c) =
      mentionedVars e `Set.union` mentionedVars c

instance MentionsVars (IterIf Expr) where
    mentionedVars (IterIf _ e c) =
      mentionedVars e `Set.union` mentionedVars c

instance MentionsVars (Comprehension Expr) where
    mentionedVars (CompFor it) = mentionedVars it
    mentionedVars (CompIf it) = mentionedVars it
    mentionedVars (CompBody e) = mentionedVars e

-------------------------------------------------------------------------------
-- Exported functions

-- | Convert a Python statement to a Pyon expression.
-- The lowest unassigned variable ID is returned.
convertStatement :: PyStmt -> Int -> Either [String] (Int, [Stmt])
convertStatement stmt names =
    let computation = singleStatement stmt
    in case runAndGetErrors computation names
       of (ns, Left errs)    -> Left errs
          (ns, Right result) -> Right (ns, result)

-- | Convert a Python module to a Pyon module.
-- The lowest unassigned variable ID is returned.
convertModule :: PredefinedVars -- ^ Predefined global variables
              -> Py.ModuleSpan   -- ^ Module to scan
              -> Int             -- ^ First unique variable ID to use
              -> Either [String] (Int, ([Func], [ExportItem]))
convertModule globals mod names =
    let computation =
            case mod
            of Py.Module statements -> 
                 enterGlobal $ \_ -> do defineGlobals globals
                                        topLevel statements
    in case runAndGetErrors computation names
       of (ns, Left errs)    -> Left errs
          (ns, Right result) -> Right (ns, result)

-- | Parse a Python module.
-- The lowest unassigned variable ID is returned.
parseModule :: String           -- ^ File contents
            -> String           -- ^ File name
            -> PredefinedVars   -- ^ Predefined global variables
            -> Int              -- ^ First unique variable ID to use
            -> Either [String] (Int, Module)
parseModule stream path globals nextID =
    case Py.parseModule stream path
    of Left err  -> Left [show err]
       Right (mod, _) ->
           case convertModule globals mod nextID
           of Left err -> Left err
              Right (n, (defs, exps)) ->
                let groups = definitionGroups defs
                in Right (n, Module groups exps)
