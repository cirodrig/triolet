{- AST parsing and name resolution.
--
-- The exported parsing functions in this module first call the
-- Language.Python parser, then apply name resolution rules to
-- assign variables a globally unique ID.
--
-- Some errors related to name resolution, such as undefined variable
-- names and redefinitions of parameter variables, are detected here. 
-}

{-# LANGUAGE FlexibleInstances, DoRec #-}
module Parser.Parser(convertStatement, convertModule, parseModule)
where

import Prelude hiding(mapM, sequence)

import Control.Applicative
import Control.Monad hiding(mapM, sequence)
import Data.Char
import Data.Function
import Data.IORef
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
import Export
import Parser.ParserSyntax
import {-# SOURCE #-} Parser.SSA

import Common.SourcePos(SourcePos, fileSourcePos)

toSourcePos :: Py.SrcSpan -> SourcePos
toSourcePos pos =
  fileSourcePos (Py.span_filename pos) (Py.startRow pos) (Py.startCol pos)

type PyIdent = Py.IdentSpan

data Binding =
    Local                       -- A locally defined variable
    { bIsDef :: Bool
    , bName  :: PVar
    }
  | Param                       -- A variable defined as a function parameter
    { bIsDef :: Bool            -- Always true
    , bName  :: PVar
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

-- | A Python variable with scope information.
--
-- If a variable is a parameter, it cannot have a nonlocal definition.
--
-- Since we do not keep track of global uses and defs, global variables
-- are always marked as having nonlocal uses and defs.
data ScopeVar =
    ScopeVar
    { scopeVar       :: {-# UNPACK #-} !PVar
    , isParameter    :: !Bool   -- ^ True if this is a function parameter
    , hasNonlocalUse :: !Bool   -- ^ True if the variable is used outside
                                -- of its scope; implied by hasNonlocalDef
    , hasNonlocalDef :: !Bool   -- ^ True if the variable is assigned outside
                                -- of its scope
    }

-- A list of the variables local to a scope, generated after a scope is
-- fully processed.
newtype Locals = Locals [ScopeVar]

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

data CvtState = S !Int !Int !Scopes Errors

newtype Cvt a = Cvt {run :: CvtState -> IO (Cvt' a)}

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
joinCvtResults u d m = Cvt $ \s -> do
  x <- run m s
  case x of
    OK s' u2 d2 x    -> return $ OK s' (Set.union u u2) (Set.union d d2) x
    failure@(Fail _) -> return failure

ok :: CvtState -> a -> IO (Cvt' a)
ok s x = return $ OK s Set.empty Set.empty x

instance Monad Cvt where
    return x = Cvt $ \s -> return $ OK s Set.empty Set.empty x
    fail msg = Cvt $ \_ -> return $ Fail msg
    m >>= k  = Cvt $ \s -> do
      x <- run m s
      case x of
        OK s' u1 d1 x -> run (joinCvtResults u1 d1 (k x)) s'
        Fail msg      -> return $ Fail msg

instance Functor Cvt where
    fmap f m = Cvt $ \s -> do
      x <- run m s
      return $ case x of                     
        OK s' u d x -> OK s' u d (f x)
        Fail msg    -> Fail msg

instance Applicative Cvt where
    pure  = return
    (<*>) = ap

-- Run a computation in a nested scope.  This adds a scope to the stack at
-- the beginning of the computation and removes it at the end.
--
-- We do things slightly differently at global scope, since there's no next
-- scope to propagate to.
enter_ :: Bool -> Cvt a -> Cvt a
enter_ isGlobalScope m = Cvt $ \initialState -> do
  rec { 
  -- Run the local computation in a modified environment
  (final, localUses, localDefs, result) <- do
    ret <- run m $ addNewScope final initialState
    return $ case ret
             of OK finalState localUses localDefs x ->
                  let (final, finalState') = removeNewScope finalState
                  in (final, localUses, localDefs, Right (finalState', x))
                Fail str ->
                  (Map.empty, Set.empty, Set.empty, Left str)

  -- Nonlocal variables, plus uses that are not satisfied locally,
  -- propagate upward
  ; let boundHere = Set.fromList $ mapMaybe localBindingName $ Map.elems final
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
                       defsNotBoundHere }
  return $! case result
            of Right (finalState, resultValue) ->
                 OK finalState nonlocalUses nonlocalDefs resultValue
               Left str -> Fail str
    where
      -- Put a new scope on the stack.  The new scope contains the final value
      -- of its dictionary.
      addNewScope finalScope (S ms ns scopes errs) =
          S ms ns (Scope finalScope Map.empty : scopes) errs

      -- Remove the scope at the top of the stack.
      -- Save its final dictionary, which will be inserted when the scope was
      -- created.
      removeNewScope (S ms ns (Scope _ finalScope : scopes) errs) =
          (finalScope, S ms ns scopes errs)

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
withScopes f = Cvt $ \(S ms ns scopes errs) ->
                         let (x, errs') = f scopes
                         in ok (S ms ns scopes (errs' . errs)) x

updateScopes :: (Scopes -> (Scopes, Errors)) -> Cvt ()
updateScopes f = Cvt $ \(S ms ns scopes errs) ->
                           let (scopes', errs') = f scopes
                           in ok (S ms ns scopes' (errs' . errs)) ()

newID :: Cvt Int
newID = Cvt $ \(S ms n s errs) -> ok (S ms (n+1) s errs) n

newStmtID :: Cvt Int
newStmtID = Cvt $ \(S m ns s errs) -> ok (S (m+1) ns s errs) m

logErrors :: Errors -> Cvt ()
logErrors es = Cvt $ \(S ms ns scopes errs) ->
  ok (S ms ns scopes (es . errs)) ()

logError :: Maybe Err -> Cvt ()
logError e = logErrors (toErrors e)
    where
      toErrors Nothing  = noError
      toErrors (Just e) = oneError e

runAndGetErrors :: Cvt a -> Int -> IO (Int, Int, Either [String] a)
runAndGetErrors m nextName = do
  x <- run m (S 0 nextName emptyScope noError)
  return $! case x
            of Fail msg -> (0, nextName, Left [msg])
               OK (S nextSName' nextName' _ errs) _ _ x ->
                 case errs []
                 of [] -> (nextSName', nextName', Right x)
                    xs -> (nextSName', nextName', Left xs)

newJoinNodeRef :: Cvt (IORef (Maybe JoinNode))
newJoinNodeRef = Cvt $ \s -> do
  x <- newIORef Nothing
  ok s x


-------------------------------------------------------------------------------
-- Low-level editing of bindings

-- Look up a variable in the environment.  The result must be used lazily.
lookupVar :: PyIdent -> Cvt PVar
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

-- | Put the given list of variables into the environment.  Use this function
-- at global scope to initialize the global variables.
defineGlobals :: [PVar] -> Cvt ()
defineGlobals xs = mapM_ define_global xs
  where 
    define_global v =
      let binding = Local True v
      in addLocalBinding (Py.Ident (varName v) Py.SpanEmpty) binding

-- Indicate that a definition was seen
signalDef :: PyIdent -> Cvt ()
signalDef id = Cvt $ \s ->
  return $ OK s Set.empty (Set.singleton $ identName id) ()

-- Indicate that a use was seen
signalUse :: PyIdent -> Cvt ()
signalUse id = Cvt $ \s ->
  return $ OK s (Set.singleton $ identName id) Set.empty ()

-------------------------------------------------------------------------------
-- High-level editing of bindings

-- Record that a binding has a definition 
markAsDefinition :: PyIdent -> Binding -> Cvt ()
markAsDefinition name b
    | bIsDef b = return ()
    | otherwise = addLocalBinding name (b {bIsDef = True})

-- Create a new variable from an identifier.
-- This is different from all other variables created by newVar.
newVar :: PyIdent -> Cvt PVar
newVar id = makeVar (identName id) <$> newID

-- Process a definition of an identifier.  Return the corresponding variable,
-- which must be used lazily.
definition :: PyIdent -> Cvt PVar
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
parameterDefinition :: PyIdent -> Cvt PVar
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
type PySlice = Py.SliceSpan
type PyStmt = Py.StatementSpan
type PyComp a = Py.ComprehensionSpan a

expression :: PyExpr -> Cvt (Expr Int)
expression expr =
    case expr
    of Py.Var {Py.var_ident = ident} -> 
         Variable source_pos <$> use ident
       Py.Int {Py.int_value = n} -> 
         pure (Literal source_pos (IntLit n))
       Py.Float {Py.float_value = d} ->
         pure (Literal source_pos (FloatLit d))
       Py.Imaginary {Py.imaginary_value = d} ->
         pure (Literal source_pos (ImaginaryLit d))
       Py.Bool {Py.bool_value = b} ->
         pure (Literal source_pos (BoolLit b))
       Py.None {} -> 
         pure(Literal source_pos NoneLit)
       Py.Tuple {Py.tuple_exprs = es} -> 
         Tuple source_pos <$> traverse expression es
       Py.Call {Py.call_fun = f, Py.call_args = xs} -> 
         Call source_pos <$> expression f <*> traverse argument xs
       Py.LetExpr { Py.let_target = ts
                  , Py.let_rhs = rhs
                  , Py.let_body = body} -> do
         let t = case ts
                 of [t] -> t
                    _ -> error "Multiple assignment not allowed in 'let'"
         rhs' <- expression rhs
         enter $ do
           t' <- exprToParam t 
           body' <- expression body 
           return $ Let source_pos t' rhs' body'
       Py.CondExpr { Py.ce_true_branch = tr
                   , Py.ce_condition = c
                   , Py.ce_false_branch = fa} -> 
         let mkCond tr c fa = Cond source_pos c tr fa
         in mkCond <$> expression tr <*> expression c <*> expression fa
       Py.BinaryOp { Py.operator = op
                   , Py.left_op_arg = l
                   , Py.right_op_arg = r} -> 
         Binary source_pos op <$> expression l <*> expression r
       Py.Subscript {Py.subscriptee = base, Py.subscript_exprs = [index]} ->
         Subscript source_pos <$> expression base <*> expression index
       Py.SlicedExpr {Py.slicee = base, Py.slices = slices} ->
         Slicing source_pos <$> expression base <*> traverse slice slices
       Py.UnaryOp {Py.operator = op, Py.op_arg = arg} -> 
         Unary source_pos op <$> expression arg
       Py.Lambda {Py.lambda_args = args, Py.lambda_body = body} -> 
         enter $ Lambda source_pos <$> traverse parameter args 
                                   <*> expression body

       -- Generators and list comprehensions have a separate scope
       Py.Generator {Py.gen_comprehension = comp} -> 
         enter $ Generator source_pos <$> comprehension expression comp
       Py.ListComp {Py.list_comprehension = comp} -> 
         enter $ ListComp source_pos <$> comprehension expression comp
                            
       Py.Paren {Py.paren_expr = e} -> expression e
       _ -> fail $ "Cannot translate expression:\n" ++ Py.prettyText expr
    where
      source_pos = toSourcePos $ Py.expr_annot expr

-- Convert an optional expression into an expression or None
maybeExpression :: SourcePos -> Maybe PyExpr -> Cvt (Expr Int)
maybeExpression _   (Just e) = expression e
maybeExpression pos Nothing  = pure (noneExpr pos)

slice :: PySlice -> Cvt (Slice Int)
slice sl =
  case sl
  of Py.SliceProper (Just l) (Just u) Nothing _ ->
       SliceSlice source_pos <$> expression l <*> expression u <*> pure Nothing
     Py.SliceProper (Just l) (Just u) (Just (Just s)) _ ->
       SliceSlice source_pos <$> expression l <*> expression u <*> (Just <$> expression s)
     Py.SliceExpr e _ ->
       ExprSlice <$> expression e
  where
    source_pos = toSourcePos $ Py.slice_annot sl

comprehension :: (a -> Cvt (b Int)) -> PyComp a -> Cvt (IterFor Int b)
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

argument :: Py.ArgumentSpan -> Cvt (Expr Int)
argument (Py.ArgExpr {Py.arg_py_annotation = Just _}) = 
  error "Type annotation not allowed here"
argument (Py.ArgExpr {Py.arg_expr = e, Py.arg_py_annotation = Nothing}) = 
  expression e
argument _ = error "Unsupported argument type"

parameter :: Py.ParameterSpan -> Cvt (Parameter Int)
parameter (Py.Param {Py.param_name = name, Py.param_py_annotation = ann}) =
  Parameter <$> parameterDefinition name <*> traverse expression ann

parameters xs = traverse parameter xs

exprToParam :: PyExpr -> Cvt (Parameter Int)
exprToParam e@(Py.Var name _) =
  Parameter <$> parameterDefinition name <*> pure Nothing
exprToParam e@(Py.Tuple es _) =
  TupleParam <$> traverse exprToParam es
exprToParam (Py.Paren e _) = exprToParam e
exprToParam _                 = error "Unsupported variable binding"

exprToLHS :: PyExpr -> Cvt (Parameter Int)
exprToLHS e@(Py.Var name _) = Parameter <$> definition name <*> pure Nothing
exprToLHS e@(Py.Tuple es _) = TupleParam <$> traverse exprToLHS es
exprToLHS (Py.Paren e _) = exprToLHS e
exprToLHS _                 = error "Unsupported assignment target"

-- Convert a single statement.
singleStatement :: PyStmt -> Cvt [Stmt Int]
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
         singleton <$> (Return source_pos <$> newStmtID
                                          <*> newJoinNodeRef 
                                          <*> maybeExpression source_pos me)
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
                                       <*> ifFalse
                                       <*> pure Nothing)

      singleton x = [x]

defStatements :: [PyStmt] -> Cvt (Stmt Int)
defStatements stmts =
  let pos = toSourcePos $ Py.stmt_annot (head stmts)
  in DefGroup pos <$> traverse funDefinition stmts

-- For each assignment in a multiple-assignment statement,
-- assign to one variable, then use that variable as the source value
-- for the next assignment.
assignments :: [PyExpr] -> Cvt (Expr Int) -> Cvt [Stmt Int]
assignments (v:vs) src = (:) <$> assign v src
                             <*> assignments vs (expression v)
    where
      assign v src = 
        let pos = toSourcePos $ Py.expr_annot v
        in Assign pos <$> exprToLHS v <*> src

assignments [] src = pure []

-- Convert a suite of statements.  A suite must have at least one statement.
suite :: [PyStmt] -> Cvt (Suite Int)
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

topLevel :: [PyStmt] -> Cvt ([Func Int], [ExportItem Int])
topLevel xs = do
  items <- traverse topLevelFunction xs
  return $ partitionEither items
  where
    partitionEither xs = part xs id id
      where
        part (Left y : xs)  ys zs = part xs ((y:) . ys) zs
        part (Right z : xs) ys zs = part xs ys ((z:) . zs)
        part []             ys zs = (ys [], zs [])

    topLevelFunction stmt
      | isDefStatement stmt = do x <- funDefinition stmt
                                 return (Left x)
      | isExportStatement stmt = do x <- exportStatement stmt
                                    return (Right x)
      | otherwise =
          fail "Only functions and exports permitted at global scpoe"

-- Process an export statement
exportStatement :: PyStmt -> Cvt (ExportItem Int)
exportStatement stmt@(Py.Export {Py.export_lang = lang,
                                 Py.export_name = name,
                                 Py.export_item = item,
                                 Py.export_type = ty,
                                 Py.stmt_annot = ann}) = do
  language <-
    case identName lang
    of "ccall" -> return CCall
       _ -> error $ "Unsupported language '" ++ identName lang ++ "'"
  var <- use item
  ty' <- expression ty
  
  -- Determine the exported name.
  -- Remove quote characters from the given string.
  export_name <-
    case name
    of Nothing -> return $ identName item
       Just nm -> check_valid_identifier language $ init $ tail nm

  return $
    ExportItem (toSourcePos ann) (ExportSpec language export_name) var ty'
  where
    check_valid_identifier _ "" = fail "Exported name is empty string"

    -- Valid C identifier: alpha (alnum*)
    check_valid_identifier CCall name@(c:cs)
      | is_c_alpha c && all is_c_alnum cs = return name
      | otherwise = fail "Exported name is not a valid C identifier"
    
    is_c_alpha c = isAlpha c || c == '_'
    is_c_alnum c = isAlphaNum c || c == '_'

-- Unpack a function definition into decorator and real definition
funDefinition :: PyStmt -> Cvt (Func Int)
funDefinition stmt@(Py.Fun {}) = funDefinition' [] stmt
funDefinition (Py.Decorated { Py.decorated_decorators = decorators
                            , Py.decorated_def = stmt@(Py.Fun {})}) = 
  funDefinition' decorators stmt

-- A function can be decorated with a list of type variable parameters,
-- specified with a 'forall' annotation. 
-- Each parameter consists of a variable and an optional kind expression.
data Decorators = Decorators (Maybe [(PyIdent, Maybe (Expr Int))])

funDefinition' decorators (Py.Fun { Py.fun_name = name
                                  , Py.fun_args = params
                                  , Py.fun_result_annotation = result
                                  , Py.fun_body = body
                                  , Py.stmt_annot = annotation}) = do
  Decorators forall_decorator <- extractDecorators decorators
  nameVar <- definition name
  let pos = toSourcePos annotation
  enter $ do
    qvars <- traverse (mapM qvarDefinition) forall_decorator
    params' <- parameters params
    result' <- traverse expression result
    body' <- suite body
    return $ Func pos nameVar qvars params' result' body' Nothing
    
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
definitionGroups :: [Func Int] -> [[Func Int]]
definitionGroups fs =
    -- Find strongly-connected components of the reference graph.
    -- The root belongs at the head of the list.
    let g = Graph.mkGraph nodes edges :: Graph.Gr (Func Int) ()
        components = reverse $ Graph.scc g
    -- Build the list of functions
    in map (map labelOf) components
    where
      nodes :: [Graph.LNode (Func Int)]
      nodes = zip [0..] fs

      labelMap = Map.fromList nodes
      labelOf nodeID = labelMap Map.! nodeID

      -- Map from function name to graph node ID
      nodeMap :: Map Int Int
      nodeMap = Map.fromList [(varID (funcName f), n) | (n, f) <- nodes]

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

instance MentionsVars (Stmt Int) where
    mentionedVars s =
        case s
        of ExprStmt _ e   -> mentionedVars e
           Assign _ _ e   -> mentionedVars e
           Return _ _ _ e -> mentionedVars e
           If _ e s1 s2 _ -> mentionedVars e `Set.union`
                             mentionedVars s1 `Set.union`
                             mentionedVars s2
           DefGroup _ fs  -> mentionedVars fs

instance MentionsVars (Func Int) where
    mentionedVars f = mentionedVars $ funcBody f

instance MentionsVars (Expr Int) where
    mentionedVars e =
        case e
        of Variable _ v -> Set.singleton (varID v)
           Literal _ _ -> Set.empty
           Tuple _ es -> mentionedVars es
           Unary _ _ e -> mentionedVars e
           Binary _ _ e1 e2 -> mentionedVars e1 `Set.union` mentionedVars e2
           Subscript _ e1 e2 -> mentionedVars e1 `Set.union` mentionedVars e2
           Slicing _ e ss -> mentionedVars e `Set.union` mentionedVars ss
           ListComp _ it -> mentionedVars it
           Generator _ it -> mentionedVars it
           Call _ e es -> mentionedVars (e:es)
           Cond _ e1 e2 e3 -> mentionedVars [e1, e2, e3]
           Lambda _ _ e -> mentionedVars e
           Let _ _ e1 e2 -> mentionedVars e1 `Set.union` mentionedVars e2

instance MentionsVars (Slice Int) where
  mentionedVars (SliceSlice _ e1 e2 e3) =
    Set.unions [mentionedVars e1, mentionedVars e2, maybe Set.empty mentionedVars e3]

instance MentionsVars (IterFor Int Expr) where
    mentionedVars (IterFor _ _ e c) =
      mentionedVars e `Set.union` mentionedVars c

instance MentionsVars (IterIf Int Expr) where
    mentionedVars (IterIf _ e c) =
      mentionedVars e `Set.union` mentionedVars c

instance MentionsVars (Comprehension Int Expr) where
    mentionedVars (CompFor it) = mentionedVars it
    mentionedVars (CompIf it) = mentionedVars it
    mentionedVars (CompBody e) = mentionedVars e

-------------------------------------------------------------------------------
-- Exported functions

-- | Convert a Python statement to a Pyon expression.
-- The lowest unassigned variable ID is returned.
convertStatement :: PyStmt -> Int -> IO (Either [String] (Int, Int, [Stmt Int]))
convertStatement stmt names =
    let computation = singleStatement stmt
    in do x <- runAndGetErrors computation names
          return $! case x of (ms, ns, Left errs)    -> Left errs
                              (ms, ns, Right result) -> Right (ms, ns, result)

-- | Convert a Python module to a Pyon module.
-- The lowest unassigned variable ID is returned.
convertModule :: [Var Int]       -- ^ Predefined global variables
              -> Py.ModuleSpan   -- ^ Module to scan
              -> Int             -- ^ First unique variable ID to use
              -> IO (Either [String] (Int, Int, ([Func Int], [ExportItem Int])))
convertModule globals mod names =
    let computation =
            case mod
            of Py.Module statements ->
                 enterGlobal $ do defineGlobals globals
                                  topLevel statements
    in do x <- runAndGetErrors computation names
          return $! case x of (ms, ns, Left errs)    -> Left errs
                              (ms, ns, Right result) -> Right (ms, ns, result)

-- | Parse a Python module.
-- The lowest unassigned variable ID is returned.
parseModule :: String           -- ^ File contents
            -> String           -- ^ File name
            -> [Var Int]        -- ^ Predefined global variables
            -> Int              -- ^ First unique variable ID to use
            -> IO (Either [String] (Int, Int, Module Int))
parseModule stream path globals nextID =
    case Py.parseModule stream path
    of Left err  -> return $ Left [show err]
       Right (mod, _) -> do
         x <- convertModule globals mod nextID
         return $! case x of Left err -> Left err
                             Right (m, n, (defs, exps)) ->
                               let groups = definitionGroups defs
                               in Right (m, n, Module path groups exps)
