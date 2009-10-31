
module Parser(convertStatement, convertModule, parseModule)
where

import Control.Applicative
import Control.Monad
import qualified Data.Map as Map
import Data.Traversable

import qualified Language.Python.Version3.Parser as Py
import qualified Language.Python.Version3.Syntax.AST as Py
import ParserSyntax

data Binding = Local Var        -- A locally defined variable
             | Param Var        -- A variable defined as a function parameter
             | Nonlocal         -- A nonlocal variable (indicated by a keyword)
             | Global           -- A global variable (indicated by a keyword)
               deriving(Show)
type Bindings = Map.Map Py.Ident Binding

data Scope =
    Scope { finalMembers   :: Bindings
          , currentMembers :: !Bindings
          }
    deriving(Show)

type Scopes = [Scope]

emptyScope :: Scopes
emptyScope = [] 

type NameSupply = [Int]

-- Some errors are generated lazily
type Err = String
type Errors = [Err] -> [Err]

noError :: Errors
noError = id

oneError :: Err -> Errors
oneError = (:)

identName (Py.Ident name) = name

-------------------------------------------------------------------------------
-- The process of converting to a Pyon AST.
--
-- Keeps track of the current context and thread a name supply through the
-- computation.   throw an error. 

data CvtState = S NameSupply !Scopes Errors

newtype Cvt a = Cvt {run :: CvtState -> Cvt' a}

data Cvt' a = OK !CvtState a
            | Fail String

instance Monad Cvt where
    return x = Cvt $ \s -> OK s x
    fail msg = Cvt $ \_ -> Fail msg
    m >>= k  = Cvt $ \s -> case run m s
                           of OK s' x  -> run (k x) s'
                              Fail msg -> Fail msg

instance Functor Cvt where
    fmap f m = Cvt $ \s -> case run m s
                           of OK s' x  -> OK s' (f x)
                              Fail msg -> Fail msg

instance Applicative Cvt where
    pure  = return
    (<*>) = ap

-- Run a computation in a nested scope.  This adds a scope to the stack at
-- the beginning of the computation and removes it at the end.
enter :: Cvt a -> Cvt a
enter m = Cvt $ \initialState ->
    let (final, result) =
            case run m $ addNewScope final initialState
            of OK finalState x ->
                   let (final, finalState') = removeNewScope finalState
                   in (final, OK finalState' x)
               Fail str -> 
                   (Map.empty, Fail str)
    in result
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

withScopes :: (Scopes -> (a, Errors)) -> Cvt a
withScopes f = Cvt $ \(S ns scopes errs) ->
                         let (x, errs') = f scopes
                         in OK (S ns scopes (errs' . errs)) x

updateScopes :: (Scopes -> (Scopes, Errors)) -> Cvt ()
updateScopes f = Cvt $ \(S ns scopes errs) ->
                           let (scopes', errs') = f scopes
                           in OK (S ns scopes' (errs' . errs)) ()

newID :: Cvt Int
newID = Cvt $ \(S (n:ns) s errs) -> OK (S ns s errs) n

logErrors :: Errors -> Cvt ()
logErrors es = Cvt $ \(S ns scopes errs) -> OK (S ns scopes (es . errs)) ()

logError :: Maybe Err -> Cvt ()
logError e = logErrors (toErrors e)
    where
      toErrors Nothing  = noError
      toErrors (Just e) = oneError e

runAndGetErrors :: Cvt a -> NameSupply -> (NameSupply, Either [String] a)
runAndGetErrors m names =
    case run m (S names emptyScope noError)
    of Fail msg -> (names, Left [msg])
       OK (S names _ errs) x ->
           case errs []
           of [] -> (names, Right x)
              xs -> (names, Left xs)

-------------------------------------------------------------------------------
-- Low-level editing of bindings

-- Look up a variable in the environment.  The result must be used lazily.
lookupVar :: Py.Ident -> Cvt Var
lookupVar name = withScopes $ \s -> lookup s
    where
      lookup (s:ss) = case Map.lookup name $ finalMembers s
                      of Just (Local v) -> (v, noError)
                         Just (Param v) -> (v, noError)
                         _              -> lookup ss

      lookup [] = (noVariable, oneError msg)

      msg = "Undefined variable '" ++ identName name ++ "'"

      noVariable = error "Invalid variable due to parse error"

-- Look up a binding in the current, incomplete local scope.
lookupCurrentLocalBinding :: Py.Ident -> Cvt (Maybe Binding)
lookupCurrentLocalBinding name =
    withScopes $ \s -> (lookup (head s), noError)
    where
      lookup s = Map.lookup name $ currentMembers s

addLocalBinding :: Py.Ident -> Binding -> Cvt ()
addLocalBinding name binding =
    updateScopes $ \s -> (addBinding s, noError)
    where
      addBinding (s:ss) = addBindingToScope s : ss

      addBindingToScope s = s {currentMembers = Map.insert name binding $
                                                currentMembers s}

-------------------------------------------------------------------------------
-- High-level editing of bindings

-- Create a new variable from an identifier.
-- This is different from all other variables created by newVar.
newVar :: Py.Ident -> Cvt Var
newVar (Py.Ident name) = Var name <$> newID

-- Process a definition of an identifier.  Return the corresponding variable,
-- which must be used lazily.
definition :: Py.Ident -> Cvt Var
definition name = do
  -- First, insert a new binding if appropriate
  b <- lookupCurrentLocalBinding name
  case b of
    Just _  -> return ()
    Nothing -> do v' <- newVar name
                  addLocalBinding name (Local v')

  -- Then look up the actual binding for this variable.
  -- The binding that was inserted may not be the actual binding.
  lookupVar name

-- Process a parameter definition.
-- Unlike ordinary definitions, parameters cannot be redefined.
-- Return the corresponding variable.
parameterDefinition :: Py.Ident -> Cvt Var
parameterDefinition name = do
  b <- lookupCurrentLocalBinding name
  case b of
    Just _  -> parameterRedefined name
    Nothing -> do v <- newVar name
                  addLocalBinding name (Param v)
                  return v

parameterRedefined :: Py.Ident -> Cvt a
parameterRedefined name =
    let msg = "Parameter variable '" ++ identName name ++ "' redefined"
    in fail msg

-- Record that a variable is globally or nonlocally defined.  If this
-- conflicts with an existing definition, report an error.
globalDeclaration, nonlocalDeclaration :: Py.Ident -> Cvt ()
globalDeclaration name = do
  b <- lookupCurrentLocalBinding name
  case b of
    Just (Local v) -> addLocalBinding name Global -- override local binding
    Just (Param _) -> parameterRedefined name
    Just Nonlocal  -> fail msg
    Just Global    -> return () -- no change
    Nothing        -> addLocalBinding name Global
    where
      msg = "Variable '" ++ identName name ++ "' cannot be declared both global and nonlocal"

nonlocalDeclaration name = do
  b <- lookupCurrentLocalBinding name
  case b of
    Just (Local v) -> addLocalBinding name Nonlocal -- override local binding
    Just (Param _) -> parameterRedefined name
    Just Nonlocal  -> return () -- no change
    Just Global    -> fail message
    Nothing        -> addLocalBinding name Nonlocal
    where
      message = "Variable '" ++ identName name ++ "' cannot be declared both global and nonlocal"

-- Look up a use of a variable
use name = lookupVar name

-------------------------------------------------------------------------------
-- Conversions for Python 3 Syntax

expression :: Py.Expr -> Cvt LabExpr
expression expr = Lab expr <$> expression' expr

expression' :: Py.Expr -> Cvt Expr
expression' expr =
    case expr
    of Py.Var ident        -> Variable <$> use ident
       Py.Int n            -> pure (Literal (IntLit n))
       Py.Float d          -> pure (Literal (FloatLit d))
       Py.Bool b           -> pure (Literal (BoolLit b))
       Py.None             -> pure (Literal NoneLit)
       Py.Call f xs        -> Call <$> expression f <*> traverse argument xs
       Py.CondExpr tr c fa -> let mkCond tr c fa = Cond c tr fa
                              in mkCond <$> expression tr
                                        <*> expression c
                                        <*> expression fa
       Py.BinaryOp op l r  -> Binary op <$> expression l <*> expression r
       Py.UnaryOp op arg   -> Unary op <$> expression arg
       Py.Lambda args body -> Lambda <$> lambda args body

       -- Generators have a separate scope
       Py.Generator comp   -> Generator <$>
                              enter (comprehension expression comp)
       Py.ListComp comp    -> ListComp <$> comprehension expression comp

-- Convert an optional expression into an expression or None
maybeExpression :: Maybe Py.Expr -> Cvt LabExpr
maybeExpression (Just e) = expression e
maybeExpression Nothing  = pure noneExpr

comprehension :: (a -> Cvt b) -> Py.Comprehension a -> Cvt (IterFor b)
comprehension convertBody comprehension =
    compFor $ Py.comprehension_for comprehension
    where
      compFor cf = mkIter <$> expression (Py.comp_in_expr cf)
                          <*> traverse exprToParam (Py.comp_for_exprs cf)
                          <*> compIter (Py.comp_for_iter cf)
          where
            mkIter e params body = IterFor params e body

      compIf ci = IterIf <$> expression (Py.comp_if ci)
                         <*> compIter (Py.comp_if_iter ci)

      compBody = convertBody (Py.comprehension_expr comprehension)

      compIter Nothing                = CompBody <$> compBody
      compIter (Just (Py.IterFor cf)) = CompFor <$> compFor cf
      compIter (Just (Py.IterIf ci))  = CompIf <$> compIf ci

noneExpr = Lab ("None") (Literal NoneLit)

argument :: Py.Argument -> Cvt LabExpr
argument (Py.ArgExpr e) = expression e
argument _ = error "Unsupported argument type"

parameter :: Py.Parameter -> Cvt LabParameter
parameter param = Lab param <$> parameter' param

parameter' :: Py.Parameter -> Cvt Parameter
parameter' (Py.Param name _ _) = Parameter <$> parameterDefinition name

exprToParam :: Py.Expr -> Cvt LabParameter
exprToParam e@(Py.Var name) = Lab e . Parameter <$> parameterDefinition name

exprToLHS :: Py.Expr -> Cvt LabParameter
exprToLHS e@(Py.Var name) = Lab e . Parameter <$> definition name

-- Convert a statement that is not at the end of a suite.
-- The rest of the suite is passed as a parameter.
medialStatement :: Py.Statement -> Cvt LabExpr -> Cvt LabExpr
medialStatement stmt cont = addLabel $
    case stmt
    of Py.For targets generator bodyClause _ ->
           let mkFor generator targets bodyClause =
                   For targets generator bodyClause
           in mkFor <$> expression generator
                    <*> traverse exprToLHS targets
                    <*> suite bodyClause
       Py.Fun name args _ body ->
           let funBody = fmap (Lab stmt) $ funDefinition name args body
           in Letrec <$> fmap (:[]) funBody <*> cont
       Py.Assign dsts src -> expression src <**> assignments (reverse dsts)
       Py.Return me -> -- Process, then discard statements after the return
                       Return <$> maybeExpression me <* cont
    where
      -- Assign the right-hand side to a sequence of variables by handing
      -- the value along.  The continuation comes after all assignments.
      assignments :: [Py.Expr] -> Cvt (LabExpr -> Expr)
      assignments (v:vs) = do v' <- exprToLHS v
                              body <- assignments vs
                              let body' = Lab stmt $ body $ paramToValue v'
                              return $ \src -> Let v' src body'
      assignments []     = return $ \(Lab _ e) -> e

      paramToValue (Lab l (Parameter v)) = Lab l (Variable v)

      addLabel f = Lab stmt <$> f

finalStatement :: Py.Statement -> Cvt LabExpr
finalStatement stmt =
    case stmt
    of Py.Return me -> addLabel $ Return <$> maybeExpression me
       Py.Pass -> pure noneExpr

       -- Default: run the expression and return None
       _ -> medialStatement stmt $ pure noneExpr

    where
      addLabel f = Lab stmt <$> f

-- Convert a suite of statements.  A suite must have at least one statement.
suite :: [Py.Statement] -> Cvt LabExpr
suite [s]    = finalStatement s
suite (s:ss) = medialStatement s $ suite ss

topLevel :: [Py.Statement] -> Cvt [Lab FunDef]
topLevel xs = traverse topLevelFunction xs
    where
      topLevelFunction stmt@(Py.Fun name args _ body) = fmap (Lab stmt) $
          FunDef <$> definition name <*> function args body
      topLevelFunction _ =
          fail "Only function definitions permitted at global scpoe"

lambda :: [Py.Parameter] -> Py.Expr -> Cvt Function
lambda args body = enter $
    Function <$> traverse parameter args <*> expression body

function :: [Py.Parameter] -> Py.Suite -> Cvt Function
function args body = enter $
    Function <$> traverse parameter args <*> suite body

funDefinition :: Py.Ident -> [Py.Parameter] -> Py.Suite -> Cvt FunDef
funDefinition name params body =
    FunDef <$> definition name <*> function params body

-------------------------------------------------------------------------------
-- Exported functions

-- Convert a statement; check for and report errors
convertStatement :: Py.Statement -> NameSupply -> Either [String] LabExpr
convertStatement stmt names =
    let computation = finalStatement stmt
    in case runAndGetErrors computation names
       of (_, result) -> result

-- Convert a module; check for and report errors
convertModule :: Py.Module -> NameSupply -> Either [String] [Lab FunDef]
convertModule mod names =
    let computation =
            case mod
            of Py.Module statements -> enter $ topLevel statements
    in case runAndGetErrors computation names
       of (_, result) -> result

parseModule :: String -> String -> Either [String] [Lab FunDef]
parseModule stream path =
    case Py.parseModule stream path
    of Left err  -> Left [show err]
       Right mod -> case convertModule mod [1..]
                    of Left err   -> Left err
                       Right defs -> Right defs
