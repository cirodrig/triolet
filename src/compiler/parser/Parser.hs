
module Parser(convertStatement, convertModule, parseModule)
where

import Control.Applicative
import Control.Monad
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Traversable

import qualified Language.Python.Version3.Parser as Py
import qualified Language.Python.Version3.Syntax.AST as Py
import qualified Language.Python.Version3.Syntax.Pretty as Py
import ParserSyntax

data Binding = Local { bIsDef :: Bool
                     , bName  :: Var
                     }   -- A locally defined variable
             | Param { bIsDef :: Bool -- Always true
                     , bName  :: Var
                     }   -- A variable defined as a function parameter
             | Nonlocal { bIsDef :: Bool
                        }       -- A nonlocal variable (indicated by a keyword)
             | Global { bIsDef :: Bool
                      }         -- A global variable (indicated by a keyword)
               deriving(Show)



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

type Bindings = Map.Map Py.Ident Binding

data Scope =
    Scope { finalMembers   :: Bindings
          , currentMembers :: !Bindings
          }
    deriving(Show)

type Scopes = [Scope]

emptyScope :: Scopes
emptyScope = [] 

-- A set of variable names
type NameSet = Set.Set String

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
                           Map.elems $
                           Map.mapMaybeWithKey nonlocalUseName final
        defsNotBoundHere = Set.fromList $
                           Map.elems $
                           Map.mapMaybeWithKey nonlocalDefName final
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

      nonlocalUseName (Py.Ident name) (Nonlocal False) = Just name
      nonlocalUseName _ _ = Nothing

      nonlocalDefName (Py.Ident name) (Nonlocal True) = Just name
      nonlocalDefName _ _ = Nothing

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
newID = Cvt $ \(S (n:ns) s errs) -> ok (S ns s errs) n

logErrors :: Errors -> Cvt ()
logErrors es = Cvt $ \(S ns scopes errs) -> ok (S ns scopes (es . errs)) ()

logError :: Maybe Err -> Cvt ()
logError e = logErrors (toErrors e)
    where
      toErrors Nothing  = noError
      toErrors (Just e) = oneError e

runAndGetErrors :: Cvt a -> NameSupply -> (NameSupply, Either [String] a)
runAndGetErrors m names =
    case run m (S names emptyScope noError)
    of Fail msg -> (names, Left [msg])
       OK (S names _ errs) _ _ x ->
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
                      of Just (Local _ v) -> (v, noError)
                         Just (Param _ v) -> (v, noError)
                         _                -> lookup ss

      lookup [] = (noVariable, oneError msg)

      msg = "Undefined variable '" ++ identName name ++ "'"

      noVariable = error "Invalid variable due to parse error"

-- Look up a binding in the current, incomplete local scope.
lookupCurrentLocalBinding :: Py.Ident -> Cvt (Maybe Binding)
lookupCurrentLocalBinding name =
    withScopes $ \s -> (lookup (head s), noError)
    where
      lookup s = Map.lookup name $ currentMembers s

-- Insert or modify a binding
addLocalBinding :: Py.Ident -> Binding -> Cvt ()
addLocalBinding name binding =
    updateScopes $ \s -> (addBinding s, noError)
    where
      addBinding (s:ss) = addBindingToScope s : ss

      addBindingToScope s = s {currentMembers = Map.insert name binding $
                                                currentMembers s}

signalDef :: Py.Ident -> Cvt ()
signalDef (Py.Ident nm) = Cvt $ \s -> OK s Set.empty (Set.singleton nm) ()

signalUse :: Py.Ident -> Cvt ()
signalUse (Py.Ident nm) = Cvt $ \s -> OK s (Set.singleton nm) Set.empty ()

-------------------------------------------------------------------------------
-- High-level editing of bindings

-- Record that a binding has a definition 
markAsDefinition :: Py.Ident -> Binding -> Cvt ()
markAsDefinition name b
    | bIsDef b = return ()
    | otherwise = addLocalBinding name (b {bIsDef = True})

-- Create a new variable from an identifier.
-- This is different from all other variables created by newVar.
newVar :: Py.Ident -> Cvt Var
newVar (Py.Ident name) = Var name <$> newID

-- Process a definition of an identifier.  Return the corresponding variable,
-- which must be used lazily.
definition :: Py.Ident -> Cvt Var
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
parameterDefinition :: Py.Ident -> Cvt Var
parameterDefinition name = do
  signalDef name
  mb <- lookupCurrentLocalBinding name
  case mb of
    Just _  -> parameterRedefined name
    Nothing -> do v <- newVar name
                  addLocalBinding name (Param True v)
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
       Py.Generator comp   -> enter $ \locals ->
                                  Generator locals <$>
                                  comprehension expression comp
       Py.ListComp comp    -> ListComp <$> comprehension expression comp
       _ -> fail $ "Cannot translate expression:\n" ++ Py.prettyText expr

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
medialStatement stmt cont =
    case stmt
    of {- Py.For targets generator bodyClause _ ->
           let mkFor generator targets bodyClause =
                   For targets generator bodyClause
           in addLabel $ mkFor <$> expression generator
                               <*> traverse exprToLHS targets
                               <*> suite bodyClause -}
       Py.Fun name args _ body ->
           let funBody = fmap (Lab stmt) $ funDefinition name args body
           in addLabel $ Letrec <$> fmap (:[]) funBody <*> cont
       Py.Conditional guards els ->
           addLabel $ Let Nothing <$> foldr ifelse (suite els) guards <*> cont
       Py.Assign dsts src -> do src' <- expression src
                                assignments stmt cont (reverse dsts) src'
       Py.Return me -> -- Process, then discard statements after the return
                       addLabel $ Return <$> maybeExpression me <* cont
       Py.NonLocal xs -> do
         mapM_ nonlocalDeclaration xs
         cont
       Py.Global xs -> do
         mapM_ globalDeclaration xs
         cont
       _ -> fail $ "Cannot translate statement:\n" ++ Py.prettyText stmt
    where
      -- An if-else clause
      ifelse (guard, ifTrue) ifFalse = 
          addLabel $ Cond <$> expression guard
                          <*> suite ifTrue
                          <*> ifFalse

      addLabel f = Lab stmt <$> f

-- For each assignment in a multiple-assignment statement,
-- assign to one variable, then use that variable as the source value
-- for the next assignment.
assignments :: Py.Statement
            -> Cvt LabExpr
            -> [Py.Expr]
            -> LabExpr
            -> Cvt LabExpr
assignments stmt cont (v:vs) src = do
  lhs <- exprToLHS v            -- Bind variable

  -- Create an expression to get the value of the variable that was just bound
  let vExpr = case lhs of Lab l (Parameter v) -> Lab l (Variable v)
  body <- assignments stmt cont vs vExpr
  return $ Lab stmt $ Let (Just lhs) src body

-- After all variables are assigned, continue
assignments _ cont [] _ = cont

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
lambda args body = enter $ \locals ->
    Function locals <$> traverse parameter args <*> expression body

function :: [Py.Parameter] -> Py.Suite -> Cvt Function
function args body = enter $ \locals ->
    Function locals <$> traverse parameter args <*> suite body

funDefinition :: Py.Ident -> [Py.Parameter] -> Py.Suite -> Cvt FunDef
funDefinition name params body =
    FunDef <$> definition name <*> function params body

-------------------------------------------------------------------------------
-- Exported functions

-- | Convert a Python statement to a Pyon expression.
convertStatement :: Py.Statement -> NameSupply -> Either [String] LabExpr
convertStatement stmt names =
    let computation = finalStatement stmt
    in case runAndGetErrors computation names
       of (_, result) -> result

-- | Convert a Python module to a Pyon module.
convertModule :: Py.Module -> NameSupply -> Either [String] [Lab FunDef]
convertModule mod names =
    let computation =
            case mod
            of Py.Module statements -> enterGlobal $ \_ -> topLevel statements
    in case runAndGetErrors computation names
       of (_, result) -> result

-- | Parse a Python module.
parseModule :: String           -- ^ File contents
            -> String           -- ^ File name
            -> Either [String] [Lab FunDef]
parseModule stream path =
    case Py.parseModule stream path
    of Left err  -> Left [show err]
       Right mod -> case convertModule mod [1..]
                    of Left err   -> Left err
                       Right defs -> Right defs
