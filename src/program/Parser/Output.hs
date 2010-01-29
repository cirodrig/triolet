
{-# LANGUAGE MultiParamTypeClasses,
             TypeSynonymInstances,
             FlexibleInstances,
             Rank2Types #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Parser.Output
    (Exportable(..), runExport, Inherit(Inherit))
where

import Control.Exception
import Control.Monad.State
import Control.Monad.Trans
import Data.List
import qualified Data.Map as Map
import Foreign.Ptr
import System.IO.Unsafe(unsafePerformIO)
import qualified Language.Python.Common.AST as Py
import qualified Language.Python.Common.Pretty as Py
import Language.Python.Common.PrettyAST()

import Parser.ParserSyntax
import Python

data Env =
    Env
    { py_RuntimeError       :: !PyPtr
    , py_PythonVariable     :: !PyPtr
    , py_VariableParam      :: !PyPtr
    , py_TupleParam         :: !PyPtr
    , py_VariableExpr       :: !PyPtr
    , py_LiteralExpr        :: !PyPtr
    , py_TupleExpr          :: !PyPtr
    , py_UnaryExpr          :: !PyPtr
    , py_BinaryExpr         :: !PyPtr
    , py_ListCompExpr       :: !PyPtr
    , py_GeneratorExpr      :: !PyPtr
    , py_CallExpr           :: !PyPtr
    , py_CondExpr           :: !PyPtr
    , py_LambdaExpr         :: !PyPtr
    , py_ForIter            :: !PyPtr
    , py_IfIter             :: !PyPtr
    , py_DoIter             :: !PyPtr
    , py_ExprStmt           :: !PyPtr
    , py_AssignStmt         :: !PyPtr
    , py_ReturnStmt         :: !PyPtr
    , py_IfStmt             :: !PyPtr
    , py_DefGroupStmt       :: !PyPtr
    , py_Function           :: !PyPtr
    , py_Module             :: !PyPtr
    , py_BITWISEAND         :: !PyPtr
    , py_BITWISEOR          :: !PyPtr
    , py_BITWISEXOR         :: !PyPtr
    , py_ADD                :: !PyPtr
    , py_SUB                :: !PyPtr
    , py_DIV                :: !PyPtr
    , py_FLOORDIV           :: !PyPtr
    , py_MUL                :: !PyPtr
    , py_MOD                :: !PyPtr
    , py_POWER              :: !PyPtr
    , py_LT                 :: !PyPtr
    , py_GT                 :: !PyPtr
    , py_EQ                 :: !PyPtr
    , py_GE                 :: !PyPtr
    , py_LE                 :: !PyPtr
    , py_NE                 :: !PyPtr
    , py_ARROW              :: !PyPtr
    , py_NEGATE             :: !PyPtr
    , py_COMPLEMENT         :: !PyPtr
    , py_NOT                :: !PyPtr
    }

-- Get references to objects needed on the Python side
mkEnv :: IO Env
mkEnv =
    withPyPtr (importModule "pyon.ast.parser_ast") $ \mod -> do
      withPyPtr (importModule "pyon.ast.operators") $ \op -> do
        builtins <- getBuiltins

        runtimeError <- getItemString builtins "RuntimeError"
        py_IncRef runtimeError  -- getItemString doesn't return a new reference

        pythonVariable <- getAttr mod "PythonVariable"
        variableParam <- getAttr mod "VariableParam"
        tupleParam <- getAttr mod "TupleParam"
        variableExpr <- getAttr mod "VariableExpr"
        literalExpr <- getAttr mod "LiteralExpr"
        tupleExpr <- getAttr mod "TupleExpr"
        unaryExpr <- getAttr mod "UnaryExpr"
        binaryExpr <- getAttr mod "BinaryExpr"
        listCompExpr <- getAttr mod "ListCompExpr"
        generatorExpr <- getAttr mod "GeneratorExpr"
        callExpr <- getAttr mod "CallExpr"
        condExpr <- getAttr mod "CondExpr"
        lambdaExpr <- getAttr mod "LambdaExpr"
        forIter <- getAttr mod "ForIter"
        ifIter <- getAttr mod "IfIter"
        doIter <- getAttr mod "DoIter"
        exprStmt <- getAttr mod "ExprStmt"
        assignStmt <- getAttr mod "AssignStmt"
        returnStmt <- getAttr mod "ReturnStmt"
        ifStmt <- getAttr mod "IfStmt"
        defGroupStmt <- getAttr mod "DefGroupStmt"
        function <- getAttr mod "Function"
        module_ <- getAttr mod "Module"

        bitwiseandOp <- getAttr op "BITWISEAND"
        bitwiseorOp <- getAttr op "BITWISEOR"
        bitwisexorOp <- getAttr op "BITWISEXOR"
        addOp <- getAttr op "ADD"
        subOp <- getAttr op "SUB"
        divOp <- getAttr op "DIV"
        floordivOp <- getAttr op "FLOORDIV"
        mulOp <- getAttr op "MUL"
        modOp <- getAttr op "MOD"
        powerOp <- getAttr op "POWER"
        ltOp  <- getAttr op "LT"
        gtOp  <- getAttr op "GT"
        eqOp  <- getAttr op "EQ"
        leOp  <- getAttr op "LE"
        geOp  <- getAttr op "GE"
        neOp  <- getAttr op "NE"
        arrowOp <- getAttr op "ARROW"
        negateOp <- getAttr op "NEGATE"
        complementOp <- getAttr op "COMPLEMENT"
        notOp <- getAttr op "NOT"

        return $ Env { py_RuntimeError = runtimeError
                     , py_PythonVariable = pythonVariable
                     , py_VariableParam = variableParam
                     , py_TupleParam = tupleParam
                     , py_VariableExpr = variableExpr
                     , py_LiteralExpr = literalExpr
                     , py_TupleExpr = tupleExpr
                     , py_UnaryExpr = unaryExpr
                     , py_BinaryExpr = binaryExpr
                     , py_ListCompExpr = listCompExpr
                     , py_GeneratorExpr = generatorExpr
                     , py_CallExpr = callExpr
                     , py_CondExpr = condExpr
                     , py_LambdaExpr = lambdaExpr
                     , py_ForIter = forIter
                     , py_IfIter = ifIter
                     , py_DoIter = doIter
                     , py_ExprStmt = exprStmt
                     , py_AssignStmt = assignStmt
                     , py_ReturnStmt = returnStmt
                     , py_IfStmt = ifStmt
                     , py_DefGroupStmt = defGroupStmt
                     , py_Function = function
                     , py_Module = module_
                     , py_BITWISEAND = bitwiseandOp
                     , py_BITWISEOR = bitwiseorOp
                     , py_BITWISEXOR = bitwisexorOp
                     , py_ADD = addOp
                     , py_SUB = subOp
                     , py_DIV = divOp
                     , py_FLOORDIV = floordivOp
                     , py_MUL = mulOp
                     , py_MOD = modOp
                     , py_POWER = powerOp
                     , py_LT = ltOp
                     , py_GT = gtOp
                     , py_EQ = eqOp
                     , py_LE = leOp
                     , py_GE = geOp
                     , py_NE = neOp
                     , py_ARROW = arrowOp
                     , py_NEGATE = negateOp
                     , py_COMPLEMENT = complementOp
                     , py_NOT = notOp
                     }

-- Release the references in an Env
freeEnv :: Env -> IO ()
freeEnv env = mapM_ decrefField
              [ py_RuntimeError
              , py_PythonVariable
              , py_VariableParam
              , py_TupleParam
              , py_VariableExpr
              , py_LiteralExpr
              , py_TupleExpr
              , py_UnaryExpr
              , py_BinaryExpr
              , py_ListCompExpr
              , py_GeneratorExpr
              , py_CallExpr
              , py_CondExpr
              , py_LambdaExpr
              , py_ForIter
              , py_IfIter
              , py_DoIter
              , py_ExprStmt
              , py_AssignStmt
              , py_ReturnStmt
              , py_IfStmt
              , py_DefGroupStmt
              , py_Function
              , py_Module
              , py_BITWISEAND
              , py_BITWISEOR
              , py_BITWISEXOR
              , py_ADD
              , py_SUB
              , py_DIV
              , py_FLOORDIV
              , py_MUL
              , py_MOD
              , py_POWER
              , py_LT
              , py_GT
              , py_EQ
              , py_LE
              , py_GE
              , py_NE
              , py_ARROW
              , py_NEGATE
              , py_COMPLEMENT
              , py_NOT
              ]
    where
      decrefField field = py_DecRef (field env)

-------------------------------------------------------------------------------

-- For each variable, keep track of the corresponding Python object.
-- These are not owned references.
data ExportState =
    ExportState
    { stVars :: Map.Map Var PyPtr }

newtype Export a =
    Export {runEx :: Env -> ExportState -> IO (ExportState, a)}

instance Monad Export where
    return x = Export $ \_ s -> return (s, x)
    m >>= k = Export $ \r s -> do (s', x) <- runEx m r s
                                  runEx (k x) r s'

instance MonadState ExportState Export where
    get   = Export $ \_ s -> return (s, s)
    put s = Export $ \_ _ -> return (s, ())

instance MonadIO Export where
    liftIO m = Export $ \_ s -> do x <- m
                                   return (s, x)

runExport :: Export PyPtr -> IO PyPtr
runExport m =
    bracket mkEnv freeEnv $ \env ->
        do (_, p) <- runEx m env initialState
           return p
    where
      initialState = ExportState {stVars = Map.empty}

liftEndo :: (forall a. IO a -> IO a) -> Export a -> Export a
liftEndo t m = Export $ \r s -> t (runEx m r s)

liftTrans :: (forall b. (a -> IO b) -> IO b) -> (a -> Export b) -> Export b
liftTrans t f = Export $ \r s -> t (\x -> runEx (f x) r s)

bracketOnErrorExport :: Export a -> (a -> IO b) -> (a -> Export c) -> Export c
bracketOnErrorExport acquire release body =
    let wrapRelease (_, x) = release x
    in  Export $ \r s ->
        let wrapBody (s', x) = runEx (body x) r s'
        in bracketOnError (runEx acquire r s) wrapRelease wrapBody

-- like withPyPtrExc, but for the Export monad
withPyPtrExcEx f body = bracketOnErrorExport f py_DecRef body

bracketExport :: Export a -> (a -> IO b) -> (a -> Export c) -> Export c
bracketExport acquire release body =
    let wrapRelease (_, x) = release x
    in  Export $ \r s ->
        let wrapBody (s', x) = runEx (body x) r s'
        in bracket (runEx acquire r s) wrapRelease wrapBody

-- like withPyPtr, but for the Export monad
withPyPtrEx f body = bracketExport f py_DecRef body

-- Borrow a reference to one of the Python objects from the environment.
readEnv :: (Env -> PyPtr) -> Export PyPtr
readEnv field = Export $ \env s -> let ptr = field env
                                   in return (s, ptr)

-- Look up the Python object that was created from a variable, if any.
-- This returns a borrowed reference.
lookupPtrOfVar :: Var -> Export (Maybe PyPtr)
lookupPtrOfVar v = gets lookupPtr
    where
      lookupPtr st = Map.lookup v (stVars st)

-- Insert a new variable into the state.
-- This overwrites an existing binding.
savePtrOfVar :: Var -> PyPtr -> Export ()
savePtrOfVar v ptr = modify savePtr
    where
      savePtr st = st {stVars = Map.insert v ptr (stVars st)}

-------------------------------------------------------------------------------

-- Data types that can be exported to Python, using objects looked up
-- from 'Env'.
class Exportable a where
    toPythonEx :: a -> Export PyPtr

-- Inherit the marshaling method for ordinary Python code
newtype Inherit a = Inherit a

instance Python a => Exportable (Inherit a) where
    toPythonEx (Inherit x) = liftIO $ toPython x

instance Exportable a => Exportable [a] where
    toPythonEx xs =
        liftTrans (withPyPtrExc (newList $ length xs)) $ \list ->
            let marshalItem index x =
                    withPyPtrExcEx (toPythonEx x) $ \obj ->
                        liftIO $ setListItem list index obj
            in do mapMIndex_ marshalItem xs
                  return list
                  
instance Exportable a => Exportable (Maybe a) where
  toPythonEx Nothing = liftIO pyNone
  toPythonEx (Just x) = toPythonEx x

-- Return a Python variable corresponding to the current variable.
-- Only one Python variable is created for each variable.
createPythonVar :: Var -> Export PyPtr
createPythonVar v = lookupPtrOfVar v >>= check
    where
      -- If found, return a new reference
      check (Just ptr) = do liftIO $ py_IncRef ptr
                            return ptr
      check Nothing = do
        let py_var = varPythonPtr v
        ptr <- if py_var == nullPtr
               then do mk_python_var <- readEnv py_PythonVariable
                       liftIO $ call2 mk_python_var 
                         (AsString $ varName v) (varID v)
               else liftIO $ do py_IncRef py_var
                                return py_var
        savePtrOfVar v ptr
        return ptr

-- Convert Haskell tuples to Python tuples
toPythonTupleEx :: [Export PyPtr] -> Export PyPtr
toPythonTupleEx xs =
    liftTrans (withPyPtrExc (newTuple $ length xs)) $ \tuple ->
        let marshalItem index x =
                withPyPtrExcEx x $ \obj ->
                    liftIO $ setTupleItem tuple index obj
        in do mapMIndex_ marshalItem xs
              return tuple

instance (Exportable a, Exportable b) => Exportable (a, b) where
    toPythonEx (x, y) =
        toPythonTupleEx [toPythonEx x, toPythonEx y]

instance (Exportable a, Exportable b, Exportable c) =>
         Exportable (a, b, c) where
    toPythonEx (x, y, z) =
        toPythonTupleEx [toPythonEx x, toPythonEx y, toPythonEx z]

call1Ex :: Exportable a => Export PyPtr -> a -> Export PyPtr
call1Ex fun mkx =
    withPyPtrExcEx (toPythonTupleEx [toPythonEx mkx]) $ \tuple ->
        do ptr <- fun
           liftIO $ checkNull $ pyObject_CallObject ptr tuple

call2Ex :: (Exportable a, Exportable b) =>
           Export PyPtr -> a -> b -> Export PyPtr
call2Ex fun mkx mky =
    withPyPtrExcEx (toPythonTupleEx [ toPythonEx mkx
                                    , toPythonEx mky]) $ \tuple ->
        do ptr <- fun
           liftIO $ checkNull $ pyObject_CallObject ptr tuple

call3Ex :: (Exportable a, Exportable b, Exportable c) =>
           Export PyPtr -> a -> b -> c -> Export PyPtr
call3Ex fun mkx mky mkz =
    withPyPtrExcEx (toPythonTupleEx [ toPythonEx mkx
                                    , toPythonEx mky
                                    , toPythonEx mkz]) $ \tuple ->
        do ptr <- fun
           liftIO $ checkNull $ pyObject_CallObject ptr tuple

call4Ex :: (Exportable a, Exportable b, Exportable c, Exportable d) =>
           Export PyPtr -> a -> b -> c -> d -> Export PyPtr
call4Ex fun mkx mky mkz mkw =
    withPyPtrExcEx (toPythonTupleEx [ toPythonEx mkx
                                    , toPythonEx mky
                                    , toPythonEx mkz
                                    , toPythonEx mkw]) $ \tuple ->
        do ptr <- fun
           liftIO $ checkNull $ pyObject_CallObject ptr tuple

call5Ex :: (Exportable a, Exportable b, Exportable c, Exportable d, Exportable e) =>
           Export PyPtr -> a -> b -> c -> d -> e -> Export PyPtr
call5Ex fun mkx mky mkz mkw mkv =
    withPyPtrExcEx (toPythonTupleEx [ toPythonEx mkx
                                    , toPythonEx mky
                                    , toPythonEx mkz
                                    , toPythonEx mkw
                                    , toPythonEx mkv]) $ \tuple ->
        do ptr <- fun
           liftIO $ checkNull $ pyObject_CallObject ptr tuple

call6Ex :: (Exportable a, Exportable b, Exportable c, Exportable d, Exportable e, Exportable f) =>
           Export PyPtr -> a -> b -> c -> d -> e -> f -> Export PyPtr
call6Ex fun mkx mky mkz mkw mkv mku =
    withPyPtrExcEx (toPythonTupleEx [ toPythonEx mkx
                                    , toPythonEx mky
                                    , toPythonEx mkz
                                    , toPythonEx mkw
                                    , toPythonEx mkv
                                    , toPythonEx mku]) $ \tuple ->
        do ptr <- fun
           liftIO $ checkNull $ pyObject_CallObject ptr tuple

-- Convert an association list to a Python dictionary
toPythonDictEx :: (Exportable key, Exportable value) =>
                  [(key, value)] -> Export PyPtr
toPythonDictEx xs = do
  withPyPtrExcEx (liftIO pyDict_New) $ \dict -> do
      -- For each element, marshal key and value, and put them into the dict
      forM_ xs $ \(k, v) ->
          withPyPtrEx (toPythonEx k) $ \kPtr ->
              withPyPtrEx (toPythonEx v) $ \vPtr ->
                  liftIO (setDictItem dict kPtr vPtr)
      return dict

instance Exportable Var where
    toPythonEx v = createPythonVar v

instance Python Literal where
    toPython (IntLit n)   = toPython n
    toPython (FloatLit d) = toPython d
    toPython (BoolLit b)  = toPython b
    toPython NoneLit      = pyNone

instance Exportable (Py.Op a) where
  toPythonEx (Py.Plus {})        = readEnv py_ADD
  toPythonEx (Py.Minus {})       = readEnv py_SUB
  toPythonEx (Py.Divide {})      = readEnv py_DIV
  toPythonEx (Py.Multiply {})    = readEnv py_MUL
  toPythonEx (Py.Modulo {})      = readEnv py_MOD
  toPythonEx (Py.FloorDivide {}) = readEnv py_FLOORDIV
  toPythonEx (Py.Exponent {})    = readEnv py_POWER
  toPythonEx (Py.LessThan {})    = readEnv py_LT
  toPythonEx (Py.GreaterThan {}) = readEnv py_GT
  toPythonEx (Py.Equality {})    = readEnv py_EQ
  toPythonEx (Py.GreaterThanEquals {}) = readEnv py_GE
  toPythonEx (Py.LessThanEquals {}) = readEnv py_LE
  toPythonEx (Py.NotEquals {})   = readEnv py_NE
  toPythonEx (Py.Arrow {})       = readEnv py_ARROW
  toPythonEx (Py.BinaryAnd {})   = readEnv py_BITWISEAND
  toPythonEx (Py.BinaryOr {})    = readEnv py_BITWISEOR
  toPythonEx (Py.Xor {})         = readEnv py_BITWISEXOR
  toPythonEx op             = error $ "Cannot translate operator to Python: " ++ Py.prettyText op

-- Language-Python uses the same names for unary and binary operators.
-- This newtype wrapper is used to disambiguate the 'Exportable' instance.
newtype AsUnary a = AsUnary (Py.Op a)

instance Exportable (AsUnary a) where
    toPythonEx (AsUnary (Py.Minus {}))  = readEnv py_NEGATE
    toPythonEx (AsUnary (Py.Invert {})) = readEnv py_COMPLEMENT
    toPythonEx (AsUnary (Py.Not {}))    = readEnv py_NOT
    toPythonEx (AsUnary op)        = error $ "Cannot translate operator to Python: " ++ Py.prettyText op

instance Exportable Parameter where
    toPythonEx (Parameter v ann) = call2Ex (readEnv py_VariableParam) v ann
    toPythonEx (TupleParam es)   = call1Ex (readEnv py_TupleParam) es

-- Convert locals to a map from variable to (bool, bool, bool)
instance Exportable Locals where
    toPythonEx (Locals vars) = toPythonDictEx (map asAssoc vars)
        where
          asAssoc v =
              ( scopeVar v
              , Inherit (isParameter v, hasNonlocalUse v, hasNonlocalDef v)
              )

instance Exportable Stmt where
    toPythonEx (ExprStmt e) = call1Ex (readEnv py_ExprStmt) e
    toPythonEx (Assign lhs e) = call2Ex (readEnv py_AssignStmt) lhs e
    toPythonEx (Return e) = call1Ex (readEnv py_ReturnStmt) e
    toPythonEx (If e tr fa) = call3Ex (readEnv py_IfStmt) e tr fa
    toPythonEx (DefGroup fs) = call1Ex (readEnv py_DefGroupStmt) fs

instance Exportable Expr where
    toPythonEx (Variable v)    = call1Ex (readEnv py_VariableExpr) v
    toPythonEx (Literal l)     = call1Ex (readEnv py_LiteralExpr) (Inherit l)
    toPythonEx (Tuple es)      = call1Ex (readEnv py_TupleExpr) es
    toPythonEx (Unary op e)    = call2Ex (readEnv py_UnaryExpr) (AsUnary op) e
    toPythonEx (Binary op e f) = call3Ex (readEnv py_BinaryExpr) op e f
    toPythonEx (ListComp it)   = call1Ex (readEnv py_ListCompExpr) it
    toPythonEx (Generator l f) = call2Ex (readEnv py_GeneratorExpr) f l
    toPythonEx (Call f xs)     = call2Ex (readEnv py_CallExpr) f xs
    toPythonEx (Cond c tr fa)  = call3Ex (readEnv py_CondExpr) c tr fa
    toPythonEx (Lambda ps e)   = call2Ex (readEnv py_LambdaExpr) ps e
    
instance Exportable (IterFor Expr) where
    toPythonEx (IterFor [param] e comp) =
        call3Ex (readEnv py_ForIter) param e comp

    toPythonEx (IterFor _ e comp) =
        error "Cannot translate 'for' generator to Python"

instance Exportable (IterIf Expr) where
    toPythonEx (IterIf e comp) =
        call2Ex (readEnv py_IfIter) e comp

instance Exportable (Comprehension Expr) where
    toPythonEx (CompFor iter) = toPythonEx iter
    toPythonEx (CompIf iter)  = toPythonEx iter
    toPythonEx (CompBody x)   = call1Ex (readEnv py_DoIter) x

instance Exportable Func where
    toPythonEx (Func name locals qvars params ann body) =
        call6Ex (readEnv py_Function) name qvars params ann body locals

instance Exportable Module where
    toPythonEx (Module groups) = call1Ex (readEnv py_Module) groups