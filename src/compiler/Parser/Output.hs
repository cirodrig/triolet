
{-# LANGUAGE MultiParamTypeClasses,
             TypeSynonymInstances,
             FlexibleInstances,
             Rank2Types #-}
module Parser.Output
    (Exportable(..), runExport, Inherit(Inherit))
where

import Control.Exception
import Control.Monad.State
import Control.Monad.Trans
import Data.List
import qualified Data.Map as Map
import System.IO.Unsafe(unsafePerformIO)
import qualified Language.Python.Version3.Syntax.AST as Py
import Parser.ParserSyntax
import Python

data Env =
    Env
    { py_RuntimeError       :: PyPtr
    , py_VariableExpr       :: PyPtr
    , py_LiteralExpr        :: PyPtr
    , py_UnaryExpr          :: PyPtr
    , py_BinaryExpr         :: PyPtr
    , py_Function           :: PyPtr
    }

-- Get references to objects needed on the Python side
mkEnv :: IO Env
mkEnv = do withPyPtr (importModule "ast.parser_ast") $ \mod -> do
             builtins <- getBuiltins
             runtimeError <- getItemString builtins "RuntimeError"
             variableExpr <- getAttr mod "PythonVariable"
             literalExpr <- getAttr mod "LiteralExpr"
             unaryExpr <- getAttr mod "UnaryExpr"
             binaryExpr <- getAttr mod "BinaryExpr"
             function <- getAttr mod "Function"
             return $ Env { py_RuntimeError = runtimeError
                          , py_VariableExpr = variableExpr
                          , py_LiteralExpr = literalExpr
                          , py_UnaryExpr = unaryExpr
                          , py_BinaryExpr = binaryExpr
                          , py_Function = function
                          }

-- Release the references in an Env
freeEnv :: Env -> IO ()
freeEnv env = mapM_ decrefField
              [ py_RuntimeError
              , py_VariableExpr
              , py_LiteralExpr
              , py_UnaryExpr
              , py_BinaryExpr
              , py_Function
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

runExport :: Export PyPtr -> IO PyPtr
runExport m =
    bracket mkEnv freeEnv $ \env ->
        do (_, p) <- runEx m env initialState
           return p
    where
      initialState = ExportState {stVars = Map.empty}

-------------------------------------------------------------------------------

-- Return a Python variable corresponding to the current variable.
-- Only one Python variable is created for each variable.
createPythonVar :: Var -> Export PyPtr
createPythonVar v = lookupPtrOfVar v >>= check
    where
      -- If found, return a new reference
      check (Just ptr) = do liftIO $ py_IncRef ptr
                            return ptr
      -- Otherwise, create a new object
      check Nothing = do
        ptr <- call2Ex (readEnv py_VariableExpr)
                       (Inherit $ AsString $ varName v)
                       (Inherit $ varID v)
        savePtrOfVar v ptr
        return ptr

class Exportable a where
    toPythonEx :: a -> Export PyPtr

newtype AsRuntimeError a = AsRuntimeError a

-- Marshal all exceptions as RuntimeError
instance Exception a => Exportable (AsRuntimeError a) where
    toPythonEx (AsRuntimeError e) =
        let message = Inherit $ AsString (show e)
        in call1Ex (readEnv py_RuntimeError) message

-- Convert Haskell tuples to Python tuples
toPythonTupleEx :: [Export PyPtr] -> Export PyPtr
toPythonTupleEx xs =
    liftTrans (withPyPtrExc (newTuple $ length xs)) $ \tuple ->
        let marshalItem index x =
                withPyPtrExcEx x $ \obj ->
                    liftIO $ setTupleItem tuple index obj
        in do mapMIndex_ marshalItem xs
              return tuple

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


instance Exportable Var where
    toPythonEx v = createPythonVar v

instance Python Literal where
    toPython (IntLit n)   = toPython n
    toPython (FloatLit d) = toPython d
    toPython (BoolLit b)  = toPython b
    toPython NoneLit      = pyNone

instance Python Py.Op

instance Exportable Parameter

instance Exportable Locals

instance Exportable Stmt

instance Exportable Expr where
    toPythonEx (Variable v)    = call1Ex (readEnv py_VariableExpr) v
    toPythonEx (Literal l)     = call1Ex (readEnv py_LiteralExpr) (Inherit l)
    toPythonEx (Unary op e)    = call2Ex (readEnv py_UnaryExpr) (Inherit op) e
    toPythonEx (Binary op e f) = call3Ex (readEnv py_BinaryExpr) (Inherit op) e f

instance Exportable Func where
    toPythonEx (Func name locals params body) =
        call4Ex (readEnv py_Function) name locals params body

{-
-- A string that should be marshaled to a Python string
newtype PyShowString = PyShowString String

instance PyShow PyShowString where
    pyShow (PyShowString s) = shows s

showPythonString :: String -> ShowS
showPythonString = showString

data PyFunCall = PyFunCall String [P]

instance PyShow Int where pyShow n = shows n

instance PyShow a => PyShow [a] where pyShow = showPythonList

-- Represent a 'Maybe a' as a possibly-None value
instance PyShow a => PyShow (Maybe a) where
    pyShow Nothing  = showPythonString "None"
    pyShow (Just x) = pyShow x

instance PyShow PyFunCall where pyShow (PyFunCall n xs) = showCall' n xs

showCall :: ShowS -> [P] -> ShowS
showCall fun args = fun . showPythonTuple args

showCall' :: String -> [P] -> ShowS
showCall' fun args = showCall (showPythonString fun) args

instance PyShow Var where
    pyShow v = showCall' "makeVariable"
               [P $ PyShowString (varName v), P (varID v)]

instance PyShow Locals where
    pyShow (Locals vs) = showPythonDict $ map toLocal vs
        where
          toLocal v = (scopeVar v, BoolLit (hasNonlocalDef v))

instance PyShow Literal where
    pyShow (IntLit n)   = shows n
    pyShow (FloatLit d) = shows d
    pyShow (BoolLit b)  = showPythonString $
                          case b of {True -> "True"; False -> "False"}
    pyShow NoneLit      = showPythonString "None"

instance PyShow LabExpr where
    pyShow (Lab _ e) = showExpr e

showExpr (Variable v)    = showCall' "VariableExpr" [P v]
showExpr (Literal l)     = showCall' "LiteralExpr" [P l]
showExpr (Call e args)   = showCall' "CallExpr" [P e, P args]
showExpr (Cond c tr fa)  = showCall' "IfExpr" [P c, P tr, P fa]
showExpr (Binary op l r) = showCall' "BinaryExpr" [P op, P l, P r]
showExpr (Unary op arg)  = showCall' "UnaryExpr" [P op, P arg]
showExpr (Lambda f)      = showCall' "FunExpr" [P f]
showExpr (Generator locals gen) = showCall' "GeneratorExpr" [P locals, P gen]
showExpr (ListComp gen)  = showCall' "ListCompExpr" [P gen]
showExpr (Let lhs rhs e) = showCall' "LetExpr" [P lhs, P rhs, P e]
showExpr (Letrec fs e)   = showCall' "LetrecExpr" [P fs, P e]
showExpr (Return e)      = showCall' "ReturnExpr" [P e]

instance PyShow a => PyShow (Comprehension a) where
    pyShow (CompFor iter) = pyShow iter
    pyShow (CompIf iter)  = pyShow iter
    pyShow (CompBody e)   = showCall' "DoIter" [P e]

instance PyShow a => PyShow (IterFor a) where
    pyShow (IterFor params e c) = showCall' "ForIter"
                                  [P (ParamTuple params), P e, P c]

instance PyShow a => PyShow (IterIf a) where
    pyShow (IterIf e c) = showCall' "IfIter" [P e, P c]

instance PyShow Function where
    pyShow (Function locals params body) =
        showCall' "Function" [P params, P body, P locals]

instance PyShow (Lab Parameter) where
    pyShow (Lab _ (Parameter v)) = showCall' "VariableParam" [P v]

data ParamTuple = ParamTuple [Lab Parameter]

instance PyShow ParamTuple where
    pyShow (ParamTuple xs) = showPythonTuple xs

instance PyShow (Lab FunDef) where
    pyShow (Lab _ (FunDef v f)) = showCall' "FunctionDef" [P v, P f]

instance PyShow Py.Op where
    pyShow Py.And = showPythonString "operators.AND"
    pyShow Py.Or = showPythonString "operators.OR"
    pyShow Py.Not = showPythonString "operators.NOT"
    pyShow Py.Exponent = showPythonString "operators.EXPONENT"
    pyShow Py.LessThan = showPythonString "operators.LT"
    pyShow Py.GreaterThan = showPythonString "operators.GT"
    pyShow Py.Equality = showPythonString "operators.EQ"
    pyShow Py.GreaterThanEquals = showPythonString "operators.GE"
    pyShow Py.LessThanEquals = showPythonString "operators.LE"
    pyShow Py.NotEquals = showPythonString "operators.NE"
    pyShow Py.In = showPythonString "operators.IN"
    pyShow Py.Is = showPythonString "operators.IS"
    pyShow Py.IsNot = showPythonString "operators.ISNOT"
    pyShow Py.NotIn = showPythonString "operators.NOTIN"
    pyShow Py.BinaryOr = showPythonString "operators.BITWISE_OR"
    pyShow Py.Xor = showPythonString "operators.BITWISE_XOR"
    pyShow Py.BinaryAnd = showPythonString "operators.BITWISE_AND"
    pyShow Py.ShiftLeft = showPythonString "operators.SHIFT_LEFT"
    pyShow Py.ShiftRight = showPythonString "operators.SHIFT_RIGHT"
    pyShow Py.Multiply = showPythonString "operators.MULTIPLY"
    pyShow Py.Plus = showPythonString "operators.ADD"
    pyShow Py.Minus = showPythonString "operators.SUB"
    pyShow Py.Divide = showPythonString "operators.DIV"
    pyShow Py.FloorDivide = showPythonString "operators.FLOOR_DIV"
    pyShow Py.Invert = showPythonString "operators.INVERT"
    pyShow Py.Modulo = showPythonString "operators.MOD"
    pyShow Py.Dot = showPythonString "operators.DOT"
-}