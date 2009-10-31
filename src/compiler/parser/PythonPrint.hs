
{-# LANGUAGE ExistentialQuantification, TypeSynonymInstances, FlexibleInstances #-}
module PythonPrint where

import Data.List
import qualified Language.Python.Version3.Syntax.AST as Py
import ParserSyntax

-- Pure text formatting
parenthesize :: ShowS -> ShowS
parenthesize x = showChar '(' . x . showChar ')'
brackets :: ShowS -> ShowS
brackets x = showChar '[' . x . showChar ']'
concatList :: [ShowS] -> ShowS
concatList xs z = foldr ($) z xs
commas xs = intersperse (showChar ',') xs
showPythonList xs = brackets $ concatList $ commas $ map pyShow xs
showPythonTuple xs = parenthesize $ concatList $ commas $ map pyShow xs

-- Data that can be marshaled in the form of Python code
class PyShow a where
    pyShow :: a -> ShowS

-- A marshalable object
data P = forall a. PyShow a => P a

instance PyShow P where pyShow (P x) = pyShow x

-- A string that should be marshaled to a Python string
newtype PyShowString = PyShowString String

instance PyShow PyShowString where
    pyShow (PyShowString s) = shows s

showPythonString :: String -> ShowS
showPythonString = showString

data PyFunCall = PyFunCall String [P]

instance PyShow Int where pyShow n = shows n

instance PyShow a => PyShow [a] where pyShow = showPythonList

instance PyShow PyFunCall where pyShow (PyFunCall n xs) = showCall' n xs

showCall :: ShowS -> [P] -> ShowS
showCall fun args = fun . showPythonTuple args

showCall' :: String -> [P] -> ShowS
showCall' fun args = showCall (showPythonString fun) args

instance PyShow Var where
    pyShow v = showCall' "makeVariable"
               [P $ PyShowString (varName v), P (varID v)]

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
showExpr (Call e args)   = showCall' "CallExpr" [P args]
showExpr (Cond c tr fa)  = showCall' "CondExpr" [P c, P tr, P fa]
showExpr (Binary op l r) = showCall' "BinaryExpr" [P op, P l, P r]
showExpr (Unary op arg)  = showCall' "UnaryExpr" [P op, P arg]
showExpr (Lambda f)      = showCall' "FunExpr" [P f]
showExpr (Generator gen) = showCall' "GeneratorExpr" [P gen]
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
    pyShow (Function params body) = showCall' "Function" [P params, P body]

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
