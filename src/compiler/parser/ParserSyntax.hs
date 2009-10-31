
{-# LANGUAGE ExistentialQuantification #-}
module ParserSyntax where

import qualified Language.Python.Version3.Syntax.AST as Python
import Language.Python.Version3.Syntax.AST(Ident, AssignOp, Op)

data Var =
    Var
    { varName :: String
    , varID   :: !Int
    }
    deriving(Show)

-- Expression are labeled with their original syntax tree equivalent.
-- To save space, we store the original showable object. 
data Lab a = forall lab. Show lab => Lab lab a

type LabExpr = Lab Expr
type LabArgument = Lab Expr
type LabParameter = Lab Parameter

instance Show (Lab a) where
    showsPrec n (Lab label _) = showsPrec n label

data Literal =
    IntLit !Integer
  | FloatLit !Double
  | BoolLit !Bool
  | NoneLit

data Expr =
    -- Terminals
    Variable Var
  | Literal Literal
    -- Python expressions
  | Call LabExpr [LabArgument]
  | Cond LabExpr LabExpr LabExpr -- condition, true, false
  | Binary !Op LabExpr LabExpr
  | Unary !Op LabExpr
  | Lambda Function
  | Generator (IterFor LabExpr)
  | ListComp (IterFor LabExpr)
    -- Python statements
  | Let LabParameter LabExpr LabExpr
  | Letrec [Lab FunDef] LabExpr
  | For [LabParameter] LabExpr LabExpr -- parameter, generator, body
  | Return LabExpr

data IterFor a =
    IterFor [LabParameter] LabExpr (Comprehension a)

data IterIf a =
    IterIf LabExpr (Comprehension a)

data Comprehension a =
    CompFor (IterFor a)
  | CompIf (IterIf a)
  | CompBody a

data Parameter =
    Parameter Var

data Function = Function [LabParameter] LabExpr

data FunDef = FunDef Var !Function
