
{-# LANGUAGE ExistentialQuantification #-}
module ParserSyntax where

import qualified Language.Python.Version3.Syntax.AST as Python
import Language.Python.Version3.Syntax.AST(Ident, AssignOp, Op)

-- | A Python variable.
-- Different variables have different IDs, though they can have
-- the same name.
data Var =
    Var
    { varName           :: String
    , varID             :: !Int
    }
    deriving(Show)

-- | A Python variable with scope information.
--
-- If a variable is a parameter, it cannot have a nonlocal definition.
--
-- Since we do not keep track of global uses and defs, global variables
-- are always marked as having nonlocal uses and defs.
data ScopeVar =
    ScopeVar
    { scopeVar       :: {-# UNPACK #-} !Var
    , isParameter    :: !Bool   -- ^ True if this is a function parameter
    , hasNonlocalUse :: !Bool   -- ^ True if the variable is used outside
                                -- of its scope; implied by hasNonlocalDef
    , hasNonlocalDef :: !Bool   -- ^ True if the variable is assigned outside
                                -- of its scope
    }

-- A list of the variables local to a scope, generated after a scope is
-- fully processed.
newtype Locals = Locals [ScopeVar]

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
  | Generator Locals (IterFor LabExpr)
  | ListComp (IterFor LabExpr)
    -- Python statements
  | Let LabParameter LabExpr LabExpr
  | Letrec [Lab FunDef] LabExpr
  -- | For [LabParameter] LabExpr LabExpr -- parameter, generator, body
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

data Function = Function Locals [LabParameter] LabExpr

data FunDef = FunDef Var !Function
