
{- This file defines the temporary AST used by the parser.
-- It is nearly a copy of the Language.Python AST.  Unlike that AST,
-- variables have globally unique IDs, there is information about
-- variable scopes, and a few parts of the AST are simplified.
 -}

{-# LANGUAGE ExistentialQuantification #-}
module Parser.ParserSyntax where

import qualified Language.Python.Version3.Syntax.AST as Python
import Language.Python.Version3.Syntax.AST(Ident, AssignOp, Op)

-- | A Python variable.
-- Different variables have different IDs, though they can have
-- the same name.
data Var =
    Var
    { varName           :: String
    , varID             :: {-# UNPACK #-} !Int
    }
    deriving(Eq, Ord, Show)

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
  | Tuple [Expr]
  | Unary !Op Expr
  | Binary !Op Expr Expr
  | ListComp (IterFor Expr)
  | Generator Locals (IterFor Expr)
  | Call Expr [Expr]
  | Cond Expr Expr Expr -- condition, true, false
  | Lambda [Parameter] Expr

data IterFor a =
    IterFor [Parameter] Expr (Comprehension a)

data IterIf a =
    IterIf Expr (Comprehension a)

data Comprehension a =
    CompFor (IterFor a)
  | CompIf (IterIf a)
  | CompBody a

data Stmt =
    ExprStmt Expr
  | Assign Parameter Expr
  | Return Expr
  | If Expr Suite Suite
  | DefGroup [Func]

type Suite = [Stmt]

data Parameter =
    Parameter Var
  | TupleParam [Parameter]

data Func = Func Var Locals [Parameter] Suite
