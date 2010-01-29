
{- This file defines the temporary AST used by the parser.
-- It is nearly a copy of the Language.Python AST.  Unlike that AST,
-- variables have globally unique IDs, there is information about
-- variable scopes, and a few parts of the AST are simplified.
 -}

{-# LANGUAGE ExistentialQuantification #-}
module Parser.ParserSyntax where

import Foreign.Ptr
import Python(PyPtr)

import qualified Language.Python.Common.AST as Python
import Language.Python.Common.AST(Ident, AssignOp, Op)

-- | A Python variable.
-- Different variables have different IDs, though they can have
-- the same name.
-- There is already a Python object created for preexisting variables 
-- (such as builtin functions).  If no Python object already exists, 
-- 'varPythonPtr' is NULL.  Otherwise, it holds a borrowed reference
-- to the corresponding object.
-- already have that existed 
data Var =
    Var
    { varName           :: String
    , varID             :: {-# UNPACK #-} !Int
    , varPythonPtr      :: {-# UNPACK #-} !PyPtr
    }
    deriving(Eq, Ord, Show)
            
makeVar :: String -> Int -> Var
makeVar name id = Var name id nullPtr            

makePredefinedVar :: String -> Int -> PyPtr -> Var
makePredefinedVar = Var

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
  | Unary !Python.OpSpan Expr
  | Binary !Python.OpSpan Expr Expr
  | ListComp (IterFor Expr)
  | Generator Locals (IterFor Expr)
  | Call Expr [Expr]
  | Cond Expr Expr Expr -- condition, true, false
  | Lambda [Parameter] Expr

type Annotation = Maybe Expr

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
    Parameter Var Annotation
  | TupleParam [Parameter]

data Func = Func Var Locals (Maybe [Var]) [Parameter] Annotation Suite

data Module = Module [[Func]]