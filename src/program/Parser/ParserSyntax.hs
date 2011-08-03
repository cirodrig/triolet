
{- This file defines the temporary AST used by the parser.
-- It is nearly a copy of the Language.Python AST.  Unlike that AST,
-- variables have globally unique IDs, there is information about
-- variable scopes, and a few parts of the AST are simplified.
 -}

{-# LANGUAGE ExistentialQuantification #-}
module Parser.ParserSyntax where

import Data.IORef
import Foreign.Ptr
import {-# SOURCE #-} Parser.SSA

import qualified Language.Python.Common.AST as Python
import Common.SourcePos(SourcePos)
import Export
import Untyped.Data(ParserVarBinding)
import Untyped.Builtins

type PVar = Var Int
type PParameter = Parameter Int
type PExpr = Expr Int
type PIterFor t = IterFor Int t
type PIterIf t = IterIf Int t
type PComprehension t = Comprehension Int t
type PStmt = Stmt Int

-- | A Python variable.
-- Different variables have different IDs, though they can have
-- the same name.
-- There is already a Python object created for preexisting variables 
-- (such as builtin functions).  If no Python object already exists, 
-- 'varPythonPtr' is NULL.  Otherwise, it holds a borrowed reference
-- to the corresponding object.
-- already have that existed 
data Var id =
    Var
    { varName           :: String
    , varID             :: !id
    , varPythonPtr      :: {-# UNPACK #-} !(Ptr ())
    }
    deriving(Eq, Ord, Show)

makeVar :: String -> Int -> PVar
makeVar name id = Var name id nullPtr            

-- | Create global variables recognized by the parser.  The variables are 
-- assigned consecutive IDs starting at the given ID.
createParserGlobals :: Int -> [(Var Int, ParserVarBinding)]
createParserGlobals n = zipWith predefined_var [n..] predefinedBindings
  where
    predefined_var n (name, binding) = (Var name n nullPtr, binding)

data Literal =
    IntLit !Integer
  | FloatLit !Double
  | ImaginaryLit !Double
  | BoolLit !Bool
  | NoneLit

data Expr id =
    -- Terminals
    Variable SourcePos (Var id)
  | Literal SourcePos Literal
    -- Python expressions
  | Tuple SourcePos [Expr id]
  | Unary SourcePos !Python.OpSpan (Expr id)
  | Binary SourcePos !Python.OpSpan (Expr id) (Expr id)
  | Subscript SourcePos (Expr id) [Expr id]
  | Slicing SourcePos (Expr id) [Slice id]
  | ListComp SourcePos (IterFor id Expr)
  | Generator SourcePos (IterFor id Expr)
  | Call SourcePos (Expr id) [(Expr id)]
  | Cond SourcePos (Expr id) (Expr id) (Expr id) -- condition, true, false
  | Lambda SourcePos [Parameter id] (Expr id)
  | Let SourcePos (Parameter id) (Expr id) (Expr id)

-- | A component of a slice expression
data Slice id =
    SliceSlice SourcePos (Expr id) (Expr id) (Maybe (Expr id)) 
  | ExprSlice (Expr id)

type Annotation id = Maybe (Expr id)

data IterFor id a =
    IterFor SourcePos [Parameter id] (Expr id) (Comprehension id a)

data IterIf id a =
    IterIf SourcePos (Expr id) (Comprehension id a)

data Comprehension id a =
    CompFor (IterFor id a)
  | CompIf (IterIf id a)
  | CompBody (a id)

data Stmt id =
    ExprStmt
    { stmtPos :: !SourcePos 
    , stmtExpr :: Expr id
    }
  | Assign 
    { stmtPos :: !SourcePos 
    , stmtLhs :: Parameter id
    , stmtRhs :: Expr id
    }
  | If 
    { stmtPos :: SourcePos 
    , stmtCond :: Expr id
    , stmtTruePath :: Suite id
    , stmtFalsePath :: Suite id
    , stmtJoinPoint :: !(Maybe JoinNode)
    }
  | DefGroup 
    { stmtPos :: SourcePos
    , stmtDefs :: [Func id]
    }
  | FallThrough 
    { stmtPos :: SourcePos
    , stmtID :: !Int
    , stmtSuccessor :: {-# UNPACK #-} !(IORef (Maybe JoinNode))
    }
  | Return 
    { stmtPos :: SourcePos 
    , stmtID :: !Int
    , stmtSuccessor :: {-# UNPACK #-} !(IORef (Maybe JoinNode))
    , stmtRhs :: Expr id
    }

type Suite id = [Stmt id]

data Parameter id =
    Parameter (Var id) (Annotation id)
  | TupleParam [Parameter id]

type ForallAnnotation id = [(Var id, Maybe (Expr id))] 

data Func id =
  Func 
  { funcPos :: !SourcePos 
  , funcName :: Var id 
  , funcAnnotation :: Maybe (ForallAnnotation id) 
  , funcParams :: [Parameter id] 
  , funcReturnAnnotation :: Annotation id
  , funcBody :: Suite id
  , funcJoinPoint :: !(Maybe JoinNode)
  }

data ExportItem id =
  ExportItem 
  { exportPos :: !SourcePos 
  , exportSpec :: !ExportSpec
  , exportVar :: Var id
  , exportType :: Expr id
  }

data Module id = Module String [[Func id]] [ExportItem id]