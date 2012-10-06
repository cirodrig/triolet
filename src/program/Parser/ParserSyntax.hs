
{- This file defines the temporary AST used by the parser.
-- It is nearly a copy of the Language.Python AST.  Unlike that AST,
-- variables have globally unique IDs, there is information about
-- variable scopes, and a few parts of the AST are simplified.
 -}

{-# LANGUAGE ExistentialQuantification, FlexibleContexts,
    UndecidableInstances, StandaloneDeriving #-}
module Parser.ParserSyntax where

import Compiler.Hoopl(LabelMap)
import Data.IORef
import qualified Data.Set as Set

import qualified Language.Python.Common.AST as Python
import Common.SourcePos(SourcePos)
import Export
import Untyped.Data(ParserVarBinding)
import Untyped.Builtins

data AST                        -- | ^ The AST stage of parsing

type PVar = Var AST
type PExpr = LExpr AST
type PSlice = Slice AST
type PIterFor = IterFor AST
type PIterIf = IterIf AST
type PIterLet = IterLet AST
type PComprehension = Comprehension AST
type PFunc = LFunc AST

-- | A set of live variables
type Liveness = Set.Set PVar
type MLiveness = Maybe Liveness

-- | A map from block ID to live variables
type Livenesses = LabelMap Liveness
type MLivenesses = Maybe Livenesses

type family VarID stage

type instance VarID AST = Int

-- | An object with source location information
data Loc a = Loc SourcePos a

unLoc :: Loc a -> a
unLoc (Loc _ a) = a

mapLoc :: (a -> a) -> Loc a -> Loc a
mapLoc f (Loc pos x) = Loc pos $! f x

-- | A Python variable.
-- Different variables have different IDs, though they can have
-- the same name.
data Var s =
    Var
    { varName           :: String
    , varID             :: !(VarID s)
    }

deriving instance Eq (VarID s) => Eq (Var s)
deriving instance Ord (VarID s) => Ord (Var s)
deriving instance Show (VarID s) => Show (Var s)

makeVar :: String -> Int -> PVar
makeVar name id = Var name id            

-- | Create global variables recognized by the parser.  The variables are 
-- assigned consecutive IDs starting at the given ID.
createParserGlobals :: Int -> [(PVar, ParserVarBinding)]
createParserGlobals n = zipWith predefined_var [n..] predefinedBindings
  where
    predefined_var n (name, binding) = (Var name n, binding)

data Literal =
    IntLit !Integer
  | FloatLit !Double
  | ImaginaryLit !Double
  | BoolLit !Bool
  | NoneLit

type LExpr s = Loc (Expr s)

data Expr s =
    -- Terminals
    Variable (Var s)
  | Literal Literal
    -- Python expressions
  | Tuple [LExpr s]
  | List [LExpr s]
  | Unary !Python.OpSpan (LExpr s)
  | Binary !Python.OpSpan (LExpr s) (LExpr s)
  | Subscript (LExpr s) [LExpr s]
  | Slicing (LExpr s) [Slice s]
  | ListComp (IterFor s)
  | Generator (IterFor s)
  | Call (LExpr s) [(LExpr s)]
  | Cond (LExpr s) (LExpr s) (LExpr s) -- condition, true, false
  | Lambda [Parameter s] (LExpr s)
  | Let (Parameter s) (LExpr s) (LExpr s)

-- | A component of a slice expression
data Slice id =
    SliceSlice SourcePos !(Maybe (LExpr id)) !(Maybe (LExpr id)) !(Maybe (Maybe (LExpr id)))
  | ExprSlice (LExpr id)

type Annotation id = Maybe (LExpr id)

data IterFor id =
    IterFor SourcePos [Parameter id] (LExpr id) (Comprehension id)

data IterIf id =
    IterIf SourcePos (LExpr id) (Comprehension id)

data IterLet id =
    IterLet SourcePos (Parameter id) (LExpr id) (Comprehension id)

data Comprehension id =
    CompFor (IterFor id)
  | CompIf (IterIf id)
  | CompLet (IterLet id)
  | CompBody (LExpr id)

data Stmt =
    ExprStmt
    { stmtPos :: !SourcePos 
    , stmtExpr :: PExpr
    }
  | Assign 
    { stmtPos :: !SourcePos 
    , stmtLhs :: Parameter AST
    , stmtRhs :: PExpr
    }
  | Assert 
    { stmtPos :: !SourcePos 
    , stmtExprs :: [PExpr]
    }
  | Require 
    { stmtPos :: !SourcePos 
    , stmtVar :: PVar
    , stmtExpr :: PExpr
    }
  | If 
    { stmtPos :: SourcePos 
    , stmtCond :: PExpr
    , stmtTruePath :: Suite
    , stmtFalsePath :: Suite
    }
  | DefGroup 
    { stmtPos :: SourcePos
    , stmtDefs :: [LFunc AST]
    }
  | Return 
    { stmtPos :: SourcePos 
    , stmtRhs :: PExpr
    }

type Suite = [Stmt]

data Parameter id =
    Parameter (Var id) (Annotation id)
  | TupleParam [Parameter id]

type ForallAnnotation id = [(Var id, Maybe (LExpr id))]

data FunPragma = FunPragma { funInline :: !Bool }

type LFunc id = Loc (Func id)

data FunSig id =
  FunSig
  { sigName             :: Var id
  , sigAnnotation       :: Maybe (ForallAnnotation id)
  , sigPragma           :: FunPragma
  , sigParams           :: [Parameter id] 
  , sigReturnAnnotation :: Annotation id
  }

data Func id =
  Func 
  { funcSignature        :: !(FunSig id)
  , funcBody             :: Suite
  }


data ExportItem id =
  ExportItem 
  { exportPos :: !SourcePos 
  , exportSpec :: !ExportSpec
  , exportVar :: Var id
  , exportType :: LExpr id
  }

data Module id = Module String [[LFunc id]] [ExportItem id]