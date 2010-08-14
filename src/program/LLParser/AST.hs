
{-# LANGUAGE TypeFamilies, EmptyDataDecls, StandaloneDeriving, FlexibleInstances #-}
module LLParser.AST where

import LowLevel.Types

data Parsed

type family RecordName a :: *
type family VarName a :: *
     
type instance RecordName Parsed = String
type instance VarName Parsed = String

data BinOp =
    AddOp
  | AtomicAddOp
  | CmpEQOp
  deriving(Show)

-- | A data type, represented by a primitive type, a record type, or bytes.
data Type a = PrimT !PrimType
            | RecordT (RecordName a)
            | BytesT (Expr a) (Expr a)

type FieldName = String

-- | A definition
data Def a =
    RecordDefEnt !(RecordDef a)
  | DataDefEnt !(DataDef a)
  | FunctionDefEnt !(FunctionDef a)

data RecordDef a =
  RecordDef
  { recordName :: RecordName a
  , recordParams :: Parameters a
  , recordFields :: [FieldDef a]
  }

data FieldDef a = FieldDef (Type a) FieldName

data DataDef a =
  DataDef
  { dataName :: VarName a 
  , dataValue :: Expr a
  }

-- | A function or procedure definition
data FunctionDef a =
  FunctionDef
  { functionName :: VarName a
  , functionIsProcedure :: !Bool
  , functionParams :: Parameters a
  , functionReturns :: [Type a]
  , functionBody :: Block a
  }

data Parameter a = Parameter (Type a) (VarName a)
type Parameters a = [Parameter a]

-- | A record field.  The field is a record name followed by a sequence of
-- field names, and possibly a type cast.
data Field a = Field (RecordName a) [FieldName] (Maybe (Type a))

data Expr a =
    -- | A variable
    VarE (VarName a)
    -- | An integer literal
  | IntLitE (Type a) !Integer
    -- | A floating-point literal
  | FloatLitE (Type a) !Double
    -- | Construct a record value
  | RecordE (RecordName a) [Expr a]
    -- | Get a reference to a field of an expression
  | FieldE (Expr a) (Field a)
    -- | Load a field
  | LoadFieldE (Expr a) (Field a)
    -- | Call a function
  | CallE [Type a] (Expr a) [Expr a]
    -- | Call a procedure
  | PrimCallE [Type a] (Expr a) [Expr a]
    -- | Binary operator
  | BinaryE BinOp (Expr a) (Expr a)
    -- | Type cast an expression
  | CastE (Expr a) (Type a)
    -- | Size of a data type
  | SizeofE (Type a)
    -- | Alignment of a data type
  | AlignofE (Type a)

data LValue a =
    -- | Assign a variable
    VarL (VarName a)
    -- | Store into memory
  | StoreFieldL (Expr a) (Field a)

data Atom a =
    ValA [Expr a]
  | IfA (Expr a) (Block a) (Block a)

data Stmt a =
  LetS [LValue a] (Atom a)

data Block a = Block [Stmt a] (Atom a)

deriving instance Show (Type Parsed)
deriving instance Show (Def Parsed)
deriving instance Show (RecordDef Parsed)
deriving instance Show (FieldDef Parsed)
deriving instance Show (DataDef Parsed)
deriving instance Show (FunctionDef Parsed)
deriving instance Show (Parameter Parsed)
deriving instance Show (Field Parsed)
deriving instance Show (Expr Parsed)
deriving instance Show (Atom Parsed)
deriving instance Show (LValue Parsed)
deriving instance Show (Stmt Parsed)
deriving instance Show (Block Parsed)
