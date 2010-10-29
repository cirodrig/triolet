
{-# LANGUAGE TypeFamilies, Rank2Types, EmptyDataDecls, StandaloneDeriving,
    FlexibleInstances #-}
module LLParser.AST where

import Data.List

import Gluon.Common.Label
import LowLevel.Types
import qualified LowLevel.Syntax as LL

data Parsed

type family Expr a :: *
type family RecordName a :: *
type family TypeName a :: *
type family VarName a :: *

type instance Expr Parsed = BaseExpr Parsed
type instance RecordName Parsed = String
type instance TypeName Parsed = String
type instance VarName Parsed = String

data BinOp =
    MulOp                       -- ^ '*'
  | ModOp                       -- ^ '%'
  | AddOp                       -- ^ '+'
  | SubOp                       -- ^ '-'
  | PointerAddOp                -- ^ '^+'
  | AtomicAddOp                 -- ^ '!+'
  | CmpEQOp                     -- ^ '=='
  | CmpNEOp                     -- ^ '!='
  | CmpLTOp                     -- ^ '<'
  | CmpLEOp                     -- ^ '<='
  | CmpGTOp                     -- ^ '>'
  | CmpGEOp                     -- ^ '>='
  deriving(Show)

data UnaryOp = NegateOp deriving(Show)

-- | A data type, represented by a primitive type, a record type, or bytes.
data Type a =
    -- | A primitive type
    PrimT !PrimType
    -- | A named type; could be a record type or a type parameter.
  | RecordT (RecordName a)
    -- | Featureless bytes, with given size and alignment.
  | BytesT (Expr a) (Expr a)
    -- | A type application of a named type to arguments.
  | AppT (Type a) [Type a]

type FieldName = String

-- | An external symbol declaration, giving the Pyon name and/or externally 
-- visible name of a symbol.
--
-- External symbols can have pointer or owned type.
data ExternDecl a =
    -- | An externally visible Pyon symbol, defined in this file or in another
    -- file.
    ExternDecl !PrimType Label (Maybe String)
    -- | An imported symbol, assigned a local name
  | ImportDecl !PrimType (VarName a) String

-- | A definition
data Def a =
    RecordDefEnt !(RecordDef a)
  | DataDefEnt !(DataDef a)
  | FunctionDefEnt !(FunctionDef a)

data RecordDef a =
  RecordDef
  { recordName :: RecordName a
  , recordParams :: [TypeName a]
  , recordFields :: [FieldDef a]
  }

findFieldIndex :: FieldName -> RecordDef a -> Maybe Int
findFieldIndex fname r = findIndex match_name $ recordFields r
  where
    match_name (FieldDef _ nm) = nm == fname

data FieldDef a = FieldDef (Type a) FieldName

data DataDef a =
  DataDef
  { dataName :: VarName a
  , dataType :: !PrimType
  , dataValue :: Expr a
  }

-- | A function or procedure definition
data FunctionDef a =
  FunctionDef
  { functionName :: VarName a
  , functionIsProcedure :: !Bool
  , functionParams :: Parameters a
  , functionReturns :: [Type a]
  , functionBody :: Stmt a
  }

data Parameter a = Parameter (Type a) (VarName a)
type Parameters a = [Parameter a]

-- | A record field.  The field is a record name followed by a sequence of
-- field names, and possibly a type cast.
data Field a = Field (RecordName a) [FieldName] (Maybe (Type a))

data BaseExpr a =
    -- | A variable
    VarE (VarName a)
    -- | An integer literal
  | IntLitE (Type a) !Integer
    -- | A floating-point literal
  | FloatLitE (Type a) !Double
    -- | A boolean literal
  | BoolLitE !Bool
    -- | The NULL value
  | NullLitE
    -- | Construct a record value
  | RecordE (RecordName a) [Expr a]
    -- | Get a reference to an object field from a pointer expression
  | FieldE (Expr a) (Field a)
    -- | Load a field
  | LoadFieldE (Expr a) (Field a)
    -- | Dereference a pointer (only valid in LValue expressions)
  | DerefE (Expr a)
    -- | Load from a pointer
  | LoadE (Type a) (Expr a)
    -- | Call a function
  | CallE [Type a] (Expr a) [Expr a]
    -- | Call a procedure
  | PrimCallE [Type a] (Expr a) [Expr a]
    -- | Unary operator
  | UnaryE !UnaryOp (Expr a)
    -- | Binary operator
  | BinaryE !BinOp (Expr a) (Expr a)
    -- | Type cast an expression
  | CastE (Expr a) (Type a)
    -- | Size of a data type
  | SizeofE (Type a)
    -- | Alignment of a data type
  | AlignofE (Type a)
    -- | Wildcard (only valid in LValue expressions)
  | WildE

data LValue a =
    -- | Assign a variable
    VarL (VarName a)
    -- | Store into a pointer
  | StoreL (Expr a)
    -- | Store into a field of an object
  | StoreFieldL (Expr a) (Field a)
    -- | Unpack a record into its fields
  | UnpackL (RecordName a) [LValue a]
    -- | Wildcard; match and ignore a value
  | WildL

data Atom a =
    ValA [Expr a]

data Stmt a =
    LetS [LValue a] (Atom a) (Stmt a)
  | IfS (Expr a) (Stmt a) (Stmt a) (Maybe ([LValue a], Stmt a))
  | ReturnS (Atom a)

deriving instance Show (Type Parsed)
deriving instance Show (Def Parsed)
deriving instance Show (RecordDef Parsed)
deriving instance Show (FieldDef Parsed)
deriving instance Show (DataDef Parsed)
deriving instance Show (FunctionDef Parsed)
deriving instance Show (Parameter Parsed)
deriving instance Show (Field Parsed)
deriving instance Show (BaseExpr Parsed)
deriving instance Show (Atom Parsed)
deriving instance Show (LValue Parsed)
deriving instance Show (Stmt Parsed)

