
{-# LANGUAGE TypeFamilies, Rank2Types, EmptyDataDecls, StandaloneDeriving,
    FlexibleInstances #-}
module LLParser.AST where

import Data.List

import LowLevel.Types
import LowLevel.Record(Mutability(..))
import Common.Label

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
  | DivOp                       -- ^ '/'
  | IntDivOp                    -- ^ '%/'
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
    -- | A named type; could be a record type, typedef, or type parameter.
  | NamedT (RecordName a)
    -- | Featureless bytes, with given size and alignment.
    -- Size and alignment are unsigned words.
  | BytesT (Expr a) (Expr a)
    -- | An array of values.  The array contents are either all mutable or
    --   all immutable.  Size is an unsigned word.
  | ArrayT !Mutability (Expr a) (Type a)
    -- | A type application of a named type to arguments.
  | AppT (Type a) [TypeArg a]

-- | An argument of a parametric type is either a type or an expression.
data TypeArg a = TypeArg (Type a) | ExprArg (Expr a)

type FieldName = String

-- | What kind of external data a thing is and what type it has.
data ExternType a =
    -- | A procedure with parameter and return types
    ExternProcedure [Type a] [Type a]
    -- | A function with parameter and return types
  | ExternFunction [Type a] [Type a]
    -- | A global variable, either Pointer or Owned type
  | ExternData PrimType

externTypePrimType :: ExternType a -> PrimType
externTypePrimType (ExternProcedure _ _) = PointerType
externTypePrimType (ExternFunction _ _)  = OwnedType
externTypePrimType (ExternData pt)       = pt

-- | An external symbol declaration, giving the Pyon name and/or externally 
-- visible name of a symbol.
--
data ExternDecl a =
    -- | An externally visible Pyon symbol, defined in this file or in another
    -- file.
    ExternDecl 
    { -- | Type of the external symbol
      externType :: !(ExternType a)
      -- | Symbol name
    , externLabel :: Label
    }
    -- | An imported symbol that was not created by the Pyon compiler.
  | ImportDecl 
    { -- | Type of the external symbol.  Must be procedure or data.
      externType :: !(ExternType a)
      -- | Symbol name
    , externLabel :: Label
      -- | The variable representing this symbol
    , externVar :: VarName a
    }

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
    match_name (FieldDef _ _ nm) = nm == fname

data FieldDef a = FieldDef !Mutability (Type a) FieldName

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
  , functionInlineRequest :: !Bool
  , functionLocals :: Locals a -- ^ Stack variables
  , functionParams :: Parameters a
  , functionReturns :: [Type a]
  , functionBody :: Stmt a
  }

data Parameter a = Parameter (Type a) (Maybe (VarName a))
type Parameters a = [Parameter a]
type Locals a = [Parameter a]

-- | A referene to a record field.  The field is a type followed by
-- a sequence of field names, and possibly a type cast.  The type must be
-- a 'NamedT' or an application of a 'NamedT'.
data Field a = Field (Type a) [FieldSpec a] (Maybe (Type a))

data FieldSpec a = RecordFS !FieldName
                 | ArrayFS (Expr a)

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
    -- | The unit value
  | NilLitE
    -- | Construct a record value
  | RecordE (Type a) [Expr a]
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
  | UnpackL (Type a) [LValue a]
    -- | Wildcard; match and ignore a value
  | WildL

data Atom a =
    ValA [Expr a]

-- | A statement.
data Stmt a =
    -- | An assignment statement
    LetS [LValue a] (Atom a) (Stmt a)
    -- | Local function definitions
  | LetrecS [FunctionDef a] (Stmt a)
    -- | Local type synonym definition.
    --   Code to compute the data type's layout 
    --   will be inserted in place of this statement.
  | TypedefS (RecordName a) (Type a) (Stmt a)
    -- | An if statement.  The statement may be followed by a continuation.
  | IfS (Expr a) (Stmt a) (Stmt a) (Maybe ([LValue a], Stmt a))
    -- | A while statement.  The loop-carried variables and their initial   
    -- values are given.  The statement may be followed by a continuation.
  | WhileS [(Parameter a, Expr a)] (Expr a) (Stmt a) (Maybe ([LValue a], Stmt a))
  | ReturnS (Atom a)

deriving instance Show (Type Parsed)
deriving instance Show (TypeArg Parsed)
deriving instance Show (Def Parsed)
deriving instance Show (RecordDef Parsed)
deriving instance Show (FieldDef Parsed)
deriving instance Show (DataDef Parsed)
deriving instance Show (FunctionDef Parsed)
deriving instance Show (Parameter Parsed)
deriving instance Show (Field Parsed)
deriving instance Show (FieldSpec Parsed)
deriving instance Show (BaseExpr Parsed)
deriving instance Show (Atom Parsed)
deriving instance Show (LValue Parsed)
deriving instance Show (Stmt Parsed)

