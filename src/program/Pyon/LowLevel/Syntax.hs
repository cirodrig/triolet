
{-# LANGUAGE FlexibleContexts, DeriveDataTypeable #-}
module Pyon.LowLevel.Syntax where

import Data.Function
import Data.Typeable

import Gluon.Common.Identifier
import Gluon.Common.Supply
import Gluon.Common.Label
import Gluon.Core(Con)
import Pyon.LowLevel.Types
import Pyon.LowLevel.Record

-- | A type that may be put into a variable
data ValueType = PrimType !PrimType
               | RecordType !StaticRecord

-- | A comparison operation
data CmpOp = CmpEQ | CmpNE | CmpLT | CmpLE | CmpGT | CmpGE

data Prim =
    PrimAddZ !Signedness !Size  -- ^ Add two integers
  | PrimSubZ !Signedness !Size  -- ^ Subtract Y from X
  | PrimModZ !Signedness !Size  -- ^ Remainder (floor) of X modulo Y
  | PrimMaxZ !Signedness !Size  -- ^ Compute maximum
  | PrimCmpZ !Signedness !Size !CmpOp -- ^ Boolean compare integers
  | PrimAddP                    -- ^ Add a native unsigned integer to a
                                --   (owned or non-owned) pointer.  The result
                                --   is a non-owned pointer.
  | PrimLoad !ValueType         -- ^ Load a value from an (owned or non-owned) 
                                --   pointer.
  | PrimStore !ValueType        -- ^ Store a value to an (owned or non-owned) 
                                --   pointer.
  | PrimAAddZ !Signedness !Size -- ^ Atomically add the target of a pointer to
                                --   an integer.  Return the original value at
                                --   that address.
  | PrimCastToOwned             -- ^ Cast a non-owned pointer to an owned
                                --   pointer.  The reference count is not
                                --   adjusted.
  | PrimCastFromOwned           -- ^ Cast an owned pointer to a non-owned
                                --   pointer.  The reference count is not
                                --   adjusted.

data Lit =
    UnitL                       -- ^ The unit value
  | NullL                       -- ^ The NULL pointer
  | BoolL !Bool                 -- ^ A boolean
  | IntL !Signedness !Size !Integer -- ^ An integer
  | FloatL !Size !Double        -- ^ A floating-point number

data Var =
  Var
  { varID :: {-# UNPACK #-} !(Ident Var)
  , varName :: !(Maybe Label)
  , varType :: !ValueType
  }

instance Eq Var where
  (==) = (==) `on` varID

instance Ord Var where
  compare = compare `on` varID

type ParamVar = Var

-- | A value
data Val =
    VarV Var
  | RecV !StaticRecord [Val]
  | ConV !Con
  | LitV !Lit
  | LamV Fun

-- | An atomic operation.  Some non-atomic operations are included here.
-- This is modeled after ANF, but isn't truly ANF since expressions can be 
-- recursive.
data Atom =
    -- | Return some values
    ValA [Val]
    -- | Call a closure-based function 
    -- (possibly with the wrong number of arguments).
    -- The function must be an owned pointer.
  | CallA Val [Val]
    -- | Call a primitive function, using the C calling convention extended
    -- with support for multiple return values.
    -- Unlike closure-based calls, this call must have exactly the right
    -- number of arguments.
    -- The function must be a non-owned pointer.
  | PrimCallA Val [Val]
    -- | Perform a primitive operation (such as 'add' or 'load').
    --   Must have exactly the right number of arguments.
  | PrimA !Prim [Val]
    -- | Pack a statically typed record value.
  | PackA !StaticRecord [Val]
    -- | Unpack a statically typed record value.
  | UnpackA !StaticRecord Val
    -- | Branch based on a Boolean or integer value
  | SwitchA Val [Alt]

-- | A block of computation, consisting of some statements followed by an
-- atom.  The block's return value is the atom's return value.
data Block = Block [Stm] !Atom

-- | A statement.  Statements are executed for their effect and have no
-- return value.
data Stm =
    -- | Bind an atom's result to temporary variables
    LetE [ParamVar] Atom
    -- | Define local functions
  | LetrecE [FunDef]

data Fun = Fun [ParamVar] [ValueType] Block

type Alt = (Lit, Block)

-- | A function definition
data FunDef = FunDef !ParamVar Fun

-- | A static data definition
data DataDef = DataDef !ParamVar !StaticRecord ![Val]

data Module =
  Module 
  { moduleFunctions :: [FunDef]
  , moduleData :: [DataDef]
  }
  deriving(Typeable)

newVar :: Supplies m (Ident Var) => Maybe Label -> ValueType -> m Var
newVar name ty = do
  ident <- fresh
  return $ Var ident name ty

newAnonymousVar :: Supplies m (Ident Var) => ValueType -> m Var
newAnonymousVar ty = newVar Nothing ty

litType :: Lit -> PrimType
litType UnitL = UnitType
litType NullL = PointerType
litType (BoolL _) = BoolType
litType (IntL sgn sz _) = IntType sgn sz
litType (FloatL sz _) = FloatType sz