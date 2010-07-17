
{-# LANGUAGE FlexibleContexts, DeriveDataTypeable #-}
module Pyon.LowLevel.Syntax where

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

data Prim =
    PrimAddZ !Signedness !Size  -- ^ Add two integers
  | PrimSubZ !Signedness !Size  -- ^ Subtract Y from X
  | PrimModZ !Signedness !Size  -- ^ Remainder (floor) of X modulo Y
  | PrimMaxZ !Signedness !Size  -- ^ Compute maximum
  | PrimAddP                    -- ^ Add a native unsigned integer to a
                                --   (owned or non-owned) pointer.  The result
                                --   is a non-owned pointer.
  | PrimLoad !ValueType         -- ^ Load a value from an (owned or non-owned) 
                                --   pointer.
  | PrimStore !ValueType        -- ^ Store a value to an (owned or non-owned) 
                                --   pointer.

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
    -- | Return a value
    ValA Val
    -- | Call a function (possibly with the wrong number of arguments)
  | CallA Val [Val]
    -- | Perform a primitive operation (such as 'add' or 'load').
    --   Must have exactly the right number of arguments.
  | PrimA !Prim [Val]
    -- | Pack a statically typed record value.
  | PackA !StaticRecord [Val]
    -- | Unpack a statically typed record value.
  | UnpackA !StaticRecord Val
    -- | Allocate some bytes of local storage.  The given value is the
    -- parameter-passing convention of the object to allocate.
    -- The storage is live for the duration of the expression.
  | AllocA !ParamVar Val Exp
    -- | Branch based on a Boolean or integer value
  | SwitchA Val [Alt]

-- | An expression
data Exp =
    -- | Evaluate and return the return value of an atom
    ReturnE Atom
    -- | Bind an atom's result to temporary variables
  | LetE [ParamVar] Atom Exp
    -- | Define local functions
  | LetrecE [Def] Exp

data Fun = Fun [ParamVar] ValueType Exp

type Alt = (Lit, Exp)
type Def = (ParamVar, Fun)

data Module = Module [Def]
            deriving(Typeable)

newVar :: Supplies m (Ident Var) => Maybe Label -> ValueType -> m Var
newVar name ty = do
  ident <- fresh
  return $ Var ident name ty

newAnonymousVar :: Supplies m (Ident Var) => ValueType -> m Var
newAnonymousVar ty = newVar Nothing ty

