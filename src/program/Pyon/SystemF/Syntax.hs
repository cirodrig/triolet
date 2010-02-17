
{-# LANGUAGE DeriveDataTypeable #-}
module Pyon.SystemF.Syntax
    (PyonType,
     PyonClass(..),
     Var,
     Lit(..),
     Pat(..),
     TyPat(..),
     ExpInfo, defaultExpInfo,
     Exp(..),
     Fun(..),
     Def(..),
     Module(..)
    )
where

import Data.Typeable

import Gluon.Common.Identifier
import Gluon.Common.Label
import qualified Gluon.Core as Gluon

-- | Pyon types are type-level Gluon expressions.
type PyonType = Gluon.Exp Gluon.Core

-- | The Pyon type classes.
data PyonClass = EqClass | OrdClass | TraversableClass
               deriving(Show, Typeable)

-- | Pyon variables are the same as Gluon variables.
type Var = Gluon.Var

-- | Literal values.
--
-- Integer and floating-point iteral values have an unspecified type.
-- The type is given when the literal is used in an expression.
data Lit =
    IntL !Integer
  | FloatL {-# UNPACK #-} !Double
  | BoolL {-# UNPACK #-} !Bool
  | NoneL
  deriving(Typeable)

-- | Patterns.
data Pat =
    WildP PyonType              -- ^ Wildcard pattern
  | VarP Var PyonType           -- ^ Variable pattern binding
  | TupleP [Pat]                -- ^ Tuple pattern
  deriving(Typeable)
          
-- | Type-level patterns.
data TyPat = TyPat Gluon.Var PyonType
           deriving(Typeable)

-- | Information common to all expressions.
data ExpInfo = ExpInfo

-- | Default values of 'ExpInfo'.
defaultExpInfo :: ExpInfo
defaultExpInfo = ExpInfo

-- | Expressions.
data Exp =
    -- | A variable reference
    VarE
    { expInfo :: ExpInfo
    , expVar :: Var
    }
    -- | A constructor value
  | ConE
    { expInfo :: ExpInfo
    , expCon :: Gluon.Con
    }
    -- | A literal value
  | LitE
    { expInfo :: ExpInfo
    , expLit :: !Lit
    , expType :: PyonType
    }
    -- | An undefined value
  | UndefinedE
    { expInfo :: ExpInfo
    , expType ::  PyonType
    }
    -- | Build a tuple
  | TupleE
    { expInfo :: ExpInfo
    , expFields :: [Exp]
    }
    -- | Type application
  | TyAppE
    { expInfo :: ExpInfo
    , expOper :: Exp
    , expTyArg :: PyonType
    }
    -- | Function call
  | CallE
    { expInfo :: ExpInfo
    , expOper :: Exp
    , expArgs :: [Exp]
    }
    -- | If-then-else expression
  | IfE
    { expInfo :: ExpInfo
    , expCond :: Exp
    , expTrueCase :: Exp
    , expFalseCase :: Exp
    }
    -- | Lambda expression
  | FunE
    { expInfo :: ExpInfo
    , expFun :: Fun
    }
    -- | Let expression
  | LetE
    { expInfo :: ExpInfo
    , expBinder :: Pat
    , expValue :: Exp
    , expBody :: Exp
    }
    -- | Recursive definition group
  | LetrecE
    { expInfo :: ExpInfo
    , expDefs :: [Def]
    , expBody :: Exp
    }
    -- | Create a class dictionary
  | DictE
    { expInfo :: ExpInfo
    , expClass :: PyonClass
    , expType :: PyonType
    , expSuperclasses :: [Exp]
    , expMethods :: [Exp]
    }
    -- | Select a class method
  | MethodSelectE
    { expInfo :: ExpInfo
    , expClass :: PyonClass
    , expType :: PyonType
    , expMethodIndex :: {-# UNPACK #-} !Int
    , expArg :: Exp
    }
  deriving(Typeable)

data Fun =
  Fun { funTyParams :: [TyPat]  -- ^ Type parameters
      , funParams :: [Pat]      -- ^ Object parameters
      , funReturnType :: PyonType -- ^ Return type
      , funBody :: Exp
      }
  deriving(Typeable)

data Def = Def Var Fun
         deriving(Typeable)

data Module = Module [Def]
            deriving(Typeable)