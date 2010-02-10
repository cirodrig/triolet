
{-# LANGUAGE DeriveDataTypeable #-}
module Pyon.SystemF.Syntax where

import Data.Typeable

import Gluon.Common.Identifier
import Gluon.Common.Label
import qualified Gluon.Core as Gluon

type PyonType = Gluon.Exp Gluon.Core

data PyonClass = EqClass | OrdClass | TraversableClass
               deriving(Show, Typeable)

data Var =
  Var
  { varID   :: {-# UNPACK #-} !(Ident Var)
  , varName :: !(Maybe Label)
  }
  deriving(Typeable)

-- Literal values.
-- Integer and float literals have an unspecified type.
data Lit =
    IntL !Integer
  | FloatL !Double
  | BoolL !Bool
  | NoneL
  deriving(Typeable)

data Pat =
    WildP PyonType
  | VarP Var PyonType
  | TupleP [Pat]
  deriving(Typeable)

data TyPat = TyPat Gluon.Var PyonType
           deriving(Typeable)

data Exp =
    VarE Var
  | ConE Gluon.Con
  | LitE !Lit PyonType
  | UndefinedE PyonType
  | TupleE [Exp]
  | TyAppE Exp PyonType
  | CallE Exp [Exp]
  | IfE Exp Exp Exp
  | FunE Fun
  | LetE Pat Exp Exp
  | LetrecE [Def] Exp
    -- Create a class dictionary
  | DictE PyonClass PyonType [Exp] [Exp]
    -- Select a class method
  | MethodSelectE PyonClass PyonType Int Exp
  deriving(Typeable)

data Fun =
  Fun { funTyParams :: [TyPat]  -- ^ Type parameters
      , funParams :: [Pat]      -- ^ Object parameters
      , funBody :: Exp
      }
  deriving(Typeable)

data Def = Def Var Fun
         deriving(Typeable)

data Module = Module [Def]
            deriving(Typeable)