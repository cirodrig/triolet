-- | System F representation of Pyon code.
--
-- This is a short-lived representation produced as the output of type
-- inference.  It is translated to another form with the help of type
-- information.
-- Since it has no dependent types, renaming is not required.

{-# LANGUAGE DeriveDataTypeable, EmptyDataDecls, TypeFamilies, FlexibleInstances #-}
module Pyon.SystemF.Syntax
    (PyonClass(..),
     pyonClassConstructor, pyonClassNumSuperclasses, pyonClassNumMethods,
     ExpOf, TypeOf,
     RExp, RType, RPat, RTyPat, RFun, RDef, RModule,
     PyonType,
     Var,
     Lit(..),
     Pat(..),
     TyPat(..),
     ExpInfo, defaultExpInfo,
     Exp(..),
     Fun(..),
     Def(..),
     Module(..),
     isValueExp
    )
where

import Data.Typeable

import Gluon.Common.Error
import Gluon.Common.Identifier
import Gluon.Common.Label
import Gluon.Common.SourcePos
import qualified Gluon.Core as Gluon
import Gluon.Core(Rec)

import Pyon.SystemF.Builtins

-- | The Pyon type classes.
data PyonClass =
  EqClass | OrdClass | TraversableClass | AdditiveClass | VectorClass
  deriving(Show, Typeable)

pyonClassConstructor :: PyonClass -> Gluon.Con
pyonClassConstructor EqClass = pyonBuiltin the_eqDict
pyonClassConstructor OrdClass = pyonBuiltin the_ordDict
pyonClassConstructor TraversableClass = pyonBuiltin the_traversableDict
pyonClassConstructor AdditiveClass = pyonBuiltin the_additiveDict
pyonClassConstructor VectorClass = pyonBuiltin the_vectorDict

pyonClassNumSuperclasses :: PyonClass -> Int
pyonClassNumSuperclasses EqClass = 0
pyonClassNumSuperclasses OrdClass = 1
pyonClassNumSuperclasses TraversableClass = 0
pyonClassNumSuperclasses AdditiveClass = 0
pyonClassNumSuperclasses VectorClass = 1

pyonClassNumMethods :: PyonClass -> Int
pyonClassNumMethods EqClass = 2
pyonClassNumMethods OrdClass = 4
pyonClassNumMethods TraversableClass = 1
pyonClassNumMethods AdditiveClass = 3
pyonClassNumMethods VectorClass = 2

type family ExpOf a :: *
type family TypeOf a :: *

type instance ExpOf Rec = Exp Rec
type instance TypeOf Rec = Gluon.ExpOf Rec Rec

type RExp = Exp Rec
type RType = PyonType
type RPat = Pat Rec
type RTyPat = TyPat Rec
type RDef = Def Rec
type RFun = Fun Rec
type RModule = Module Rec

-- | Pyon types are type-level Gluon expressions.
type PyonType = TypeOf Rec

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
data Pat syn =
    WildP (TypeOf syn)              -- ^ Wildcard pattern
  | VarP Var (TypeOf syn)           -- ^ Variable pattern binding
  | TupleP [Pat syn]                -- ^ Tuple pattern
  deriving(Typeable)
          
-- | Type-level patterns.
data TyPat syn = TyPat Gluon.Var (TypeOf syn)
           deriving(Typeable)

-- | Information common to all expressions.
type ExpInfo = Gluon.SynInfo

-- | Default values of 'ExpInfo'.
defaultExpInfo :: ExpInfo
defaultExpInfo = Gluon.internalSynInfo Gluon.ObjectLevel

-- | Expressions.
data Exp syn =
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
    , expType :: TypeOf syn
    }
    -- | An undefined value
  | UndefinedE
    { expInfo :: ExpInfo
    , expType ::  TypeOf syn
    }
    -- | Build a tuple
  | TupleE
    { expInfo :: ExpInfo
    , expFields :: [ExpOf syn]
    }
    -- | Type application
  | TyAppE
    { expInfo :: ExpInfo
    , expOper :: ExpOf syn
    , expTyArg :: TypeOf syn
    }
    -- | Function call
  | CallE
    { expInfo :: ExpInfo
    , expOper :: ExpOf syn
    , expArgs :: [ExpOf syn]
    }
    -- | If-then-else expression
  | IfE
    { expInfo :: ExpInfo
    , expCond :: ExpOf syn
    , expTrueCase :: ExpOf syn
    , expFalseCase :: ExpOf syn
    }
    -- | Lambda expression
  | FunE
    { expInfo :: ExpInfo
    , expFun :: Fun syn
    }
    -- | Let expression
  | LetE
    { expInfo :: ExpInfo
    , expBinder :: Pat syn
    , expValue :: ExpOf syn
    , expBody :: ExpOf syn
    }
    -- | Recursive definition group
  | LetrecE
    { expInfo :: ExpInfo
    , expDefs :: [Def syn]
    , expBody :: ExpOf syn
    }
    -- | Create a class dictionary
  | DictE
    { expInfo :: ExpInfo
    , expClass :: PyonClass
    , expType :: TypeOf syn     -- ^ Class instance type
    , expSuperclasses :: [ExpOf syn]
    , expMethods :: [ExpOf syn]
    }
    -- | Select a class method
  | MethodSelectE
    { expInfo :: ExpInfo
    , expClass :: PyonClass
    , expType :: TypeOf syn     -- ^ Class instance type
    , expMethodIndex :: {-# UNPACK #-} !Int
    , expArg :: ExpOf syn       -- ^ Class dictionary
    }
  deriving(Typeable)
          
instance HasSourcePos (Exp syn) where
  getSourcePos _ = noSourcePos
  -- Not implemented!
  setSourcePos _ _ = internalError "HasSourcePos.setSourcePos"

data Fun syn =
  Fun { funTyParams :: [TyPat syn] -- ^ Type parameters
      , funParams :: [Pat syn]      -- ^ Object parameters
      , funReturnType :: TypeOf syn -- ^ Return type
      , funMonad :: !Gluon.Con -- ^ Which monad this function inhabits 
                              -- (Stream or Action)
      , funBody :: ExpOf syn
      }
  deriving(Typeable)

data Def syn = Def Var (Fun syn)
         deriving(Typeable)

data Module syn = Module [Def syn]
            deriving(Typeable)

-- | Return True only if the given expression has no side effects.
-- This function examines only expression constructors, and avoids inspecting
-- let or letrec expressions.
--
-- Constructors 'CallE', 'LetE', and 'LetrecE' are assumed to have side
-- effects.  Lambda expressions have no side effects, since they return but
-- do not execute their function.

isValueExp :: Exp Rec -> Bool
isValueExp expression =
  case expression
  of VarE {} -> True
     ConE {} -> True
     LitE {} -> True
     UndefinedE {} -> True
     TupleE {expFields = fs} -> all isValueExp fs
     TyAppE {expOper = e} -> isValueExp e
     CallE {} -> False
     IfE {expCond = c, expTrueCase = t, expFalseCase = f} ->
       isValueExp c && isValueExp t && isValueExp f
     FunE {} -> True
     LetE {} -> False
     LetrecE {} -> False
     DictE {expSuperclasses = scs, expMethods = ms} ->
       all isValueExp scs && all isValueExp ms
     MethodSelectE {expArg = a} -> isValueExp a