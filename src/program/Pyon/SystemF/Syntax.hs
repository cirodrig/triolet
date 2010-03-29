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
     Rec,
     SFExpOf(..), TypeOf,
     SFRecExp,
     RExp, RType, RPat, RTyPat, RFun, RDef, RModule,
     Var,
     Lit(..),
     Pat(..),
     TyPat(..),
     ExpInfo, defaultExpInfo,
     SFExp,
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

data family SFExpOf a :: * -> *

type TypeOf = Gluon.ExpOf

type SFRecExp s = SFExpOf s s
type RecType s = TypeOf s s

type SFExp = SFExpOf Rec
type RExp = SFRecExp Rec
type RType = RecType Rec
type RPat = Pat Rec
type RTyPat = TyPat Rec
type RDef = Def Rec
type RFun = Fun Rec
type RModule = Module Rec

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
data Pat s =
    WildP (RecType s)              -- ^ Wildcard pattern
  | VarP Var (RecType s)           -- ^ Variable pattern binding
  | TupleP [Pat s]                 -- ^ Tuple pattern
  deriving(Typeable)
          
-- | Type-level patterns.
data TyPat s = TyPat Gluon.Var (RecType s)
             deriving(Typeable)

-- | Information common to all expressions.
type ExpInfo = Gluon.SynInfo

-- | Default values of 'ExpInfo'.
defaultExpInfo :: ExpInfo
defaultExpInfo = Gluon.internalSynInfo Gluon.ObjectLevel

-- | Expressions.
data instance SFExpOf Rec s =
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
    , expType :: RecType s
    }
    -- | An undefined value
  | UndefinedE
    { expInfo :: ExpInfo
    , expType ::  RecType s
    }
    -- | Build a tuple
  | TupleE
    { expInfo :: ExpInfo
    , expFields :: [SFRecExp s]
    }
    -- | Type application
  | TyAppE
    { expInfo :: ExpInfo
    , expOper :: SFRecExp s
    , expTyArg :: RecType s
    }
    -- | Function call
  | CallE
    { expInfo :: ExpInfo
    , expOper :: SFRecExp s
    , expArgs :: [SFRecExp s]
    }
    -- | If-then-else expression
  | IfE
    { expInfo :: ExpInfo
    , expCond :: SFRecExp s
    , expTrueCase :: SFRecExp s
    , expFalseCase :: SFRecExp s
    }
    -- | Lambda expression
  | FunE
    { expInfo :: ExpInfo
    , expFun :: Fun s
    }
    -- | Let expression
  | LetE
    { expInfo :: ExpInfo
    , expBinder :: Pat s
    , expValue :: SFRecExp s
    , expBody :: SFRecExp s
    }
    -- | Recursive definition group
  | LetrecE
    { expInfo :: ExpInfo
    , expDefs :: [Def s]
    , expBody :: SFRecExp s
    }
    -- | Create a class dictionary
  | DictE
    { expInfo :: ExpInfo
    , expClass :: PyonClass
    , expType :: RecType s     -- ^ Class instance type
    , expSuperclasses :: [SFRecExp s]
    , expMethods :: [SFRecExp s]
    }
    -- | Select a class method
  | MethodSelectE
    { expInfo :: ExpInfo
    , expClass :: PyonClass
    , expType :: RecType s     -- ^ Class instance type
    , expMethodIndex :: {-# UNPACK #-} !Int
    , expArg :: SFRecExp s       -- ^ Class dictionary
    }

instance Typeable1 (SFExpOf Rec) where
  typeOf1 x =
    let con1 = mkTyCon "Pyon.SystemF.Syntax.SFExpOf"
        arg1 = typeOf (undefined :: Rec)
    in mkTyConApp con1 [arg1]
          
instance HasSourcePos (SFExpOf Rec s) where
  getSourcePos _ = noSourcePos
  -- Not implemented!
  setSourcePos _ _ = internalError "HasSourcePos.setSourcePos"

data Fun s =
  Fun { funTyParams :: [TyPat s] -- ^ Type parameters
      , funParams :: [Pat s]     -- ^ Object parameters
      , funReturnType :: RecType s -- ^ Return type
      , funMonad :: !Gluon.Con -- ^ Which monad this function inhabits 
                              -- (Stream or Action)
      , funBody :: SFRecExp s
      }
  deriving(Typeable)

data Def s = Def Var (Fun s)
         deriving(Typeable)

data Module s = Module [Def s]
            deriving(Typeable)

-- | Return True only if the given expression has no side effects.
-- This function examines only expression constructors, and avoids inspecting
-- let or letrec expressions.
--
-- Constructors 'CallE', 'LetE', and 'LetrecE' are assumed to have side
-- effects.  Lambda expressions have no side effects, since they return but
-- do not execute their function.

isValueExp :: SFRecExp Rec -> Bool
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