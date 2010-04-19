-- | This module declares some shared data structures.  Implementation details
-- for these data structures are found in their respective modules.

{-# LANGUAGE EmptyDataDecls, TypeFamilies, DeriveDataTypeable #-}
{-# OPTIONS_HADDOCK hide #-}
module Pyon.Untyped.Data where

import Control.Concurrent.MVar
import Data.Function
import Data.IORef
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Typeable(Typeable)
import Text.PrettyPrint.HughesPJ

import Gluon.Common.Identifier
import Gluon.Common.Label
import Gluon.Common.SourcePos
import Gluon.Core(Structure)
import qualified Gluon.Core as Gluon
import Pyon.SystemF.Syntax as SystemF
import Pyon.Untyped.Kind
import {-# SOURCE #-} Pyon.Untyped.Syntax as Untyped

-- | A substitution on type-level terms
data Substitution =
  Substitution
  { _substTc :: Map.Map TyCon HMType
  , _substCc :: Map.Map PassConvVar PassConv
  }

-- | A pretty-printing applicative construct for giving names to
-- anonymous variables
newtype Ppr a = Ppr {doPpr :: PprContext -> IO a}

data PprContext =
  PprContext
  { freshNames :: {-# UNPACK #-} !(IORef [String])
  , typeNames :: {-# UNPACK #-} !(IORef (Map.Map (Ident TyCon) Doc))
  , passNames :: {-# UNPACK #-} !(IORef (Map.Map (Ident PassConvVar) Doc))
  }

 -- | A predicate to be solved by type inference
data Predicate =
    -- | Class membership.  This predicate translates to a class dictionary.
    IsInst HMType !Class
    -- | Parameter-passing constraint.  This predicate translates to
    -- parameter-passing information, such as how to load, store, or
    -- duplicate a value.
  | HasPassConv HMType PassConv
    -- | Equality constraint on parameter-passing conventions
  | EqPassConv PassConv PassConv
    -- | Equality constraint on execution modes
  | EqExecMode ExecMode ExecMode

type Constraint = [Predicate]

class Unifiable a where
  -- | Show some unifiable objects.  Temporary names may be assigned to 
  -- anonymous variables; the same names are used across all objects.  
  -- This is used when constructing messages for unification failure.
  uShow :: a -> Ppr Doc

  -- | Rename a unifiable object
  rename :: Substitution -> a -> IO a
  
  -- | Unify terms.  Unification may produce extra constraints, which should
  -- be added to any constraints already in the context.  Flexible type 
  -- variables may be modified during unification.  If the arguments cannot 
  -- be unified, an exception is thrown.
  unify :: SourcePos -> a -> a -> IO Constraint
  
  -- | Match (semi-unify) two terms. 
  --
  -- @match x y@ finds a substitution that unifies @x@ with @y@, if one exists.
  -- If no substitution can be found, return None.  The terms are not modified.
  match :: a -> a -> IO (Maybe Substitution)

  -- | Decide whether two unifiable terms are equal.
  -- The terms are not modified.
  uEqual :: a -> a -> IO Bool

-- | An entity that may contain type variables
class Type a where
  -- | Get the set of free type variables mentioned in the value
  freeTypeVariables :: a -> IO TyVarSet

-- | A list of type variables
type TyVars = [TyCon]

-- | A set of type variables
type TyVarSet = Set.Set TyCon

-- | Information about a type constructor
data TyConDescr =
  TyConDescr
  { -- | The System F constructor
    tcSystemFValue :: SystemF.RType
    -- | Parameter-passing convention for values of this type constructor
  , tcPassConv :: PassConvCtor
    -- | A proof or proof constructor for the parameter-passing convention.
    -- The proof constructor's type must match the constructor's kind.
  , tcPassConvProof :: Gluon.Con
    -- | Which arguments need to be passed to the proof constructor.  There
    -- is one list element per type parameter.
  , tcPassConvArgs :: [Bool]
    -- | Execution mode for functions returning this type constructor
  , tcExecMode :: ExecMode
  }

-- | An atomic type-level entity, such as a type variable or constructor
data TyCon =
  TyCon
  { -- | Unique ID, used for comparing TyCon instances
    tcID :: {-# UNPACK #-} !(Ident TyCon)
  , tcName :: !(Maybe Label)
  , tcKind :: !Kind
    -- | True if this is a type variable
  , tcIsVariable :: {-# UNPACK #-} !Bool
    -- | For a flexible type variable, this is what the variable has been 
    -- unified with
  , tcRep  :: {-# UNPACK #-} !(Maybe (IORef TyVarRep))
    -- | The System F equivalent of a type variable
  , tcSystemFVariable :: IORef (Maybe SystemF.Var)
    -- | Information pertaining to type constructors; undefined for variables
  , tcConInfo :: TyConDescr
  }
  deriving(Typeable)

instance Eq TyCon where
  (==) = (==) `on` tcID
  (/=) = (/=) `on` tcID

instance Ord TyCon where
  compare = compare `on` tcID

-- | A type variable's value as identified by unification
--
-- 'TyVarRep' always holds a reference to a unifiable type variable
data TyVarRep = NoRep | TyVarRep !TyCon | TypeRep !HMType

-- | A first-order Hindley-Milner type
data HMType =
    -- | A type constructor or variable
    ConTy !TyCon
    -- | An N-ary function type
  | FunTy {-# UNPACK #-} !Int
    -- | An N-element tuple type
  | TupleTy {-# UNPACK #-} !Int
    -- | A type application
  | AppTy HMType HMType
    deriving(Typeable)

-- | A parameter-passing convention variable.
-- These variables represent unknowns that are resolved through unification. 
-- Unlike type variables, they are monomorphic.
data PassConvVar =
  PassConvVar
  { pcID :: {-# UNPACK #-} !(Ident PassConvVar)
  , pcRep :: {-# UNPACK #-} !(IORef PassConvVarRep)
  }

instance Eq PassConvVar where
  (==) = (==) `on` pcID
  (/=) = (/=) `on` pcID

instance Ord PassConvVar where
  compare = compare `on` pcID

-- | The parameter-passing convention for a @PassConvVar@ as identified by
-- unification
data PassConvVarRep = NoPCRep | PCVarRep !PassConvVar | PCRep !PassConv

-- | A parameter-passing convention.
-- The actual conventions are 'ByVal', 'ByRef', and 'ByClosure'.
-- The convention 'TuplePassConv' represents a function that evaluates to
-- one of the above.
-- The constructor 'By' represents a variable.
data PassConv =
    ByVal                       -- ^ Pass by value
  | ByRef                       -- ^ Pass by reference
  | ByClosure CallConv          -- ^ Pass an un-evaluated function
  | TuplePassConv [PassConv]    -- ^ Parameter-passing convention for a tuple:
                                -- by value if all list members are by value, 
                                -- by refernce otherwise
  | TypePassConv HMType         -- ^ The parameter-passing convention of a
                                -- (possibly unknown) type 
  | By {-# UNPACK #-} !PassConvVar -- ^ Unknown parameter-passing convention

-- | A function execution mode.
-- Functions execute as 'Action' or 'Stream' functions, based on their
-- return type.  If the return type is not known, then 'PickExecMode' is
-- used to delay the decision.
data ExecMode =
  AsAction | AsStream | PickExecMode HMType

-- | A function calling convention.
data CallConv =
    -- | Require another parameter
    PassConv :+> CallConv
    -- | Execute and return a value
  | Return !ExecMode PassConv

infixr 4 :+>

-- | Constructors for parameter-passing conventions
data PassConvCtor =
  PassConvFun (HMType -> PassConvCtor) | PassConvVal PassConv

-- | A type scheme
data TyScheme = TyScheme TyVars Constraint HMType

-- | A type class.
--
-- The type class's name is used as a globally unique identifier.
--
-- The class's method and instance lists must be non-strict.  Methods and 
-- instances contain references back to the parent class.
data Class =
  Class
  { clsParam :: TyCon
  , clsConstraint :: Constraint
  , clsMethods :: [ClassMethod]
  , clsName :: String
  , clsInstances :: [Instance]
  , clsTypeCon :: !Gluon.Con    -- ^ Class dictionary type constructor
  , clsDictCon :: !Gluon.Con    -- ^ Class dictionary constructor
  }

-- | A class method interface declaration.  Information used for class
-- type and constraint inference is here.  The method's implementation is in
-- the instance method.
data ClassMethod =
  ClassMethod
  { clmName :: String
    -- | The type signature of a method retrieved from the class dictionary.  
    -- The class's parameter variables and the class constraint itself are not
    -- part of the signature.
  , clmSignature :: TyScheme
    -- | The variable that represents this method in source code 
  , clmVariable :: Untyped.Variable
  }

-- | A class instance
data Instance =
  Instance
  { insQVars :: TyVars
  , insConstraint :: Constraint
  , insClass :: Class
  , insType :: HMType
  , insMethods :: [InstanceMethod]
  }

-- | Each instance method is defined as some constructor in System F
newtype InstanceMethod = InstanceMethod {inmName :: Gluon.Con}

-- | A derivation of a predicate, containing enough information to reconstruct
-- the derivation steps in the form of a proof object
data Derivation =
    -- | A trivial derivation using an already-existing proof 
    IdDerivation 
    { conclusion :: Predicate
    }
    -- | A derivation using a class instance
  | InstanceDerivation 
    { conclusion :: Predicate 
    , derivedInstance :: Instance
    , instancePremises :: [Derivation] 
    , classPremises :: [Derivation]
    }
  | -- | Parameter-passing convention derivation for data
    PassConvDerivation
    { conclusion :: Predicate
    , derivedConstructor :: Gluon.Con
    , passConvTypes :: [HMType]
    , passConvPremises :: [Derivation]
    }
  | -- | Parameter-passing convention derivation for functions
    FunPassConvDerivation
    { conclusion :: Predicate
    }
    -- | A derivation without evidence
  | MagicDerivation
    { conclusion :: Predicate
    }

-- | A derivation of calling convention equality.  Unlike 'Derivation' values,
-- there is no predicate corresponding to the result of these derivations. 
-- These derivations are intermediate steps in other derivations.
--
-- The actual derivation is not implemented; this is a \"magic\" derivation.
data EqCallConvDerivation =
  EqCallConvDerivation
  { callConvConclusion :: (CallConv, CallConv)
  }

-- | A variable's type assignment, containing information about how to create 
-- its corresponding expression in System F
data TypeAssignment =
  TypeAssignment
  { -- | Get a type assignment's free type variables
    _typeAssignmentFreeVariables :: !(IO TyVarSet)
    -- | Get a type assignment's scheme, if it can be ascribed one
    -- This will evaluate to an error for recursive variable type assignments
  , _typeAssignmentScheme :: TyScheme
    -- | Instantiate a type assignment
  , _instantiateTypeAssignment :: !(SourcePos -> IO (Placeholders, TyVarSet, Constraint, HMType, TIExp))
  }

-- | Internal type inference representation of System F
data TI deriving(Typeable)
instance Structure TI

-- | Type inferred expressions, which may contain placeholders
data instance SystemF.SFExpOf TI TI =
    -- | A placeholder for a recursive variable
    RecVarPH
    { phExpInfo :: Gluon.SynInfo
    , phExpVariable :: Untyped.Variable
    , phExpTyVar :: TyCon
    , phExpResolution :: {-# UNPACK #-} !(MVar TIExp)
    }
    -- | A placeholder for a class dictionary
  | DictPH
    { phExpInfo :: Gluon.SynInfo
    , phExpPredicate :: Predicate
    , phExpResolution :: {-# UNPACK #-} !(MVar TIExp)
    }
    -- | A non-placeholder expression
  | TIExp !TIExp'
    
    -- | An expression that was written directly in System F
    --
    -- This kind of expression only comes from built-in terms.
  | TIRecExp SystemF.RExp

newtype instance SystemF.FunOf TI TI = TIFun (SystemF.FunOf Rec TI)

-- | A type inference System F expression
type TIExp = SystemF.SFExpOf TI TI

-- | Other expressions use regular System F constructors
type TIExp' = SystemF.SFExpOf Rec TI

-- | A Placeholder is a RecVarPH or DictPH term
type Placeholder = TIExp
type Placeholders = [Placeholder]

-- | Types are not evaluated until type inference completes
newtype instance Gluon.ExpOf TI TI = DelayedType (IO Gluon.RExp)

type TIType = SystemF.TypeOf TI TI


