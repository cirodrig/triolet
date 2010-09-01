-- | This module declares some shared data structures.  Implementation details
-- for these data structures are found in their respective modules.

{-# LANGUAGE EmptyDataDecls, TypeFamilies, DeriveDataTypeable #-}
{-# OPTIONS_HADDOCK hide #-}
module Untyped.Data where

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
import SystemF.Syntax as SystemF
import Untyped.Kind
import {-# SOURCE #-} Untyped.Syntax as Untyped

-- | The value bound to a variable in the parser.
--
-- Variables in source code may represent a kind, type, or object-level term. 
--
-- Kinds and types cannot be defined in source code, but some are predefined.
-- Type variables can be defined in source code.
data ParserVarBinding =
    KindBinding !Kind
  | TypeBinding !TyCon
  | ObjectBinding !Untyped.Variable

-- | A substitution on type-level terms
data Substitution =
  Substitution
  { _substTc :: Map.Map TyCon HMType
  }

-- | A pretty-printing applicative construct for giving names to
-- anonymous variables
newtype Ppr a = Ppr {doPpr :: PprContext -> IO a}

data PprContext =
  PprContext
  { freshNames :: {-# UNPACK #-} !(IORef [String])
  , typeNames :: {-# UNPACK #-} !(IORef (Map.Map (Ident TyCon) Doc))
  }

-- | A predicate to be solved by type inference
data Predicate =
    -- | Class membership.  This predicate translates to a class dictionary.
    IsInst HMType !Class

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

-- | A type scheme
data TyScheme = TyScheme TyVars Constraint HMType

-- | A type class.
--
-- The type class's name is used as a globally unique identifier.
--
-- The class's method and instance lists must be non-strict.  Methods and 
-- instances contain references back to the parent class.
--
-- As a special case, the \'Passable\' class has no dictionary constructor.
-- Members of this class are only deconstructed in the backend.
data Class =
  Class
  { clsParam :: TyCon
  , clsConstraint :: Constraint
  , clsMethods :: [ClassMethod]
  , clsName :: String
  , clsInstances :: [Instance]
  , clsTypeCon :: !Gluon.Con    -- ^ Class dictionary type constructor
  , clsDictCon :: Gluon.Con     -- ^ Class dictionary constructor
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
    -- | If given, this global constructor is the instance's predefined value.
    -- The constructor is parameterized over the qvars and constraint.
  , insCon :: !(Maybe Gluon.Con)
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
  | -- | Parameter-passing convention derivation for functions
    FunPassConvDerivation
    { conclusion :: Predicate
    }
    -- | A derivation without evidence
  | MagicDerivation
    { conclusion :: Predicate
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

newtype instance SystemF.AltOf TI TI = TIAlt (SystemF.AltOf Rec TI)
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
