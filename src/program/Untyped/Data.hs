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

import Common.Identifier
import Common.Label
import Common.SourcePos
import SystemF.Syntax as SystemF
import Untyped.Kind
import {-# SOURCE #-} Untyped.Syntax as Untyped
import qualified Type.Type as SystemF
import qualified Type.Var as SystemF

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
    -- | A type family constraint.  This predicate declares that F(t1) = t2 
    --   for family F and types t1, t2.
  | IsFamily !TyFamily HMType HMType

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
    tcSystemFValue :: SystemF.TypSF

    -- | If the type constructor is a type function, this is a reference
    --   to the function.
  , tcTypeFunction :: !(Maybe TyFamily)
  }

-- | An atomic type-level entity, such as a type variable or constructor
data TyCon =
  TyCon
  { -- | Unique ID, used for comparing TyCon instances
    tcID :: {-# UNPACK #-} !(Ident TyCon)
  , tcName :: !(Maybe Label)
  , tcKind :: !Kind
    -- | For a flexible type variable, this is what the variable has been 
    -- unified with
  , tcRep  :: !(Maybe (IORef TyVarRep))
    -- | The System F equivalent of a type variable
  , tcSystemFVariable :: IORef (Maybe SystemF.Var)
    -- | For type constructors, information about the type constructor; 
    --   for variables, Nothing.
  , tcConInfo :: !(Maybe TyConDescr)
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
    -- | A type constructor or variable.
    --   Type functions never appear in a 'ConTy' term.
    ConTy !TyCon
    -- | An N-ary function type
  | FunTy {-# UNPACK #-} !Int
    -- | An N-element tuple type
  | TupleTy {-# UNPACK #-} !Int
    -- | A type application
  | AppTy HMType HMType
    -- | A type function application.  Type functions are always fully applied.
  | TFunAppTy !TyCon [HMType]
    -- | A distinct type with the specified kind.  This is used for data
    --   types that have no constraints on them.
  | AnyTy !Kind
    deriving(Typeable)

-- | A type scheme
data TyScheme = TyScheme TyVars Constraint HMType

-- | A type class or type family signature.  This is the part that directs
--   constraint resolution.
data ClassSig =
  ClassSig
  { clsParam :: TyCon
  , clsConstraint :: Constraint
  , clsName :: String
  , clsTypeCon :: !SystemF.Var    -- ^ Dictionary or family type constructor
  }

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
  { clsSignature :: !ClassSig
  , clsDictCon :: SystemF.Var     -- ^ Class dictionary constructor
  , clsMethods :: [ClassMethod]
  , clsInstances :: [Instance]
  }

mkClass :: String -> TyCon -> Constraint -> SystemF.Var -> SystemF.Var
        -> [ClassMethod] -> [Instance] -> Class
mkClass name tc cst cls_con inst_con methods instances =
  Class (ClassSig tc cst name cls_con) inst_con methods instances 

mkTyFamily :: String -> TyCon -> Constraint -> SystemF.Var
           -> [TyFamilyInstance]
           -> TyFamily
mkTyFamily name tc cst fun_con instances =
  TyFamily (ClassSig tc cst name fun_con) instances

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

data TyFamily =
  TyFamily
  { tfSignature :: !ClassSig
  , tfInstances :: [TyFamilyInstance]
  }

data InstanceSig =
  InstanceSig
  { -- | Type parameters of the instance, in addition to class type parameters 
    insQVars :: TyVars
    -- | Constraints of the instance, in addition to class constraints
  , insConstraint :: Constraint
    -- | The class that the instance is associated with
  , insClass :: ClassSig
    -- | The instance type
  , insType :: HMType
  }

-- | A class instance
data Instance =
  Instance
  { insSignature :: !InstanceSig
    -- | If given, this global constructor is the instance's predefined value.
    -- The constructor is parameterized over the qvars and constraint.
  , insCon :: !(Maybe SystemF.Var)
  , insMethods :: [InstanceMethod]
  }

-- | Each instance method is defined as some constructor in System F
newtype InstanceMethod = InstanceMethod {inmName :: SystemF.Var}

mkInstance :: TyVars -> Constraint -> ClassSig -> HMType -> Maybe SystemF.Var
           -> [InstanceMethod]
           -> Instance
mkInstance qvars cst cls ty con methods =
  Instance (InstanceSig qvars cst cls ty) con methods
  
-- | A type family instance
data TyFamilyInstance =
  TyFamilyInstance
  { tinsSignature :: !InstanceSig
  , tinsType :: HMType
  }

mkTyFamilyInstance :: TyVars -> Constraint -> ClassSig -> HMType -> HMType
                   -> TyFamilyInstance
mkTyFamilyInstance qvars cst cls ty result =
  TyFamilyInstance (InstanceSig qvars cst cls ty) result

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
    -- | A derivation of a type family constraint
  | TyFamilyDerivation
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

-- | Type inferred expressions, which may contain placeholders
data instance SystemF.Exp TI =
    -- | A placeholder for a recursive variable
    RecVarPH
    { phExpInfo :: SystemF.ExpInfo
    , phExpVariable :: Untyped.Variable
    , phExpTyVar :: TyCon
    , phExpResolution :: {-# UNPACK #-} !(MVar TIExp)
    }
    -- | A placeholder for a class dictionary
  | DictPH
    { phExpInfo :: SystemF.ExpInfo
    , phExpPredicate :: Predicate
    , phExpResolution :: {-# UNPACK #-} !(MVar TIExp)
    }
    -- | A non-placeholder expression
  | TIExp !TIExp'
    
    -- | An expression that was written directly in System F
    --
    -- This kind of expression only comes from built-in terms.
  | TIRecExp SystemF.ExpSF

data instance SystemF.Pat TI =
    TIWildP TIType
  | TIVarP SystemF.Var TIType
  | TITupleP [SystemF.Pat TI]

data instance SystemF.TyPat TI = TITyPat SystemF.Var TIType

newtype instance SystemF.Alt TI = TIAlt (SystemF.BaseAlt TI)
newtype instance SystemF.Fun TI = TIFun (SystemF.BaseFun TI)

-- | A type inference System F expression
type TIExp = SystemF.Exp TI

-- | Other expressions use regular System F constructors
type TIExp' = SystemF.BaseExp TI

-- | A Placeholder is a RecVarPH or DictPH term
type Placeholder = TIExp
type Placeholders = [Placeholder]

-- | Types are not evaluated until type inference completes
newtype instance SystemF.Typ TI = DelayedType (IO SystemF.TypSF)

type TIType = SystemF.Typ TI
