
{-# LANGUAGE FlexibleContexts #-}
module Untyped.Type
       (-- * Type constructors
        TyCon,
        TyConClass(..),
        TyConSet,
        tyConID,
        tyConName,
        showTyCon,
        tyConKind,
        tyConClass,
        tyConSFVar,
        tyConArity,
        isTyVar, isTyCon, isTyCls, isTyFun,

        -- * Monotypes
        TyVar,
        TyVarSet,
        HMType(..),
        (@@),
        kindRange,
        typeKind,
        functionTy, appTy, appTys, appTyCon, tupleTy,
        isInjConstructor,
        equalInjConstructors,
        newTyConID, newTyCon, newTyVar,

        -- * Qualified types
        Qualified(..),
        FOConstructor(..),
        TyScheme,
        Predicate(..),
        Constraint,
        Proof, Proofs,
        asProof, asProofs,
        fromProof, fromProofs,

        -- * Data types
        DataType(..),
        DataCon(..),

        -- * Classes and families
        Instance(..),
        Instances,
        Class(..),
        ClassMethod(..),
        ClassInstance(..),
        TyFamily(..),
        TyFamilyInstance(..)
       )
where

import Control.Monad
import Control.Monad.Trans
import Data.IORef
import Data.Function
import qualified Data.Set as Set
import Data.Typeable(Typeable)
import System.IO.Unsafe

import Common.Error
import Common.Identifier
import Common.Label
import Common.Supply
import qualified SystemF.Syntax as SF
import qualified Type.Type as SF
import {-# SOURCE #-} Untyped.Syntax
import Untyped.Unif
import Untyped.Kind

-- | Report a kind error.  Give very rough information about where the
--   error occurred.
kindError loc =
  error $ "Kind error in " ++ loc

tyConIDSupply :: Supply (Ident TyCon)
{-# NOINLINE tyConIDSupply #-}
tyConIDSupply = unsafePerformIO newIdentSupply

newTyConID :: IO (Ident TyCon)
newTyConID = supplyValue tyConIDSupply

-- | Create a new type constructor representing an existing variable
newTyCon :: SF.Var -> Kind -> TyConClass -> Int -> IO TyCon
newTyCon sf_var kind cls tyfun_arity = do
  when (cls /= TCCFun && tyfun_arity /= 0) $
    internalError "newTyCon: Invalid arity"
  id <- newTyConID
  return $ TyCon id (SF.varName sf_var) kind cls tyfun_arity sf_var

-- | Create a new non-unifiable type variable.  A new System F variable is
--   created as well.
newTyVar :: (MonadIO m, Supplies m (Ident SF.Var)) =>
            Maybe Label -> Kind -> m TyCon
newTyVar name kind = do
  sf_v <- SF.newVar name SF.TypeLevel
  liftIO $ newTyCon sf_v kind TCCVar 0

-------------------------------------------------------------------------------
-- Types

-- | A unifiable type variable
type TyVar = UVar HMType

type TyVarSet = Set.Set TyVar

-- | A non-unifiable type-level variable or constructor
data TyCon =
  TyCon
  { -- | Unique ID, used for comparing TyCon instances
    tcID :: {-# UNPACK #-} !(Ident TyCon)
  , tcName :: !(Maybe Label)
  , tcKind :: !Kind
  , tcClass :: !TyConClass
    -- | The arity of this type constructor, if it is a type function.
    --   Zero if not a type function.
  , tcTyFunArity :: {-# UNPACK #-}!Int
    -- | The System F variable corresponding to this type constructor.
    --   It is a type variable, data type constructor, class dictionary type 
    --   constructor, or type function.
  , tcSFVar :: SF.Var
  }
  deriving(Typeable)

-- | What kind of thing a type constructor stands for
data TyConClass =
    TCCVar                      -- ^ A type variable
  | TCCCon                      -- ^ A data type constructor
  | TCCCls                      -- ^ A class
  | TCCFun                      -- ^ A type function
    deriving(Eq)

type TyConSet = Set.Set TyCon

instance Eq TyCon where
  (==) = (==) `on` tcID
  (/=) = (/=) `on` tcID

instance Ord TyCon where
  compare = compare `on` tcID

tyConID :: TyCon -> Ident TyCon
tyConID = tcID

tyConName :: TyCon -> Maybe Label
tyConName = tcName

-- | Turn a 'TyCon' into a short, human-readable string
showTyCon :: TyCon -> String
showTyCon c =
  case tyConName c
  of Nothing    -> ty_con_name (tcID c)
     Just label -> showLabel label
  where
    ty_con_name ident = "con" ++ show (fromIdent ident)

tyConKind :: TyCon -> Kind
tyConKind = tcKind

tyConClass :: TyCon -> TyConClass
tyConClass = tcClass

tyConSFVar :: TyCon -> SF.Var
tyConSFVar = tcSFVar

tyConArity :: TyCon -> Int
tyConArity tc
  | tcClass tc /= TCCFun = internalError "tyConArity: Not a type function"
  | otherwise            = tcTyFunArity tc

isTyVar, isTyCon, isTyCls, isTyFun :: TyCon -> Bool
isTyVar tc = case tcClass tc of {TCCVar {} -> True; _ -> False}
isTyCon tc = case tcClass tc of {TCCCon {} -> True; _ -> False}
isTyCls tc = case tcClass tc of {TCCCls {} -> True; _ -> False}
isTyFun tc = case tcClass tc of {TCCFun {} -> True; _ -> False}

data HMType =
    -- | A unifiable type variable
    VarTy TyVar
    -- | A type constructor or variable.
    --   Type functions never appear in a 'ConTy' term.
  | ConTy !TyCon
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

infixl 4 @@
(@@) = AppTy

-- | Get an arrow kind's range.  Error if not an arrow kind.
kindRange :: Kind -> Kind
kindRange (_ :-> k) = k
kindRange _ = kindError "type application"

typeKind :: HMType -> Kind
typeKind (VarTy v)        = uVarKind v
typeKind (ConTy c)        = tyConKind c
typeKind (FunTy n)        = nAryKind (n+1)
typeKind (TupleTy n)      = nAryKind n
typeKind (AppTy t1 t2)    = kindRange $ typeKind t1
typeKind (TFunAppTy f ts) = foldl (\k _ -> kindRange k) (tyConKind f) ts
typeKind (AnyTy k)        = k

-- | Create a type application.  Should not call this to apply a type function.
appTy :: HMType -> HMType -> HMType
s `appTy` t =
  case typeKind s
  of k :-> _ | typeKind t == k -> s `AppTy` t
     _ -> kindError "type application"

appTys :: HMType -> [HMType] -> HMType
appTys t ts = foldl appTy t ts

-- | Apply a 'TyCon' to type arguments.  Create either an ordinary
--   application term or a type function application term.
appTyCon :: TyCon -> [HMType] -> HMType
appTyCon con ts
  | tyConClass con == TCCFun =
      let arity = tyConArity con
      in if length ts < arity
         then internalError "appTyCon: Not enough arguments"
         else let tyfun_params = take arity ts
                  surplus_params = drop arity ts
              in appTys (TFunAppTy con tyfun_params) surplus_params
  | otherwise =
        appTys (ConTy con) ts

functionTy :: [HMType] -> HMType -> HMType
functionTy dom rng
  | any ((Star /=) . typeKind) dom = kindError "function parameter type"
  | Star /= typeKind rng = kindError "function return type"
  | otherwise = appTys (FunTy $ length dom) (dom ++ [rng])

tupleTy :: [HMType] -> HMType
tupleTy ts = appTys (TupleTy (length ts)) ts

-- | Return 'True' if the argument is an injective constructor and
--   not an application.  The argument should be normalized.
isInjConstructor :: HMType -> Bool
isInjConstructor ty = 
  case ty
  of VarTy _             -> False
     ConTy c | isTyCon c -> True
             | isTyCls c -> True
             | isTyVar c -> False
             | isTyFun c -> False
     FunTy _             -> True
     TupleTy _           -> True
     AnyTy _             -> True
     _ -> internalError "isInjConstructor"

-- | Return 'True' if both arguments are equal injective constructors.
--   The arguments should be normalized.
--   Only injective constructors return 'True'.  Type variables, functions,
--   and applications always return 'False'.

equalInjConstructors (ConTy c1) (ConTy c2) =
  (isTyCon c1 || isTyCls c1) &&
  (isTyCon c2 || isTyCls c2) &&
  c1 == c2

equalInjConstructors (TupleTy n1) (TupleTy n2) = n1 == n2
equalInjConstructors (FunTy n1) (FunTy n2) = n1 == n2
equalInjConstructors (AnyTy k1) (AnyTy k2) = True
equalInjConstructors _ _ = False


-------------------------------------------------------------------------------
-- Qualified types and constraints

-- | A qualified entity.  Represents @forall as. C => x@, for some
--   universal type parameters @as@, constraint @C@, and entity @x@.
data Qualified a =
  Qualified
  { qParams :: [TyCon] 
  , qConstraint :: Constraint 
  , qRange :: a
  }

instance Functor Qualified where fmap f q = q {qRange = f $ qRange q}

instance Monad Qualified where
  return x = Qualified [] [] x
  Qualified p1 c1 r1 >>= k =
    let Qualified p2 c2 r2 = k r1
    in Qualified (p1 ++ p2) (c1 ++ c2) r2

-- | A first-order parametric constructor that doesn't mention type parameters
newtype FOConstructor a = FOConstructor a

-- | A type scheme
type TyScheme = Qualified HMType

-- | A predicate in the type inference engine's constraint system
data Predicate =
    -- | Class membership.  This predicate translates to a class dictionary.
    --   the type constructor must be a class.
    IsInst TyCon HMType
    -- | A type equality constraint.  This predicate declares that the two
    --   given types are equal.
  | IsEqual HMType HMType

type Constraint = [Predicate]

-- | A proof of predicate @p@ consists of @p@ and its derivation
type Proof d = (Predicate, d)
type Proofs d = [Proof d]

-- | Pair a predicate with a dummy proof
asProof :: Predicate -> Proof ()
asProof p = (p, ())

asProofs :: Constraint -> Proofs ()
asProofs = map asProof

fromProof :: Proof d -> Predicate
fromProof = fst

fromProofs :: Proofs d -> Constraint
fromProofs = map fromProof

{-
-- | A derivation of a predicate, containing enough information to reconstruct
-- the derivation steps in the form of a proof object
data Derivation =
    -- | Nothing was derived
    Hypothesis
    { conclusion :: Predicate
    }
    -- | A derivation using a class instance
  | InstanceDerivation 
    { conclusion :: Predicate 
    , derivedInstance :: Instance ClassInstance
    , instancePremises :: [Derivation] 
    , classPremises :: [Derivation]
    }
  | -- | Parameter-passing convention derivation for functions
    FunPassConvDerivation
    { conclusion :: Predicate
    }
    -- | A derivation of an equality constraint
  | EqualityDerivation
    { conclusion :: Predicate
    }
    -- | A derivation whose result is coerced to another type
  | CoerceDerivation
    { conclusion :: Predicate
    , contentPremise :: Derivation
    }
    -- | A derivation without evidence
  | MagicDerivation
    { conclusion :: Predicate
    }

type Derivations = [Derivation]

isHypothesis :: Derivation -> Bool
isHypothesis (Hypothesis {}) = True
isHypothesis _ = False
-}

-------------------------------------------------------------------------------
-- Data type data structures

-- | An algebraic data type.
data DataType =
  DataType
  { dtBoxed :: !Bool            -- ^ Whether constructed objects of this type
                                -- are boxed
  }

-- | An algebraic data type constructor.
data DataCon =
  DataCon
  { -- | A type signature giving the type parameters, field types, and
    --   data type constructor of this data constructor.
    --   The 'TyCon' must be a data type constructor.
    --   The constraint must be empty.
    dcSignature :: Qualified ([HMType], FOConstructor TyCon)
  }

-------------------------------------------------------------------------------
-- Type class data structures

-- | A type class.
--
-- The type class's name is used as a globally unique identifier.
--
-- The class's method and instance lists must be non-strict.  Methods and 
-- instances contain references back to the parent class.
--
-- If the class is abstract, type inference cannot generate code for accessing 
-- its fields.  An abstract class can't have superclasses, since they would
-- be impossible to access.
data Class =
  Class
  { clsTyCon      :: SF.Var      -- ^ Dictionary type constructor
  , clsSFDictCon  :: SF.Var      -- ^ Dictionary data constructor
  , clsIsAbstract :: !Bool       -- ^ True if class is abstract
  , clsSignature  :: Qualified [ClassMethod] -- ^ Type signature of contents
  , clsInstances  :: Instances ClassInstance -- ^ Instances
  }

instance Eq Class where (==) = (==) `on` clsTyCon

-- | A class method type signature.
data ClassMethod =
  ClassMethod
  { -- | The method's type scheme.
    -- The class's parameter variables and the class constraint itself are not
    -- part of the type scheme.
    clmSignature :: TyScheme
  --  -- | The variable that represents this method in source code 
  -- , clmVariable :: Variable
  }

data Instance a =
  Instance
  { instHead :: HMType
  , instBody :: a
  }
type Instances a = [Qualified (Instance a)]

-- | A type class instance.
--
--   Instances may be polymorphic.  A class dictionary is constructed by
--   applying the contents of an instance to some type and dictionary
--   arguments.
data ClassInstance =
    -- | A class instance constructed by a function, or a global
    --   constant.  The instance may optionally take extra type
    --   parameters, given by the list of types.
    --
    -- > f t1 a b x y
    AbstractClassInstance SF.Var [HMType]

  | NewAbstractClassInstance ([SF.Type] -> [SF.ExpSF] -> SF.ExpSF)

    -- | A class instance that is a data structure
    --
    -- > ClsDict t (f1 a b x y) (f2 a b x y)
  | MethodsInstance [SF.Var]

data TyFamily =
  TyFamily
  { tfTyCon     :: SF.Var         -- ^ Type family type constructor
  , tfArity     :: !Int           -- ^ Number of type parameters
  , tfKind      :: Kind           -- ^ Type family's kind
  , tfInstances :: Instances TyFamilyInstance
  }

instance Eq TyFamily where (==) = (==) `on` tfTyCon

-- | A type family instance.
--
--   Instances may be polymorphic.  The type is constructed by substituting
--   types into the instance's type.
newtype TyFamilyInstance = TyFamilyInstance HMType

