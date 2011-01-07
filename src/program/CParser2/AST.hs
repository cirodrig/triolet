{-|
These AST data structures are used throughout the Core frontend.  A
single 'Module' contains all the data of a file being parsed by the 
frontend.
-}

{-# LANGUAGE TypeFamilies #-}
module CParser2.AST where

import Control.Monad
import Data.Foldable
import Data.Traversable

import Gluon.Common.Identifier
import Gluon.Common.SourcePos
import Gluon.Core.Level
import LowLevel.Label
import Type.Var

-- | Details about an externally defined variable
data VarDetails =
    PredefinedVar !Var

instance HasLevel VarDetails where
  getLevel (PredefinedVar v) = getLevel v

instance Foldable Located where
  foldMap f x = f (unLoc x)
  foldr f z x = f (unLoc x) z

instance Traversable Located where
--  traverse f (L p x) = fmap (L p) $ f x
  mapM f (L p x) = liftM (L p) $ f x

traverse f (L pos x) = do
  y <- f x
  return (L pos y)

-------------------------------------------------------------------------------
-- * Utility data types

-- | Identifiers for named things
type family Identifier ix :: *

-- | A thing with a source position
data Located a = L SourcePos a

instance Functor Located where fmap f (L p x) = L p (f x)

instance HasSourcePos (Located a) where
  getSourcePos (L p _) = p

-- | Remove the location information from a thing
unLoc :: Located a -> a
unLoc (L _ x) = x

-------------------------------------------------------------------------------
-- * Abstract Syntax Trees
-- $ast
-- Most stages of the frontend manipulate abstract syntax trees.  They are 
-- produced by the parser, and translated to Core data structures at the last
-- stage.  AST nodes are parameterized over a type index for customizing
-- data representations to specific stages of the frontend.

-- | A literal value
data Lit =
    IntL !Integer
  | FloatL !Double

-- | A data representation
data Repr = Value        -- ^ pass by value
          | Boxed        -- ^ pass a reference to a memory-managed object
          | Reference    -- ^ pass a reference to a memory area
            deriving(Eq)

-- | The AST data structure representing a type
data Type ix =

    -- | A variable
    VarT
    { -- | The variable
      tVar :: Identifier ix
    }

    -- | An application
  | AppT 
    { tOper :: LType ix
    , tArgs :: [LType ix]
    }

    -- | A function type
  | FunT 
    { fParam :: ParamType ix           -- ^ domain
    , fRng :: ReturnType ix            -- ^ range
    }

type LType ix = Located (Type ix)

-- | A parameter type, describing a function parameter's type, representation,
-- and other representation-dependent information.
data ParamType ix = ParamType (ParamRepr ix) (LType ix)

data ParamRepr ix =
    -- | A pass-by-value parameter
    ValuePT (Maybe (Identifier ix))
  | BoxedPT
  | ReadPT
  | WritePT

-- | A return type, describing a function return value's type and
--   representation.
data ReturnType ix = ReturnType ReturnRepr (LType ix)

data ReturnRepr = ValueRT | BoxedRT | ReadRT | WriteRT

-- | A top-level type declaration.  This declares a piece of global data 
data Decl ix = Decl (Identifier ix) (ReturnType ix)

type LDecl ix = Located (Decl ix)

-- | A module.  Modules represent to an entire file.
data Module ix = Module [LDecl ix]

-------------------------------------------------------------------------------
-- * Parsed modules

-- | A type index for ASTs produced by the parser
data Parsed

type PType = Type Parsed
type PLType = LType Parsed
type PDecl = Decl Parsed
type PModule = Module Parsed

-- | The parser translates names to strings
type instance Identifier Parsed = String

-------------------------------------------------------------------------------
-- * Resolved modules

-- | A type index for ASTs produced by name resolution
data Resolved

type RType = Type Resolved
type RLType = LType Resolved
type RDecl = Decl Resolved
type RModule = Module Resolved

-- | Names are resolved to variables
type instance Identifier Resolved = ResolvedVar

data ResolvedVar = ResolvedVar !(Ident Var) !(Maybe Label) !(Maybe VarDetails)

instance Eq ResolvedVar where
   ResolvedVar v1 _ _ == ResolvedVar v2 _ _ = v1 == v2

instance Ord ResolvedVar where
   ResolvedVar v1 _ _ `compare` ResolvedVar v2 _ _ = v1 `compare` v2

-------------------------------------------------------------------------------
-- * Level-inferred modules

data LevelInferred

type LvType = Type LevelInferred
type LvLType = LType LevelInferred
type LvDecl = Decl LevelInferred
type LvModule = Module LevelInferred

type instance Identifier LevelInferred = Var

