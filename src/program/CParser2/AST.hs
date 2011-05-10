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

import Common.Identifier
import Common.SourcePos
import Common.Label
import Type.Var
import Type.Type(Level(..), HasLevel(..))
import Type.Environment(TypeFunction)

-- | Details about an externally defined variable.
--
--   The main piece of information is the external variable.
--   By attaching a 'VarDetails' to a parser variable, the parser is directed
--   to translate the parser variable to the given external variable. 
--   Otherwise a new external variable will be created.
--
--   If a type-level variable stands for a built-in type function, then the
--   type function value is also included here.  Type functions must be
--   type-level entities, and must not be data types.
data VarDetails =
  PredefinedVar !Var !(Maybe TypeFunction)

instance HasLevel VarDetails where
  getLevel (PredefinedVar v _) = getLevel v

instance Foldable Located where
  foldMap f x = f (unLoc x)
  foldr f z x = f (unLoc x) z

instance Traversable Located where
  traverse f (L p x) = fmap (L p) $ f x
  mapM f (L p x) = liftM (L p) $ f x

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

-- | The AST data structure representing a type
data Type ix =

    -- | A variable
    VarT
    { -- | The variable
      tVar :: Identifier ix
    }
    
    -- | An integer index
  | IntIndexT
    { tInt :: !Integer
    }

    -- | An application
  | AppT 
    { tOper :: LType ix
    , tArg :: LType ix
    }

    -- | A function type
  | FunT 
    { tParam :: LType ix        -- ^ Domain
    , tRng :: LType ix          -- ^ range
    }
  
    -- | A universally quantified type
  | AllT
    { tDomain :: Domain ix
    , tRng :: LType ix
    }

type LType ix = Located (Type ix)

-- | A variable binder, binding a type or a value depending on how it's used.
data Domain ix = Domain (Identifier ix) (LType ix)

-- | A data constructor declaration.
--   Corresponds to @Type.Environment.DataConType@.
data DataConDecl ix =
  DataConDecl
  { dconVar :: Identifier ix
    -- | Type parameters.
  , dconParams :: [Domain ix]
    -- | Existential types.
  , dconExTypes :: [Domain ix]
    -- | Fields
  , dconArgs :: [LType ix]
    -- | Type of the constructed value
  , dconRng :: LType ix
  }

type LDataConDecl ix = Located (DataConDecl ix)

-- | A top-level type declaration.  This declares a piece of global data
--   or a data type.
--
--   A global variable may have a type function definition.  Type function
--   definitions are built-in, so the parser doesn't modify them.
data Decl ix = Decl (Identifier ix) !(Entity ix)

data Entity ix = 
    VarEnt (LType ix) 
  | TypeEnt (LType ix) (Maybe TypeFunction)
  | DataEnt (LType ix) [LDataConDecl ix]

type LDecl ix = Located (Decl ix)

-- | A module.  Modules represent to an entire file.
data Module ix = Module [LDecl ix]

-------------------------------------------------------------------------------
-- * Parsed modules

-- | A type index for ASTs produced by the parser
data Parsed

type PType = Type Parsed
type PLType = LType Parsed
type PDomain = Domain Parsed
type PDecl = Decl Parsed
type PLDecl = LDecl Parsed
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
type RLDecl = LDecl Resolved
type RModule = Module Resolved

-- | Names are resolved to variables
type instance Identifier Resolved = ResolvedVar

data ResolvedVar = ResolvedVar !Var !(Maybe VarDetails)

instance HasLevel ResolvedVar where
  getLevel (ResolvedVar v _) = getLevel v

instance Eq ResolvedVar where
   ResolvedVar v1 _ == ResolvedVar v2 _ = v1 == v2

instance Ord ResolvedVar where
   ResolvedVar v1 _ `compare` ResolvedVar v2 _ = v1 `compare` v2
