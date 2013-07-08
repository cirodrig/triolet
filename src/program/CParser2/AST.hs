{-|
These AST data structures are used throughout the Core frontend.  A
single 'Module' contains all the data of a file being parsed by the 
frontend.
-}

{-# LANGUAGE FlexibleInstances, StandaloneDeriving, FlexibleContexts,
             UndecidableInstances #-}
module CParser2.AST where

import Control.Monad
import Data.Foldable
import Data.Traversable

import Common.Error
import Common.Identifier
import Common.SourcePos
import Common.Label
import Type.Var
import Type.Type(Level(..), HasLevel(..))
import Type.Environment(BuiltinTypeFunction)

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

-- | Attribute annotations from the source code
data Attribute ix =
    AbstractAttr                    -- ^ Data type is abstract
  | NonalgebraicAttr                -- ^ Data type is not algebraic
  | SingletonAttr                   -- ^ Data type is a singleton type constructor
  | ConlikeAttr                     -- ^ Function calls are cheap to reevaluate
  | InlineAttr                      -- ^ Definition should be aggressively
                                    --   inlined
  | InlineNeverAttr                 -- ^ Definition should never be inlined
  | InlineSequentialAttr            -- ^ Definition should not be inlined until
                                    --   the sequential compilation phase
  | InlineFinalAttr                 -- ^ Definition should not be inlined until
                                    --   the final optimization phase
  | InlinePostfinalAttr             -- ^ Definition should not be inlined until
                                    --   after redundant copying is removed
  | BuiltinAttr                     -- ^ Definition of a built-in variable.
                                    --   This attribute controls name
                                    --   resolution.
                                    --   Instead of creating a new variable,
                                    --   the definition will refer to the
                                    --   built-in variable.

castAttribute :: Attribute a -> Attribute b
castAttribute AbstractAttr = AbstractAttr
castAttribute NonalgebraicAttr = NonalgebraicAttr
castAttribute SingletonAttr = SingletonAttr
castAttribute ConlikeAttr = ConlikeAttr
castAttribute InlineAttr = InlineAttr
castAttribute InlineNeverAttr = InlineNeverAttr
castAttribute InlineSequentialAttr = InlineSequentialAttr
castAttribute InlineFinalAttr = InlineFinalAttr
castAttribute InlinePostfinalAttr = InlinePostfinalAttr
castAttribute BuiltinAttr = BuiltinAttr
castAttribute _ = internalError "castAttribute"

deriving instance Eq (Identifier ix) => Eq (Attribute ix)

type Attributes ix = [Attribute ix]

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
    
    -- | An N-ary unboxed tuple, N > 0.
  | TupleT [LType ix]

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
    
    -- | A type function
  | LamT
    { tDomains :: [Domain ix]
    , tBody :: LType ix
    }

    -- | A coercion type
  | CoT
    { tKind :: LType ix
    , tParam :: LType ix
    , tRng :: LType ix
    }

type LType ix = Located (Type ix)

-- | A variable binder, binding a type or a value depending on how it's used.
--
--   The bound variable's type or kind may be omitted in some contexts where
--   it can be inferred.  An omitted type is 'Nothing'.
data Domain ix = Domain (Identifier ix) (Maybe (LType ix))

boundVar :: Domain ix -> Identifier ix
boundVar (Domain v _) = v

boundType :: Domain ix -> Maybe (LType ix)
boundType (Domain _ t) = t

-- | Get the type of a bound variable.  Report an error if no type was given.
boundType' :: SourcePos -> (Identifier ix -> String) -> Domain ix -> LType ix
boundType' pos get_name (Domain _ (Just t)) = t
boundType' pos get_name (Domain v Nothing) =
  let message = show pos ++ ": Type must be given for variable " ++ get_name v
  in error message

-- | An expression
data Exp a =
    VarE (Identifier a)
  | IntE !Integer
  | UIntE !Integer
  | FloatE !Double
  | TupleE [LExp a]
  | TAppE (LExp a) (LType a)
  | AppE (LExp a) (LExp a)
  | LamE (Fun a)
  | CaseE (LExp a) [LExp a] [LAlt a]
  | LetE (Domain a) (LExp a) (LExp a)
    -- | Define a local type synonym.  Type synonyms are substituted before
    --   converting to Core.
  | LetTypeE (Identifier a) (LType a) (LExp a)
  | LetfunE [LDef a] (LExp a)
  | ExceptE (LType a)
  | CoerceE (LType a) (LType a) (LExp a)
    -- | Get an unboxed data type constructor's info variable.
  | UnboxedInfoE (Identifier a)
    -- | Get a boxed data constructor's info variable.
  | BoxedInfoE (Identifier a)

type LExp ix = Located (Exp ix)

data Alt a =
  Alt 
  { altPattern :: !(Pattern a)
  , altBody :: LExp a
  }

data Pattern a =
    ConPattern
    { -- | Size arguments are only allowed in nested patterns.  When the
      --   nested pattern is expanded into a case expression, these are used 
      --   as the case's size arguments.
      _altSizeArgs :: [LExp a]
    , altCon :: Identifier a
    , _altExTypes :: [Domain a]
    , altFields :: [Pattern a]
    }
  | TuplePattern
    { altFields :: [Pattern a]
    }
  | VarPattern
    { altDomain :: Domain a
    }
    -- | An ambiguous pattern consisting of just an identifier.
    --   It is resolved to a 'ConPattern' or a 'VarPattern' during name
    --   resolution, depending on whether the identifier is a data
    --   constructor.
  | ConOrVarPattern 
    { altIdentifier :: Identifier a
    }

altSizeArgs (ConPattern {_altSizeArgs = es}) = es
altSizeArgs (TuplePattern {}) = []
altSizeArgs (VarPattern {}) = []
altSizeArgs (ConOrVarPattern {}) = []

altExTypes (ConPattern {_altExTypes = ts}) = ts
altExTypes (TuplePattern {}) = []

type LAlt ix = Located (Alt ix)

data Def ix =
  Def 
  { dName :: Identifier ix
  , dFun :: Fun ix
  , dAttributes :: Attributes ix
  }

type LDef ix = Located (Def ix)

-- | A function that was specified in source code
data Fun ix =
  Fun
  { fTyParams :: [Domain ix]
  , fParams :: [Domain ix]
  , fRange :: LType ix
  , fBody :: LExp ix
  }

funType :: SourcePos -> (Identifier ix -> String) -> Fun ix -> LType ix
funType pos id_name f =
  let param_types = map (boundType' pos id_name) $ fParams f
      monotype = Prelude.foldr fun_type (fRange f) param_types
      polytype = Prelude.foldr forall_type monotype (fTyParams f)
  in polytype
  where
    fun_type d r = L pos (FunT d r)
    forall_type d r = L pos (AllT d r)

-- | A data constructor declaration.
--   Corresponds to @Type.Environment.DataConType@.
data DataConDecl ix =
  DataConDecl
  { dconVar :: Identifier ix
--    -- | Type parameters.
--  , dconParams :: [Domain ix]
    -- | Existential types.
  , dconExTypes :: [Domain ix]
    -- | Fields
  , dconArgs :: [LType ix]
    -- | Attributes
  , dconAttributes :: Attributes ix
  }

type LDataConDecl ix = Located (DataConDecl ix)

-- | A top-level type declaration.  This declares a piece of global data
--   or a data type.
--
--   A global variable may have a type function definition.  Type function
--   definitions are built-in, so the parser doesn't modify them.
data Decl ix = Decl (Identifier ix) !(Entity ix)

data Entity ix = 
    -- | A variable declaration
    VarEnt (LType ix) (Attributes ix)
    -- | A type declaration
  | TypeEnt (LType ix) (Attributes ix)
    -- | A type synonym declaration
  | TypeSynEnt (LType ix)
    -- | A data type definition
  | DataEnt [Domain ix] (LType ix) [LDataConDecl ix] (Attributes ix)
    -- | A global constant definition
  | ConstEnt (LType ix) (LExp ix) (Attributes ix)
    -- | A global function
  | FunEnt (Located (Fun ix)) (Attributes ix)

entityAttributes :: Entity ix -> Attributes ix
entityAttributes (VarEnt _ xs)      = xs
entityAttributes (TypeEnt _ xs)     = xs
entityAttributes (TypeSynEnt _)     = []
entityAttributes (DataEnt _ _ _ xs) = xs
entityAttributes (ConstEnt _ _ xs)  = xs
entityAttributes (FunEnt _ xs)      = xs

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
type PLExp = LExp Parsed
type PLAlt = LAlt Parsed
type PFun = Fun Parsed
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
type RLExp = LExp Resolved
type RFun = Fun Resolved
type RDecl = Decl Resolved
type RLDecl = LDecl Resolved
type RModule = Module Resolved

-- | Names are resolved to variables
type instance Identifier Resolved = ResolvedVar

newtype ResolvedVar = ResolvedVar Var

instance HasLevel ResolvedVar where
  getLevel (ResolvedVar v) = getLevel v

instance Eq ResolvedVar where
   ResolvedVar v1 == ResolvedVar v2 = v1 == v2

instance Ord ResolvedVar where
   ResolvedVar v1 `compare` ResolvedVar v2 = v1 `compare` v2
