{-| Type-annotated expressions.

This is a temporary program representation created by type inference.
It is quite similar to the internal System F form.  However, type inference
is allowed to mutate some parts of the program after creating it: 

1. Types can be mutated by unification.  This is accounted for by making each
   'TIType' be an IO action that reads the real type.  The IO actions are 
   only run after all unification has finished.

2. Placeholders can be filled in by constraint solving.  Placeholders contain
   IO references that are eventually filled in with the placeholder's final
   value.

-}

module Untyped.TIExp where

import Control.Concurrent.MVar
import Control.Monad
import Control.Monad.Trans
import Data.Maybe
import Data.IORef

import Common.Error
import Common.SourcePos
import qualified SystemF.Syntax as SF
import qualified Builtins.Builtins as SF
import SystemF.Syntax (ExpInfo, DefGroup)
import Untyped.Kind
import {-# SOURCE #-} Untyped.TIMonad
import Untyped.Type
import Untyped.Unif
import Untyped.Variable as Untyped
import qualified Type.Type as SF
import qualified Type.Var as SF
import Export

-- | A representation dictionary for an expression's result type.
data TIRepr =
    -- | The natural representation is boxed.  Such objects do
    --   not need representation dictionaries.
    TIBoxed
    -- | The natural representation is a value, and the object will
    --   never need to be coerced.
    --   Equality coercions are inserted by the compiler in such a way that
    --   they'll never need to be coerced.
  | TIUncoercedVal
    -- | A representation dictionary generated by inferring the value of
    --   a placeholder.
  | TIInferredRepr TIExp
    -- | A Core representation dictionary.
    --   This is an application of a variable to type arguments and
    --   either pre-made expressions or other representations.
    --
    --   Arguments are eventually turned into an expression.
  | TICoreRepr SF.Var [TIType] [Either TIExp TIRepr]

-- | Create the representation of the evidence of a predicate.
--
--   Class dictionaries are always boxed.
--   Equality coercions are always 
predicateRepr :: Predicate -> TIRepr
predicateRepr (IsInst {})  = TIBoxed
predicateRepr (IsEqual {}) = TIUncoercedVal

data TIInfo = TIInfo !SourcePos !TIRepr
-- type TIInfo = ExpInfo

tiInfo :: SourcePos -> TIRepr -> TIInfo
tiInfo pos r = TIInfo pos r

-- Note on 'TIRepr' annotations
-- Let, letrec, and case expressions are not annotated with a 'TIRepr'. 
-- The reason is that, to generate 'TIRepr' annotations for other expressions, 
-- type inference sometimes inserts code consisting of let, letrec, and/or
-- case expressions.  The needed 'TIRepr' value is available in the body of
-- the inserted expressions.  It's not available outside the expression, so
-- we can't produce an annotation.

-- | Type-inferred expressions
data TIExp =
    -- Expressions that translate directly to System F
    VarTE !TIInfo !SF.Var
  | LitTE !TIInfo !SF.Lit
  | ConTE !TIInfo !TIConInst [TIRepr] [TIExp]
  | AppTE !TIInfo TIExp [TIType] [TIExp]
  | LamTE !TIInfo TIFun
    -- Let, Letfun, and Case expressions aren't annotated with representation
    -- information
  | LetTE SourcePos TIPat TIExp TIExp
  | LetfunTE SourcePos (DefGroup TIDef) TIExp
  | CaseTE SourcePos TIExp [TIRepr] [TIAlt]
  | CoerceTE !TIInfo TIType TIType TIExp 
  | ArrayTE !TIInfo TIType [TIExp]

    -- A delayed function application
  | MkExpTE !TIInfo ([SF.Type] -> [SF.ExpSF] -> SF.ExpSF) [TIType] [TIExp]
    
    -- Placeholder expressions
  | PlaceholderTE Placeholder

  | RecVarPH
    { phExpInfo :: !TIInfo
    , phExpVariable :: Untyped.Variable
    , phExpTyVar :: TyCon
    , phExpResolution :: {-# UNPACK #-} !(MVar TIExp)
    }
    -- | A placeholder for a class dictionary
  | DictPH
    { phExpInfo :: !TIInfo
    , phExpPredicate :: Predicate
    , phExpResolution :: {-# UNPACK #-} !(MVar TIExp)
    }

data TIPat =
    TIWildP TIType
  | TIVarP SF.Var TIType
  | TITupleP [TIPat]

data TITyPat = TITyPat SF.Var TIType

data TIFun =
  TIFun SourcePos               -- Source position
        [TITyPat]               -- Type parameters
        [TIPat]                 -- Parameters
        TIType                  -- Return type
        TIExp                   -- Body

data TIDef =
  TIDef SF.Var SF.DefAnn TIFun

data TIAlt =
  TIAlt !TIDeConInst [TIPat] TIExp

-- | A Placeholder stands for a dictionary or recursive variable
data Placeholder = DictPlaceholder DictP | RecVarPlaceholder RecVarP
type Placeholders = [Placeholder]

data DictP   = DictP Predicate (IORef (Maybe SF.Var))
data RecVarP = RecVarP Variable (IORef (Maybe TIExp))

dictPPredicate (DictP p _) = p

isDictPSet :: DictP -> IO Bool
isDictPSet (DictP _ r) = liftM isJust $ readIORef r

setDictP :: DictP -> SF.Var -> IO ()
setDictP (DictP _ r) e = writeIORef r (Just e)

isRecVarPSet :: RecVarP -> IO Bool
isRecVarPSet (RecVarP _ r) = liftM isJust $ readIORef r

setRecVarP :: RecVarP -> TIExp -> IO ()
setRecVarP (RecVarP _ r) e = writeIORef r (Just e)

-- | Types are not evaluated until type inference completes
newtype TIType = DelayedType (TE SF.Type)

data TIConInst = TIConInst !SF.Var [TIType] [TIType]

data TIDeConInst = TIDeConInst !SF.Var [TIType] [TITyPat]

data TIExport = TIExport !SourcePos ExportSpec TIFun

