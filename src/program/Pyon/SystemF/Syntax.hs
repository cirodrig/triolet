-- | System F representation of Pyon code.
--
-- This is a short-lived representation produced as the output of type
-- inference.  It is translated to another form with the help of type
-- information.
-- Since it has no dependent types, renaming is not required.

{-# LANGUAGE DeriveDataTypeable, EmptyDataDecls, TypeFamilies, FlexibleInstances #-}
module Pyon.SystemF.Syntax
    (Rec,
     SFExpOf(..), TypeOf,
     SFRecExp, RecType, RecAlt,
     RExp, RAlt, RType, RPat, RTyPat, RFun, RDef, RModule,
     Alt,
     Var,
     Lit(..),
     Pat(..),
     TyPat(..),
     Binder(..),
     ExpInfo, defaultExpInfo,
     SFExp,
     AltOf(..),
     FunOf(..), Fun,
     Def(..), DefGroup,
     Export(..),
     Module(..),
     isValueExp,
     unpackTypeApplication, unpackPolymorphicCall,
     
     mapSFExp, mapAlt, mapPat,
     traverseSFExp, traverseAlt, traversePat
    )
where

import Control.Monad
import Data.Typeable

import Gluon.Common.Error
import Gluon.Common.SourcePos
import qualified Gluon.Core as Gluon
import Gluon.Core(Structure, Rec, Var, Binder(..))

import Pyon.SystemF.Builtins

data family SFExpOf a :: * -> *
data family AltOf a :: * -> *
data family FunOf a :: * -> *

type TypeOf = Gluon.ExpOf

type SFRecExp s = SFExpOf s s
type RecAlt s = AltOf s s
type Fun s = FunOf s s
type RecType s = TypeOf s s

type Alt s = AltOf Rec s

type SFExp = SFExpOf Rec
type RExp = SFRecExp Rec
type RAlt = AltOf Rec Rec
type RType = RecType Rec
type RPat = Pat Rec
type RTyPat = TyPat Rec
type RDef = Def Rec
type RFun = Fun Rec
type RModule = Module Rec

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
    -- | Case analysis 
  | CaseE
    { expInfo :: ExpInfo
    , expScrutinee :: SFRecExp s
    , expAlternatives :: [RecAlt s]
    }

data instance AltOf Rec s =
  Alt { altConstructor :: !Gluon.Con
      , altTyArgs :: [RecType s]
      , altParams :: [Binder s ()]
      , altBody :: SFRecExp s
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

data instance FunOf Rec s =
  Fun { funInfo :: ExpInfo
      , funTyParams :: [TyPat s] -- ^ Type parameters
      , funParams :: [Pat s]     -- ^ Object parameters
      , funReturnType :: RecType s -- ^ Return type
      , funBody :: SFRecExp s
      }

instance Typeable1 (FunOf Rec) where
  typeOf1 x =
    let con1 = mkTyCon "Pyon.SystemF.Syntax.FunOf"
        arg1 = typeOf (undefined :: Rec)
    in mkTyConApp con1 [arg1]

data Def s = Def Var (Fun s)
         deriving(Typeable)

type DefGroup s = [Def s]

-- | An exported variable declaration
data Export =
  Export
  { exportSourcePos :: SourcePos
  , exportVariable :: Var
  }

data Module s = Module [DefGroup s] [Export]
            deriving(Typeable)

-- | Map a function over an expression.
mapSFExp :: (Structure a, Structure b)
         => (SFRecExp a -> SFRecExp b)
         -> (RecAlt a -> RecAlt b)
         -> (FunOf a a -> FunOf b b)
         -> (RecType a -> RecType b)
         -> SFExpOf Rec a -> SFExpOf Rec b
mapSFExp e a f t expression =
  case expression
  of VarE info v -> VarE info v
     ConE info c -> ConE info c
     LitE info l ty -> LitE info l (t ty)
     TyAppE info op arg -> TyAppE info (e op) (t arg)
     CallE info op args -> CallE info (e op) (map e args)
     FunE info fun -> FunE info (f fun)
     LetE info p e1 e2 -> LetE info (mapPat t p) (e e1) (e e2)
     LetrecE info defs body -> LetrecE info (map mapDef defs) (e body)
     CaseE info scr alts -> CaseE info (e scr) (map a alts)
  where
    mapDef (Def v fun) = Def v (f fun)

mapAlt :: (Structure a, Structure b)
       => (SFRecExp a -> SFRecExp b)
       -> (RecType a -> RecType b)
       -> Alt a -> Alt b
mapAlt e t (Alt con ty_args params body) =
  Alt con (map t ty_args) (map (Gluon.mapBinder id t) params) (e body)

-- | Map a monadic function over an expression.
traverseSFExp :: (Monad m, Structure a, Structure b)
              => (SFRecExp a -> m (SFRecExp b))
              -> (RecAlt a -> m (RecAlt b))
              -> (FunOf a a -> m (FunOf b b))
              -> (RecType a -> m (RecType b))
              -> SFExpOf Rec a -> m (SFExpOf Rec b)
traverseSFExp e a f t expression =
  case expression
  of VarE info v -> return $ VarE info v
     ConE info c -> return $ ConE info c
     LitE info l ty -> LitE info l `liftM` t ty
     TyAppE info op arg -> TyAppE info `liftM` e op `ap` t arg
     CallE info op args -> CallE info `liftM` e op `ap` mapM e args
     FunE info fun -> FunE info `liftM` f fun
     LetE info p e1 e2 ->
       LetE info `liftM` traversePat t p `ap` e e1 `ap` e e2
     LetrecE info defs body ->
       LetrecE info `liftM` mapM traverseDef defs `ap` e body
     CaseE info scr alts ->
       CaseE info `liftM` e scr `ap` mapM a alts
  where
    traverseDef (Def v fun) = Def v `liftM` f fun
    
traverseAlt :: (Monad m, Structure a, Structure b)
            => (SFRecExp a -> m (SFRecExp b))
            -> (RecType a -> m (RecType b))
            -> Alt a -> m (Alt b)
traverseAlt e t (Alt con ty_args params body) =
  Alt con `liftM` mapM t ty_args `ap` mapM (Gluon.traverseBinder return t) params `ap` e body

mapPat :: (Structure a, Structure b)
       => (RecType a -> RecType b)
       -> Pat a -> Pat b
mapPat t pattern =
  case pattern
  of WildP ty -> WildP (t ty)
     VarP v ty -> VarP v (t ty)
     TupleP ps -> TupleP (map (mapPat t) ps)

traversePat :: (Monad m, Structure a, Structure b)
            => (RecType a -> m (RecType b))
            -> Pat a -> m (Pat b)
traversePat t pattern =
  case pattern
  of WildP ty -> WildP `liftM` t ty
     VarP v ty -> VarP v `liftM` t ty
     TupleP ps -> TupleP `liftM` mapM (traversePat t) ps

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
     TyAppE {expOper = e} -> isValueExp e
     CallE {} -> False
     FunE {} -> True
     LetE {} -> False
     LetrecE {} -> False
     CaseE {expScrutinee = scr, expAlternatives = alts} ->
       isValueExp scr && all (isValueExp . altBody) alts
       
-- | Extract all type parameters from the expression.  Return the base 
-- expression, which is not a type application, and all the type parameters 
-- it was applied to.
unpackTypeApplication :: RExp -> (RExp, [RType])
unpackTypeApplication e = unpack [] e
  where
    unpack types (TyAppE {expOper = op, expTyArg = ty}) =
      unpack (ty : types) op
    unpack types e = (e, types)

unpackPolymorphicCall :: RExp -> Maybe (RExp, [RType], [RExp])
unpackPolymorphicCall (CallE {expOper = op, expArgs = args}) =
  case unpackTypeApplication op
  of (poly_op, ty_args) -> Just (poly_op, ty_args, args)

unpackPolymorphicCall _ = Nothing