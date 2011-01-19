-- | System F representation of Pyon code.
--
-- This is a short-lived representation produced as the output of type
-- inference.  It is translated to another form with the help of type
-- information.
-- Since it has no dependent types, renaming is not required.

{-# LANGUAGE DeriveDataTypeable, FlexibleInstances #-}
module SystemF.Syntax
    (Rec,
     SFExpOf(..),
     SFType(..),
     SFRecExp, RecAlt,
     RExp, RType, RAlt, RPat, RTyPat, RFun, RDef, RModule,
     Alt,
     Var,
     Lit(..),
     literalType,
     Pat(..),
     TyPat(..),
     ExpInfo, defaultExpInfo,
     SFExp,
     AltOf(..),
     FunOf(..), Fun,
     Def(..), DefGroup,
     Export(..),
     Module(..),
     isValueExp,
     unpackPolymorphicCall,
     {-
     mapSFExp, mapAlt, mapPat,
     traverseSFExp, traverseAlt, traversePat,-}
     isDictionaryCon
    )
where

import Control.Monad
import Data.Typeable

import Gluon.Common.Error
import Gluon.Common.Label
import Gluon.Common.SourcePos
import Gluon.Core(Structure, Rec, SynInfo, internalSynInfo)
import Gluon.Core.Level
import Builtins.Builtins
import Type.Var
import Type.Type
import Export

data family SFExpOf a :: * -> *
data family AltOf a :: * -> *
data family FunOf a :: * -> *

type SFRecExp s = SFExpOf s s
type RecAlt s = AltOf s s
type Fun s = FunOf s s
type Alt s = AltOf Rec s
data family SFType a :: *
data family Pat a :: *

type SFExp = SFExpOf Rec
type RExp = SFRecExp Rec
type RType = SFType Rec
type RAlt = AltOf Rec Rec
type RPat = Pat Rec
type RTyPat = TyPat Rec
type RDef = Def Rec
type RFun = Fun Rec
type RModule = Module Rec

newtype instance SFType Rec = SFType {fromSFType :: Type}

-- | Literal values.
--
-- Integer and floating-point literal values have a explicit type.  The type
-- must mention only constants, not type variables.
data Lit =
    IntL !Integer !Type
  | FloatL {-# UNPACK #-} !Double !Type
  | BoolL {-# UNPACK #-} !Bool
  | NoneL
  deriving(Typeable)

literalType :: Lit -> Type
literalType (IntL _ t) = t
literalType (FloatL _ t) = t
literalType (BoolL _) = VarT $ pyonBuiltin the_bool
literalType NoneL = VarT $ pyonBuiltin the_NoneType

-- | Patterns.
data instance Pat Rec =
    WildP RType                    -- ^ Wildcard pattern
  | VarP Var RType                 -- ^ Variable pattern binding
  | TupleP [Pat Rec]               -- ^ Tuple pattern

instance Typeable1 Pat where
  typeOf1 x = mkTyConApp (mkTyCon "SystemF.Syntax.Pat") []
          
-- | Type-level patterns.
data TyPat s = TyPat Var (SFType s)
             deriving(Typeable)

-- | Information common to all expressions.
type ExpInfo = SynInfo

-- | Default values of 'ExpInfo'.
defaultExpInfo :: ExpInfo
defaultExpInfo = internalSynInfo ObjectLevel

-- | Expressions.
data instance SFExpOf Rec s =
    -- | A variable reference
    VarE
    { expInfo :: ExpInfo
    , expVar :: Var
    }
    -- | A literal value
  | LitE
    { expInfo :: ExpInfo
    , expLit :: !Lit
    }
    -- | Application
  | AppE
    { expInfo :: ExpInfo
    , expOper :: SFRecExp s
    , expTyArgs :: [SFType s]
    , expArgs :: [SFRecExp s]
    }
{-    -- | Type application
  | TyAppE
    { expInfo :: ExpInfo
    , expOper :: SFRecExp s
    , expTyArg :: SFType s
    }
    -- | Function call
  | CallE
    { expInfo :: ExpInfo
    , expOper :: SFRecExp s
    , expArgs :: [SFRecExp s]
    }-}
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
  Alt { altConstructor :: !Var
      , altTyArgs :: [SFType s]
        
      , altParams :: [Pat s]
      , altBody :: SFRecExp s
      }

instance Typeable1 (SFExpOf Rec) where
  typeOf1 x =
    let con1 = mkTyCon "SystemF.Syntax.SFExpOf"
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
      , funReturnType :: SFType s -- ^ Return type
      , funBody :: SFRecExp s
      }

instance Typeable1 (FunOf Rec) where
  typeOf1 x =
    let con1 = mkTyCon "SystemF.Syntax.FunOf"
        arg1 = typeOf (undefined :: Rec)
    in mkTyConApp con1 [arg1]

data Def s = Def Var (Fun s)
         deriving(Typeable)

type DefGroup s = [Def s]

-- | An exported variable declaration
data Export s =
  Export
  { exportSourcePos :: SourcePos
  , exportSpec :: {-# UNPACK #-}!ExportSpec
  , exportFunction :: Fun s
  }

data Module s = Module !ModuleName [DefGroup s] [Export s]
            deriving(Typeable)

{-
-- | Map a function over an expression.
mapSFExp :: (Structure a, Structure b)
         => (SFRecExp a -> SFRecExp b)
         -> (RecAlt a -> RecAlt b)
         -> (FunOf a a -> FunOf b b)
         -> (SFType a -> SFType b)
         -> SFExpOf Rec a -> SFExpOf Rec b
mapSFExp e a f t expression =
  case expression
  of VarE info v -> VarE info v
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
       -> (SFType a -> SFType b)
       -> Alt a -> Alt b
mapAlt e t (Alt con ty_args params body) =
  Alt con (map t ty_args) [(v, repr ::: t ty) | (v, repr ::: ty) <- params] (e body)

-- | Map a monadic function over an expression.
traverseSFExp :: (Monad m, Structure a, Structure b)
              => (SFRecExp a -> m (SFRecExp b))
              -> (RecAlt a -> m (RecAlt b))
              -> (FunOf a a -> m (FunOf b b))
              -> (SFType a -> m (SFType b))
              -> SFExpOf Rec a -> m (SFExpOf Rec b)
traverseSFExp e a f t expression =
  case expression
  of VarE info v -> return $ VarE info v
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
            -> (SFType a -> m (SFType b))
            -> Alt a -> m (Alt b)
traverseAlt e t (Alt con ty_args params body) =
  Alt con `liftM` mapM t ty_args `ap` mapM traverse_param params `ap` e body
  where
    traverse_param (v, repr ::: ty) = do
      ty' <- t ty
      return (v, repr ::: ty')

mapPat :: (Structure a, Structure b)
       => (SFType a -> SFType b)
       -> Pat a -> Pat b
mapPat t pattern =
  case pattern
  of WildP ty -> WildP (t ty)
     VarP v ty -> VarP v (t ty)
     TupleP ps -> TupleP (map (mapPat t) ps)

traversePat :: (Monad m, Structure a, Structure b)
            => (SFType a -> m (SFType b))
            -> Pat a -> m (Pat b)
traversePat t pattern =
  case pattern
  of WildP ty -> WildP `liftM` t ty
     VarP v ty -> VarP v `liftM` t ty
     TupleP ps -> TupleP `liftM` mapM (traversePat t) ps
-}
-- | Return True only if the given expression has no side effects.
-- This function examines only expression constructors, and avoids inspecting
-- let or letrec expressions.
--
-- Constructors 'AppE', 'LetE', and 'LetrecE' are assumed to have side
-- effects.  Lambda expressions have no side effects, since they return but
-- do not execute their function.

isValueExp :: SFRecExp Rec -> Bool
isValueExp expression =
  case expression
  of VarE {} -> True
     LitE {} -> True
     AppE {} -> False
     FunE {} -> True
     LetE {} -> False
     LetrecE {} -> False
     CaseE {expScrutinee = scr, expAlternatives = alts} ->
       isValueExp scr && all (isValueExp . altBody) alts
       
{-
-- | Extract all type parameters from the expression.  Return the base 
-- expression, which is not a type application, and all the type parameters 
-- it was applied to.
unpackTypeApplication :: RExp -> (RExp, [Type])
unpackTypeApplication e = unpack [] e
  where
    unpack types (TyAppE {expOper = op, expTyArg = SFType ty}) =
      unpack (ty : types) op
    unpack types e = (e, types)-}

unpackPolymorphicCall :: RExp -> Maybe (RExp, [Type], [RExp])
unpackPolymorphicCall (AppE {expOper = op, expTyArgs = ts, expArgs = xs}) =
  Just (op, map fromSFType ts, xs)

unpackPolymorphicCall _ = Nothing

isDictionaryCon :: Var -> Bool
isDictionaryCon v = v `elem` [ pyonBuiltin the_Repr
                             , pyonBuiltin the_TraversableDict
                             , pyonBuiltin the_AdditiveDict
                             , pyonBuiltin the_MultiplicativeDict
                             ]