-- | System F representation of Pyon code.
--
-- This is a short-lived representation produced as the output of type
-- inference.  It is translated to another form with the help of type
-- information.
-- Since it has no dependent types, renaming is not required.

{-# LANGUAGE DeriveDataTypeable, FlexibleInstances #-}
module SystemF.Syntax
    (Lit(..),
     literalType,
     ExpInfo,
     defaultExpInfo,
     mkExpInfo,
     Typ(..), Pat(..), TyPat(..), Ret(..), Exp(..), Alt(..), Fun(..),
     SF,
     TypSF, PatSF, RetSF, ExpSF, AltSF, FunSF,
     BaseExp(..),
     BaseAlt(..),
     BaseFun(..),
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
import Gluon.Core.Level
import Builtins.Builtins
import Type.Var
import Type.Type
import Export

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

-- | Information common to all expressions.
data ExpInfo = ExpInfo SourcePos

defaultExpInfo :: ExpInfo
defaultExpInfo = ExpInfo noSourcePos

mkExpInfo :: SourcePos -> ExpInfo
mkExpInfo = ExpInfo

instance HasSourcePos ExpInfo where
  getSourcePos (ExpInfo p) = p

-- Data types used in representing code.  Data types are parameterized

data family Typ a               -- ^ A type; can be a wrapper around 'Type'
data family Pat a               -- ^ A pattern binding
data family TyPat a             -- ^ A pattern binding for types
data family Ret a               -- ^ A return declaration
data family Exp a               -- ^ An expression
data family Alt a               -- ^ A case alternative
data family Fun a               -- ^ A function

instance Typeable1 Typ where
  typeOf1 x = mkTyConApp (mkTyCon "SystemF.Syntax.Typ") []

instance Typeable1 Pat where
  typeOf1 x = mkTyConApp (mkTyCon "SystemF.Syntax.Pat") []
          
instance Typeable1 TyPat where
  typeOf1 x = mkTyConApp (mkTyCon "SystemF.Syntax.TyPat") []

instance Typeable1 Ret where
  typeOf1 x = mkTyConApp (mkTyCon "SystemF.Syntax.Ret") []

instance Typeable1 Exp where
  typeOf1 x = mkTyConApp (mkTyCon "SystemF.Syntax.Exp") []

instance Typeable1 Alt where
  typeOf1 x = mkTyConApp (mkTyCon "SystemF.Syntax.Alt") []

instance Typeable1 Fun where
  typeOf1 x = mkTyConApp (mkTyCon "SystemF.Syntax.Fun") []

-- | The System F code representation
data SF

type TypSF = Typ SF
type PatSF = Pat SF
type RetSF = Ret SF
type ExpSF = Exp SF
type AltSF = Alt SF
type FunSF = Fun SF

newtype instance Typ SF = TypSF {fromTypSF :: Type}
-- Pat SF is a data type
-- Ret SF is a data type
newtype instance Exp SF = ExpSF {fromExpSF :: BaseExp SF}
newtype instance Alt SF = AltSF {fromAltSF :: BaseAlt SF}
newtype instance Fun SF = FunSF {fromFunSF :: BaseFun SF}

-- | Patterns
data instance Pat SF =
    WildP Type                    -- ^ Wildcard pattern
  | VarP Var Type                 -- ^ Variable pattern binding
  | TupleP [PatSF]                -- ^ Tuple pattern

newtype instance Ret SF = RetSF {retSFType :: Type}

-- | Type-level patterns
data instance TyPat SF = TyPatSF Var Type

-- | Expressions
data BaseExp s =
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
    { expInfo   :: ExpInfo
    , expOper   :: Exp s
    , expTyArgs :: [Typ s]
    , expArgs   :: [Exp s]
    }
    -- | Lambda expression
  | LamE
    { expInfo :: ExpInfo
    , expFun  :: Fun s
    }
    -- | Let expression
  | LetE
    { expInfo   :: ExpInfo
    , expBinder :: Pat s
    , expValue  :: Exp s
    , expBody   :: Exp s
    }
    -- | Recursive definition group
  | LetrecE
    { expInfo :: ExpInfo
    , expDefs :: [Def s]
    , expBody :: Exp s
    }
    -- | Case analysis 
  | CaseE
    { expInfo :: ExpInfo
    , expScrutinee :: Exp s
    , expAlternatives :: [Alt s]
    }

data BaseAlt s =
  Alt { altConstructor :: !Var
      , altTyArgs      :: [Typ s]
        
      , altParams      :: [Pat s]
      , altBody        :: Exp s
      }

instance HasSourcePos (BaseExp s) where
  getSourcePos e = getSourcePos (expInfo e)

data BaseFun s =
  Fun { funInfo       :: ExpInfo
      , funTyParams   :: [TyPat s]   -- ^ Type parameters
      , funParams     :: [Pat s]     -- ^ Object parameters
      , funReturn     :: Ret s       -- ^ Return type
      , funBody       :: Exp s
      }

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

-- | Return True only if the given expression has no side effects.
-- This function examines only expression constructors, and avoids inspecting
-- let or letrec expressions.
--
-- Constructors 'AppE', 'LetE', and 'LetrecE' are assumed to have side
-- effects.  Lambda expressions have no side effects, since they return but
-- do not execute their function.

isValueExp :: ExpSF -> Bool
isValueExp (ExpSF expression) =
  case expression
  of VarE {} -> True
     LitE {} -> True
     AppE {} -> False
     LamE {} -> True
     LetE {} -> False
     LetrecE {} -> False
     CaseE {expScrutinee = scr, expAlternatives = alts} ->
       isValueExp scr && all (isValueExp . altBody . fromAltSF) alts
       
unpackPolymorphicCall :: ExpSF -> Maybe (ExpSF, [Type], [ExpSF])
unpackPolymorphicCall (ExpSF (AppE {expOper = op, expTyArgs = ts, expArgs = xs})) =
  Just (op, map fromTypSF ts, xs)

unpackPolymorphicCall _ = Nothing

isDictionaryCon :: Var -> Bool
isDictionaryCon v = v `elem` [ pyonBuiltin the_Repr
                             , pyonBuiltin the_TraversableDict
                             , pyonBuiltin the_AdditiveDict
                             , pyonBuiltin the_MultiplicativeDict
                             ]