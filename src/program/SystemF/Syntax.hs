{-| System F representation of Pyon code.

These data structures are used in two slightly different ways, before and  
after representation selection.  After representation selection,
value-level variables are annotated with a \"representation\", and
there is a distinguished 'Pat' constructor for patterns that bind writable
variables.

In all cases, the data structures are very close to basic Haskell or ML
data structures.  A program is a collection of functions ('Fun') whose
body is an expression ('Exp').  Values are bound by patterns ('TyPat', 'Pat')
and case statements branch to alternatives ('Alt').
-}

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
     Def(..), mkDef, mkWrapperDef,
     mapDefiniens,
     mapMDefiniens,
     modifyDefAnnotation,
     defIsWrapper,
     DefAnn(..),
     defaultDefAnn,
     DefGroup(..), defGroupMembers,
     Export(..),
     Module(..),
     isValueExp,
     unpackPolymorphicCall,
     {-
     mapSFExp, mapAlt, mapPat,
     traverseSFExp, traverseAlt, traversePat,-}
     isDictionaryTypeCon,
     isDictionaryDataCon,
     isSingletonCon,
     isReprCon
    )
where

import Control.Monad
import Data.Typeable
import qualified Data.Foldable
import Data.Monoid
import qualified Data.Traversable

import Common.Error
import Common.Label
import Common.SourcePos
import Builtins.Builtins
import Type.Type
import Export

-- | Literal values.
--
-- Integer and floating-point literal values have a explicit type.  The type
-- must mention only constants, not type variables.
data Lit =
    IntL !Integer !Type
  | FloatL {-# UNPACK #-} !Double !Type
  deriving(Typeable)

literalType :: Lit -> Type
literalType (IntL _ t) = t
literalType (FloatL _ t) = t

-- | Information common to all expressions.
data ExpInfo = ExpInfo SourcePos

defaultExpInfo :: ExpInfo
defaultExpInfo = ExpInfo noSourcePos

mkExpInfo :: SourcePos -> ExpInfo
mkExpInfo = ExpInfo

instance HasSourcePos ExpInfo where
  getSourcePos (ExpInfo p) = p

-- Data types used in representing code.  Data types are indexed by a
-- data format; different indices are used in different stages of the
-- compiler to customize the data structures.

data family Typ a               -- A type; can be a wrapper around 'Type'
data family Pat a               -- A pattern binding
data family TyPat a             -- A pattern binding for types
data family Ret a               -- A return declaration
data family Exp a               -- An expression
data family Alt a               -- A case alternative
data family Fun a               -- A function

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
newtype instance TyPat SF = TyPatSF Binder

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
  | LetfunE
    { expInfo :: ExpInfo
    , expDefs :: DefGroup (Def s)
    , expBody :: Exp s
    }
    -- | Case analysis 
  | CaseE
    { expInfo :: ExpInfo
    , expScrutinee :: Exp s
    , expAlternatives :: [Alt s]
    }
    -- | Interrupt execution.  This expression does not return.
  | ExceptE
    { expInfo :: ExpInfo
    , expType :: Type
    }

data BaseAlt s =
  Alt { altConstructor :: !Var
      , altTyArgs      :: [Typ s]
      , altExTypes     :: [TyPat s]
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

-- | A function definition
data Def s =
  Def
  { definiendum :: Var
  , defAnnotation :: {-#UNPACK#-}!DefAnn
  , definiens :: Fun s
  }
  deriving(Typeable)

mkDef :: Var -> Fun s -> Def s
mkDef v f = Def v defaultDefAnn f

mkWrapperDef :: Var -> Fun s -> Def s
mkWrapperDef v f = Def v (DefAnn True) f

mapDefiniens :: (Fun s -> Fun s') -> Def s -> Def s'
mapDefiniens f def = def {definiens = f $ definiens def}

mapMDefiniens :: Monad m => (Fun s -> m (Fun s')) -> Def s -> m (Def s')
mapMDefiniens f def = do fun <- f (definiens def)
                         return $ def {definiens = fun}

modifyDefAnnotation :: (DefAnn -> DefAnn) -> Def s -> Def s
modifyDefAnnotation f d = d {defAnnotation = f (defAnnotation d)}

defIsWrapper :: Def s -> Bool
defIsWrapper def = defAnnWrapper $ defAnnotation def

-- | Annotations on a function definition
data DefAnn =
  DefAnn
  { -- | True if the definition is a wrapper function.
    defAnnWrapper :: {-#UNPACK#-}!Bool
  }

defaultDefAnn :: DefAnn
defaultDefAnn = DefAnn False

-- | A definition group consists of either a single non-recursive definition
--   or a list of recursive definitions.  The list must not be empty.
data DefGroup a = NonRec a | Rec [a]

defGroupMembers :: DefGroup a -> [a]
defGroupMembers (NonRec x) = [x]
defGroupMembers (Rec xs) = xs

instance Functor DefGroup where
  fmap f (NonRec x) = NonRec (f x)
  fmap f (Rec xs) = Rec (map f xs)

instance Data.Foldable.Foldable DefGroup where
  foldMap f (NonRec x) = f x
  foldMap f (Rec xs) = mconcat (map f xs)
  foldr f z (NonRec x) = f x z
  foldr f z (Rec xs) = foldr f z xs

instance Data.Traversable.Traversable DefGroup where
  traverse f (NonRec x) = fmap NonRec (f x)
  traverse f (Rec xs) = fmap Rec (Data.Traversable.traverse f xs)
  mapM f (NonRec x) = liftM NonRec (f x)
  mapM f (Rec xs) = liftM Rec (Data.Traversable.mapM f xs)

-- | An exported variable declaration
data Export s =
  Export
  { exportSourcePos :: SourcePos
  , exportSpec :: {-# UNPACK #-}!ExportSpec
  , exportFunction :: Fun s
  }

data Module s = Module !ModuleName [DefGroup (Def s)] [Export s]
            deriving(Typeable)

-- | Return True only if the given expression has no side effects.
-- This function examines only expression constructors, and avoids inspecting
-- let or letfun expressions.
--
-- Constructors 'AppE', 'LetE', and 'LetfunE' are assumed to have side
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
     LetfunE {} -> False
     CaseE {expScrutinee = scr, expAlternatives = alts} ->
       isValueExp scr && all (isValueExp . altBody . fromAltSF) alts
     ExceptE {} -> False
       
unpackPolymorphicCall :: ExpSF -> Maybe (ExpSF, [Type], [ExpSF])
unpackPolymorphicCall (ExpSF (AppE {expOper = op, expTyArgs = ts, expArgs = xs})) =
  Just (op, map fromTypSF ts, xs)

unpackPolymorphicCall _ = Nothing

-- | Return True iff this is a dictionary type constructor.
isDictionaryTypeCon :: Var -> Bool
isDictionaryTypeCon v =
  v `elem` [ pyonBuiltin the_Repr
           , pyonBuiltin the_TraversableDict
           , pyonBuiltin the_EqDict
           , pyonBuiltin the_OrdDict
           , pyonBuiltin the_AdditiveDict
           , pyonBuiltin the_MultiplicativeDict
           , pyonBuiltin the_FractionalDict
           , pyonBuiltin the_RemainderDict
           , pyonBuiltin the_FloatingDict
           , pyonBuiltin the_VectorDict
           ]

-- | Return True iff this is a dictionary data constructor.
isDictionaryDataCon :: Var -> Bool
isDictionaryDataCon v =
  v `elem` [ -- There's no data constructor for "Repr" in System F
             pyonBuiltin the_traversableDict
           , pyonBuiltin the_eqDict
           , pyonBuiltin the_ordDict
           , pyonBuiltin the_additiveDict
           , pyonBuiltin the_multiplicativeDict
           , pyonBuiltin the_fractionalDict
           , pyonBuiltin the_remainderDict
           , pyonBuiltin the_floatingDict
           , pyonBuiltin the_vectorDict
           ]

-- | Return True if this is a singleton type constructor.
--   Return False if not a singleton type constructor, or if unknown.
--
--   Singleton types are data types that have exactly one value.
isSingletonCon :: Var -> Bool
isSingletonCon v = isDictionaryTypeCon v

-- | Return True iff this is a @Repr@ dictionary constructor.
isReprCon :: Var -> Bool
isReprCon v =
  v `elem` [ pyonBuiltin the_repr_int
           , pyonBuiltin the_repr_float
           , pyonBuiltin the_repr_bool
           , pyonBuiltin the_repr_list
           , pyonBuiltin the_repr_Complex
           , pyonBuiltin the_repr_PyonTuple2
           , pyonBuiltin the_repr_PyonTuple3
           , pyonBuiltin the_repr_PyonTuple4
           , pyonBuiltin the_repr_Box
           , pyonBuiltin the_repr_Boxed
           , pyonBuiltin the_repr_Stream
           ]
