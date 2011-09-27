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
    (-- * Demand information
     Dmd(..), unknownDmd,
     Multiplicity(..), Specificity(..),
     HeapMap(..),
     joinHeapMap, outerJoinHeapMap,
     
     -- * Representation of code
     Typ(..), Pat(..), TyPat(..), Exp(..), Alt(..), Fun(..),
     CInst(..), DeCInst(..),

     -- ** Annotations on expressions
     ExpInfo,
     defaultExpInfo,
     mkExpInfo,
     
     -- ** Literals
     Lit(..),
     literalType,
     
     -- ** Data types
     ConInst(..),
     summarizeConstructor,
     conTyArgs, conExTypes, conTypes, conFieldKinds, conType, isVarCon,
     DeConInst(..),
     summarizeDeconstructor,
     deConTyArgs, deConExTypes, deConFieldKinds, isVarDeCon,

     -- ** Expressions and functions
     BaseExp(..),
     BaseAlt(..),
     getAltExTypes,
     BaseFun(..),
     
     -- ** Function definitions
     Def(..), mkDef, mkWrapperDef,
     mapDefiniens,
     mapMDefiniens,
     modifyDefAnnotation,
     defIsWrapper,
     DefAnn(..),
     defaultDefAnn,
     InliningAnnotation(..),
     DefGroup(..), defGroupMembers,
     
     -- ** Top-level constructs
     Export(..),
     Module(..),
     
     -- ** System F types
     SF,
     TypSF, PatSF, ExpSF, AltSF, FunSF, CInst, DeCInstSF,

     -- * Utility functions
     isValueExp,
     unpackPolymorphicCall,
     isDictionaryTypeCon,
     isDictionaryDataCon,
     isSingletonCon,
     isReprCon
    )
where

import Control.Monad
import Data.Typeable
import qualified Data.Foldable
import Data.Function
import qualified Data.List as List
import Data.Maybe
import Data.Monoid
import qualified Data.Traversable

import Common.Error
import Common.Label
import Common.SourcePos
import Builtins.Builtins
import Type.Type
import Type.Environment
import Type.Eval
import Export

-------------------------------------------------------------------------------
-- Demand information

-- Most demand-related functions are defined in Demand.hs.

-- | Variables are assigned a demand in 'Dmd'
data Dmd = Dmd { multiplicity :: !Multiplicity
               , specificity :: !Specificity
               }

-- | The default demand value, 
--   assigned to variables before demand analysis has run.
unknownDmd :: Dmd
unknownDmd = Dmd ManyUnsafe Used

-- | How many times a variable is used.
data Multiplicity =
    Dead            -- ^ Not used
  | OnceSafe        -- ^ Used once, not under lambda
  | ManySafe        -- ^ Used in multiple mutually-exclusive locations
  | OnceUnsafe      -- ^ Used once under a lambda
  | ManyUnsafe      -- ^ Used many times
  deriving(Eq)

-- | What part of a value is used.
data Specificity =
    Used              -- ^ Used in an unknown way.  This is the top value.
  | Inspected
    -- ^ Deconstructed by a case statement or read by 'copy'.

  | Decond !DeConInst [Specificity]
    -- ^ Deconstructed at a known constructor.
    --
    --   We save the type arguments and existential type parameters
    --   of the data constructor
    --   so that we can create a @case@ statement from this info.
    --
    --   Includes a list describing how each field is used.  There is one list
    --   member for each value field.

  | Written Specificity
    -- ^ An initializer function is executed, and its result is demanded.

  | Read (HeapMap Specificity)
    -- ^ Values are read out of memory and used at the given specificities.
    --
    --   Any heap location that is not in the map is 'Unused'.

  | Unused            -- ^ Not used at all.  This is the bottom value.

-- | A map assigning properties to locations in the heap.  The key stands for
--   the output pointer.
newtype HeapMap a = HeapMap [(Var, a)]

-- | Relational join on a HeapMap
joinHeapMap :: (a -> b -> c) -> HeapMap a -> HeapMap b -> HeapMap c
joinHeapMap f (HeapMap assocs1) (HeapMap assocs2) = HeapMap new_map
  where
    new_map = do
      (v1, x) <- assocs1
      y <- maybeToList $ List.lookup v1 assocs2
      return (v1, f x y)

-- | Relational outer join on a HeapMap
outerJoinHeapMap :: (Maybe a -> Maybe b -> c)
                 -> HeapMap a -> HeapMap b -> HeapMap c
outerJoinHeapMap f (HeapMap assocs1) (HeapMap assocs2) = HeapMap new_map
  where
    a1 = List.sortBy (compare `on` fst) assocs1
    a2 = List.sortBy (compare `on` fst) assocs2
    new_map = join a1 a2

    join xs@((v1, x):xs') ys@((v2, y):ys') =
      case compare v1 v2
      of LT -> (v1, f (Just x) Nothing)  : join xs' ys
         EQ -> (v1, f (Just x) (Just y)) : join xs' ys'
         GT -> (v2, f Nothing  (Just y)) : join xs ys'
    join xs [] = [(v, f (Just x) Nothing) | (v, x) <- xs]
    join [] ys = [(v, f Nothing (Just y)) | (v, y) <- ys]

-------------------------------------------------------------------------------

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
data family Exp a               -- An expression
data family Alt a               -- A case alternative
data family Fun a               -- A function
data family CInst a             -- A constructor instantiated to a type
data family DeCInst a           -- A constructor pattern instantiated to a type

instance Typeable1 Typ where
  typeOf1 x = mkTyConApp (mkTyCon "SystemF.Syntax.Typ") []

instance Typeable1 Pat where
  typeOf1 x = mkTyConApp (mkTyCon "SystemF.Syntax.Pat") []
          
instance Typeable1 TyPat where
  typeOf1 x = mkTyConApp (mkTyCon "SystemF.Syntax.TyPat") []

instance Typeable1 Exp where
  typeOf1 x = mkTyConApp (mkTyCon "SystemF.Syntax.Exp") []

instance Typeable1 Alt where
  typeOf1 x = mkTyConApp (mkTyCon "SystemF.Syntax.Alt") []

instance Typeable1 Fun where
  typeOf1 x = mkTyConApp (mkTyCon "SystemF.Syntax.Fun") []

instance Typeable1 CInst where
  typeOf1 x = mkTyConApp (mkTyCon "SystemF.Syntax.CInst") []

instance Typeable1 DeCInst where
  typeOf1 x = mkTyConApp (mkTyCon "SystemF.Syntax.DeCInst") []

-- | The System F code representation
data SF

type TypSF = Typ SF
type PatSF = Pat SF
type ExpSF = Exp SF
type AltSF = Alt SF
type FunSF = Fun SF
type CInstSF = CInst SF
type DeCInstSF = DeCInst SF

newtype instance Typ SF = TypSF {fromTypSF :: Type}
-- Pat SF is a data type
newtype instance Exp SF = ExpSF {fromExpSF :: BaseExp SF}
newtype instance Alt SF = AltSF {fromAltSF :: BaseAlt SF}
newtype instance Fun SF = FunSF {fromFunSF :: BaseFun SF}
newtype instance CInst SF = CInstSF {fromCInstSF :: ConInst}
newtype instance DeCInst SF = DeCInstSF {fromDeCInstSF :: DeConInst}

-- | Patterns
data instance Pat SF =
    WildP Type                    -- ^ Wildcard pattern
  | VarP Var Type                 -- ^ Variable pattern binding
  | TupleP [PatSF]                -- ^ Tuple pattern

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
    -- | A data constructor application.
    --   Data constructor applications produce a value or initializer function.
  | ConE
    { expInfo      :: ExpInfo
    , expCon       :: !(CInst s)
    , expArgs      :: [Exp s]
    }
    {- Subsumed by ConE
    -- | An unboxed tuple expression
  | UTupleE
    { expInfo :: ExpInfo
    , expArgs :: [Exp s]
    } -}
    -- | Function application.
    --   Data constructor applications are represented by 'ConE' instead.
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
    -- | A type coercion
  | CoerceE
    { expInfo :: ExpInfo
    , expArgType :: Typ s       -- ^ Type of body
    , expRetType :: Typ s       -- ^ Type of coerced result
    , expBody :: Exp s
    }

data BaseAlt s =
  Alt { altCon :: !(DeCInst s)
      , altParams :: [Pat s]
      , altBody :: Exp s
      }

getAltExTypes alt = deConExTypes $ fromDeCInstSF $ altCon alt

-- | A summary of a data constructor.  For constructors of the same data type,
--   two summaries are equal iff they were created from the same constructor
--   or deconstrutor.
type ConInstSummary = Maybe Var

-- | A constructor instance appearing in a data constructor application
data ConInst =
    VarCon !Var [Type] [Type]
  | TupleCon [Type]

-- | Get a summary of the constructor.
summarizeConstructor :: ConInst -> ConInstSummary
summarizeConstructor (VarCon v _ _) = Just v
summarizeConstructor (TupleCon _)   = Nothing

conTyArgs :: ConInst -> [Type]
conTyArgs (VarCon _ ts _) = ts
conTyArgs (TupleCon ts)   = ts

conExTypes :: ConInst -> [Type]
conExTypes (VarCon _ _ ts) = ts
conExTypes (TupleCon _)    = []

conTypes :: ConInst -> [Type]
conTypes t = conTyArgs t ++ conExTypes t

conFieldKinds :: TypeEnv -> ConInst -> [BaseKind]
conFieldKinds tenv (VarCon op _ _) =
  let Just data_con = lookupDataCon op tenv
  in dataConFieldKinds tenv data_con

conFieldKinds tenv (TupleCon types) =
  map (toBaseKind . typeKind tenv) types

conType :: EvalMonad m => ConInst -> m ([Type], Type)
conType (VarCon v ty_args ex_types) = do
  tenv <- getTypeEnv
  let Just data_con = lookupDataCon v tenv
  instantiateDataConTypeWithExistentials data_con (ty_args ++ ex_types)

conType (TupleCon ty_args) = do
  tenv <- getTypeEnv
  let kinds = map (toBaseKind . typeKind tenv) ty_args
  return (ty_args, UTupleT kinds `typeApp` ty_args)

isVarCon (VarCon {}) = True
isVarCon _           = False

-- | A constructor instance appearing in a pattern match
data DeConInst =
    VarDeCon !Var [Type] [Binder]
  | TupleDeCon [Type]

-- | Get a summary of the deconstructor.
summarizeDeconstructor :: DeConInst -> ConInstSummary
summarizeDeconstructor (VarDeCon v _ _) = Just v
summarizeDeconstructor (TupleDeCon _)   = Nothing

deConTyArgs :: DeConInst -> [Type]
deConTyArgs (VarDeCon _ ts _) = ts
deConTyArgs (TupleDeCon ts)   = ts

deConExTypes :: DeConInst -> [Binder]
deConExTypes (VarDeCon _ _ ts) = ts
deConExTypes (TupleDeCon _)    = []

deConFieldKinds :: TypeEnv -> DeConInst -> [BaseKind]
deConFieldKinds tenv (VarDeCon op _ _) =
  let Just data_con = lookupDataCon op tenv
  in dataConFieldKinds tenv data_con

deConFieldKinds tenv (TupleDeCon types) =
  map (toBaseKind . typeKind tenv) types

isVarDeCon (VarDeCon {}) = True
isVarDeCon _             = False

instance HasSourcePos (BaseExp s) where
  getSourcePos e = getSourcePos (expInfo e)

data BaseFun s =
  Fun { funInfo       :: ExpInfo
      , funTyParams   :: [TyPat s]   -- ^ Type parameters
      , funParams     :: [Pat s]     -- ^ Object parameters
      , funReturn     :: Typ s       -- ^ Return type
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
mkWrapperDef v f = Def v (defaultDefAnn {defAnnInlinePhase = InlWrapper}) f

mapDefiniens :: (Fun s -> Fun s') -> Def s -> Def s'
{-# INLINE mapDefiniens #-}
mapDefiniens f def = def {definiens = f $ definiens def}

mapMDefiniens :: Monad m => (Fun s -> m (Fun s')) -> Def s -> m (Def s')
{-# INLINE mapMDefiniens #-}
mapMDefiniens f def = do fun <- f (definiens def)
                         return $ def {definiens = fun}

modifyDefAnnotation :: (DefAnn -> DefAnn) -> Def s -> Def s
modifyDefAnnotation f d = d {defAnnotation = f (defAnnotation d)}

defIsWrapper :: Def s -> Bool
defIsWrapper def = defAnnInlinePhase (defAnnotation def) == InlWrapper

-- | Annotations on a function definition
data DefAnn =
  DefAnn
  { -- | A tag controlling when inlining occurs
    defAnnInlinePhase :: !InliningAnnotation
    
    -- | A tag controlling how aggressively to inline.  If 'True', the
    --   function should be aggressively inlined.
  , defAnnInlineRequest :: !Bool
    
    -- | The uses of this definition,
    -- as determined by demand analysis
  , defAnnUses :: !Multiplicity
  }

defaultDefAnn :: DefAnn
defaultDefAnn = DefAnn InlNormal False ManyUnsafe

-- | An annotation controlling when a function may be inlined.
--
--   A function that's part of a recursive definition group cannot be inlined 
--   unless its annotation is 'InlWrapper'.
--
--   Functions that have rewrite rules should not be inlined during the first
--   few phases of compilation, so that rewrites can match the function name.
--   The annotations 'InlSequential' and 'InlFinal' control this kind of
--   inlining.
data InliningAnnotation =
    InlNormal                   -- ^ A normal function.
  | InlWrapper                  -- ^ A wrapper function; may be inlined even
                                --   in a recursive definition group.
  | InlSequential               -- ^ A parallelizable function whose definition
                                --   consists of sequential loops.  The
                                --   function should be inlined if it still
                                --   exists after parallelization.
  | InlFinal                    -- ^ A sequential loop function.  The function
                                --   should be inlined after rewriting
                                --   sequential loops.
    deriving (Eq, Enum, Show)

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

data Module s =
  Module
  { modName :: !ModuleName 

    -- | Definitions of functions that were imported from other modules.
    --   The optimizer may inline these definitions.
    --   Before representation inference, the imports should be empty.
  , modImports :: [Def s]
  , modDefs :: [DefGroup (Def s)]
  , modExports :: [Export s]
  }
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
  v `elem` [ pyonBuiltin The_Repr
           , pyonBuiltin The_TraversableDict
           , pyonBuiltin The_ShapeDict
           , pyonBuiltin The_IndexableDict
           , pyonBuiltin The_EqDict
           , pyonBuiltin The_OrdDict
           , pyonBuiltin The_AdditiveDict
           , pyonBuiltin The_MultiplicativeDict
           , pyonBuiltin The_FractionalDict
           , pyonBuiltin The_RemainderDict
           , pyonBuiltin The_FloatingDict
           , pyonBuiltin The_VectorDict
           ]

-- | Return True iff this is a dictionary data constructor.
isDictionaryDataCon :: Var -> Bool
isDictionaryDataCon v =
  v `elem` [ -- There's no data constructor for "Repr" in System F
             pyonBuiltin The_traversableDict
           , pyonBuiltin The_shapeDict
           , pyonBuiltin The_indexableDict
           , pyonBuiltin The_eqDict
           , pyonBuiltin The_ordDict
           , pyonBuiltin The_additiveDict
           , pyonBuiltin The_multiplicativeDict
           , pyonBuiltin The_fractionalDict
           , pyonBuiltin The_remainderDict
           , pyonBuiltin The_floatingDict
           , pyonBuiltin The_vectorDict
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
  v `elem` [ pyonBuiltin The_repr_int
           , pyonBuiltin The_repr_float
           , pyonBuiltin The_repr_bool
           , pyonBuiltin The_repr_list
           , pyonBuiltin The_repr_arr
           , pyonBuiltin The_repr_array0
           , pyonBuiltin The_repr_array1
           , pyonBuiltin The_repr_array2
           , pyonBuiltin The_repr_Complex
           , pyonBuiltin The_repr_PyonTuple2
           , pyonBuiltin The_repr_PyonTuple3
           , pyonBuiltin The_repr_PyonTuple4
           , pyonBuiltin The_repr_Box
           , pyonBuiltin The_repr_Stream
           ]
