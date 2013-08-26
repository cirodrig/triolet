{-| System F representation of Triolet code.

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

{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, UndecidableInstances, FlexibleContexts #-}
{-# OPTIONS_GHC -no-auto #-}
module SystemF.Syntax
    (-- * Demand information
     Dmd(..), unknownDmd,
     Multiplicity(..), Specificity(..),
     HeapMap(..),
     joinHeapMap, outerJoinHeapMap,
     CallDmd(..),
     nonCallDmd,
     
     -- * Representation of code
     Pat(..), TyPat(..), Exp(..), Alt(..), Fun(..),
     tyPatVar, tyPatKind,

     -- ** Annotations on expressions
     ExpInfo,
     Representation(..),
     defaultExpInfo,
     mkExpInfo,
     mkExpInfoWithRepresentation,
     getExpRepresentation,
     
     -- ** Literals
     Lit(..),
     literalType,
     
     -- ** Data types
     ConInst(..), ConInstSummary,
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
     Def(..), FDef,
     Ent(..), GDef,
     Constant(..),
     mkDef, mkWrapperDef, mkWorkerDef,
     mapDefiniens,
     mapMDefiniens,
     modifyDefAnnotation,
     defIsWrapper,
     DefAnn(..),
     defaultDefAnn,
     InliningAnnotation(..),
     InliningEagerness(..),
     DefGroup(..), defGroupMembers,
     
     -- ** Top-level constructs
     Export(..),
     Module(..),
     
     -- ** System F types
     SF,
     PatSF, ExpSF, AltSF, FunSF,

     -- * Utility functions
     isValueExp,
     unpackPolymorphicCall,
     isDictionaryTypeCon,
     --isDictionaryDataCon,
     isSingletonCon,
     --isReprCon
    )
where

import Control.DeepSeq
import Control.Monad
import Data.Typeable
import qualified Data.Foldable
import Data.Function
import qualified Data.List as List
import Data.Maybe
import Data.Monoid
import qualified Data.Traversable

import Common.ConPattern
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
--   Specificities form a lattice with the following ordering.
--
-- >            Used                 > _
-- >            Inspected            > {Copied, Decond _ _}
-- >  x > y ==> Decond c (u++[x]++v) > Decond c (u++[y]++v)
-- >            _                    > Unused
data Specificity =
    Used              -- ^ Used in an unknown way.  This is the top value.
  | Inspected
    -- ^ Deconstructed at an unknown constructor or copied by 'copy'.

  | Copied
    -- ^ Copied by 'copy'.

  | Decond !DeConInst [Dmd]
    -- ^ Deconstructed at a known constructor.
    --   Data with this specificity has type @T ts@ for
    --   some algebraic data constuctor or tuple type @T@.
    --
    --   We save the type arguments and existential type parameters
    --   of the data constructor
    --   so that we can create a @case@ statement from this info.
    --
    --   There is a demand for each data field.  The demand is the upper bounds
    --   of the demands at all use sites.

  | Called !Int !(Maybe Var) Specificity
    -- ^ Called with @N > 0@ arguments, then the return value used with the
    --   indicated specificity.  Construct this term with 'calledSpecificity'.
    --
    --   A variable is given for the last parameter of an initializer
    --   function.  The variable stands for
    --   the address to which the initializer function writes.
    --   If this is an iniitalizer function, the return specificity
    --   is a 'Read' term.
{-
  | Written !Var (HeapMap Specificity)
    -- ^ An initializer function @\x -> E@.  The variable stands for
    --   the address to which the initializer function writes.  Data
    --   with this specificity has type @Mut t -> Store@, for some
    --   bare type @t@.
    --
    --   The fields represent a lambda function taking a mutable reference
    -- This is similar to 'Decond'.
-}
  | Read (HeapMap Specificity)
    -- ^ Values are read out of memory and used at the given specificities.
    --   Data with this specificity has type @Store@.
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

-- | Function call demands on a variable.
--   Determines whether a function is definitely called.  If a function is
--   definitely called, then it is safe to hoist code from the function body
--   into the place where the function is defined.
--
--   Unlike 'Dmd', a definitely-called function is treated differently 
--   from a maybe-called function.
data CallDmd =
    -- | Variable may be unused
    CallUnused
    -- | Variable is definitely called with at least @N@ arguments.
    --   If variable may be used without being called, then @N = 0@.
    --   If variable is not a function, then @N@ must be zero.
  | CallUsed {-# UNPACK #-}!Int
  deriving(Eq)

-- | The call demand on a use of a variable other than a direct call
nonCallDmd :: CallDmd
nonCallDmd = CallUsed 0

-- | Call demands are ordered from least specific to most specific
instance Ord CallDmd where
  CallUnused `compare` CallUnused = EQ
  CallUnused `compare` CallUsed _ = LT
  CallUsed _ `compare` CallUnused = GT
  CallUsed m `compare` CallUsed n = m `compare` n

-------------------------------------------------------------------------------

-- | Literal values.
--
-- Integer and floating-point literal values have a explicit type.  The type
-- must mention only constants, not type variables.
data Lit =
    IntL !Integer !Type
  | FloatL {-# UNPACK #-} !Double !Type
  deriving(Typeable)

instance NFData Lit where
  rnf (IntL n t)   = rnf t
  rnf (FloatL d t) = rnf t

literalType :: Lit -> Type
literalType (IntL _ t) = t
literalType (FloatL _ t) = t

-- | Information common to all expressions.
data ExpInfo =
  ExpInfo
    SourcePos            -- Location where the expression originated
    !Representation      -- Representation dictionary for this expression.
                         -- This is only used during elaboration; afterward,
                         -- it is always 'Nothing'.

instance NFData ExpInfo where
  rnf (ExpInfo _ _) = () -- ignore fields

data Representation =
    NoRepresentation   -- ^ No representation information is available
  | BoxedRepresentation         -- ^ Data type is naturally boxed
  | ValueRepresentation         -- ^ Data type has kind 'val' and will not
                                --   be coerced
  | Representation ExpSF        -- ^ Explicitly given representation

defaultExpInfo :: ExpInfo
defaultExpInfo = ExpInfo noSourcePos NoRepresentation

mkExpInfo :: SourcePos -> ExpInfo
mkExpInfo pos = ExpInfo pos NoRepresentation

mkExpInfoWithRepresentation :: SourcePos -> Representation -> ExpInfo
mkExpInfoWithRepresentation pos r = ExpInfo pos r

-- | Look up the representation of an expression.  Representations
--   are annotated onto expressions during type inference, and are only 
--   available immediately after generating System F code.
getExpRepresentation :: ExpSF -> Representation
getExpRepresentation (ExpSF e) =
  case expInfo e
  of ExpInfo _ NoRepresentation -> internalError "getRepresentation"
     ExpInfo _ r -> r

instance HasSourcePos ExpInfo where
  getSourcePos (ExpInfo p _) = p

instance HasSourcePos ExpSF where
  getSourcePos (ExpSF e) = getSourcePos $ expInfo e

-- Data types used in representing code.  Data types are indexed by a
-- data format; different indices are used in different stages of the
-- compiler to customize the data structures.

data family Pat a               -- A pattern binding
data family Exp a               -- An expression
data family Alt a               -- A case alternative
data family Fun a               -- A function

instance Typeable1 Pat where
  typeOf1 x = mkTyConApp (mkTyCon "SystemF.Syntax.Pat") []
          
instance Typeable1 Exp where
  typeOf1 x = mkTyConApp (mkTyCon "SystemF.Syntax.Exp") []

instance Typeable1 Alt where
  typeOf1 x = mkTyConApp (mkTyCon "SystemF.Syntax.Alt") []

instance Typeable1 Fun where
  typeOf1 x = mkTyConApp (mkTyCon "SystemF.Syntax.Fun") []

-- | The System F code representation
data SF

type PatSF = Pat SF
type ExpSF = Exp SF
type AltSF = Alt SF
type FunSF = Fun SF

-- Pat SF is a data type
newtype instance Exp SF = ExpSF {fromExpSF :: BaseExp SF}
newtype instance Alt SF = AltSF {fromAltSF :: BaseAlt SF}
newtype instance Fun SF = FunSF {fromFunSF :: BaseFun SF}

-- | Patterns
data instance Pat SF = VarP Var Type

-- | Type-level patterns
newtype TyPat = TyPat Binder

instance NFData TyPat where rnf (TyPat b) = rnf b

tyPatVar :: TyPat -> Var
tyPatVar (TyPat (v ::: _)) = v

tyPatKind :: TyPat -> Type
tyPatKind (TyPat (_ ::: t)) = t

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
    -- | A data constructor application.  This term describes all the pieces 
    --   of data that go into building a new value.
    --
    --   The constructor instance determines how many other arguments to 
    --   expect.  Suppose we're constructing an object of type @T a b@.   
    --
    -- * If @T a b : box@, then a value of type
    --   @TypeObject t@ must be passed in 'expTypeObject'.  Otherwise,
    --   nothing should be passed for this argument.
    --
    -- * Size parameters should be passed as indicated by the
    --   'DataTypeLayout' associated with this data type.
    --
    -- * An argument should be passed for each field.  For value and boxed
    --   fields, the field value is passed; for bare fields, an initializer
    --   is passed.
  | ConE
    { expInfo      :: ExpInfo
    , expCon       :: !ConInst      -- ^ Instantiated data constructor
    , expSizeParams :: [Exp s]      -- ^ Run-time size info
    , expTyObject  :: Maybe (Exp s) -- ^ Type info for this constructor
    , expArgs      :: [Exp s]       -- ^ Field values or initializers
    }
    -- | Function application.
    --   Data constructor applications are represented by 'ConE' instead.
  | AppE
    { expInfo   :: ExpInfo
    , expOper   :: Exp s
    , expTyArgs :: [Type]
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
    , expDefs :: DefGroup (FDef s)
    , expBody :: Exp s
    }
    -- | Case analysis.
  | CaseE
    { expInfo :: ExpInfo
    , expScrutinee :: Exp s
    , expSizeParams :: [Exp s]  -- ^ Run-time size info
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
    , expArgType :: Type        -- ^ Type of body
    , expRetType :: Type        -- ^ Type of coerced result
    , expBody :: Exp s
    }
    -- | An explicit array expression.
    --   The array type is given explicitly because, if the array size is 0, 
    --   we can't infer its type.
    --
    --   This constructs an expression of type @arr n a@ for the given
    --   @a@, and @n@ determined by the number of array elements. 
  | ArrayE
    { expInfo :: ExpInfo
    , expType :: Type
    , expElements :: [Exp s]
    }

instance (NFData (Exp s), NFData (Alt s), NFData (Pat s), NFData (Fun s)) => NFData (BaseExp s) where
  rnf e = 
    case e
    of VarE i v        -> rnf i `seq` rnf v
       LitE i l        -> rnf i `seq` rnf l
       ConE i c p t a  -> rnf i `seq` rnf c `seq` rnf p `seq` rnf t `seq` rnf a
       AppE i o t a    -> rnf i `seq` rnf o `seq` rnf t `seq` rnf a
       LamE i f        -> rnf i `seq` rnf f
       LetE i b v e    -> rnf i `seq` rnf b `seq` rnf v `seq` rnf e
       LetfunE i g b   -> rnf i `seq` rnf (defGroupMembers g) `seq` rnf b
       CaseE i e p a   -> rnf i `seq` rnf e `seq` rnf p `seq` rnf a
       ExceptE i t     -> rnf i `seq` rnf t
       CoerceE i s t e -> rnf i `seq` rnf s `seq` rnf t `seq` rnf e
       ArrayE i t e    -> rnf i `seq` rnf t `seq` rnf e

data BaseAlt s =
  Alt { altCon :: !DeConInst
        -- | A pattern that binds a type object.  This is always 'Nothing' in  
        --   System F.  Only present when deconstructing boxed types in Core.
      , altTyObject :: !(Maybe (Pat s))
        -- | Patterns bound to each field
      , altParams :: [Pat s]
      , altBody :: Exp s
      }

instance (NFData (Exp s), NFData (Alt s), NFData (Pat s), NFData (Fun s)) => NFData (BaseAlt s) where
  rnf (Alt con tyob params body) = rnf con `seq` rnf tyob `seq` rnf params `seq` rnf body

getAltExTypes alt = deConExTypes $ altCon alt

-- | A summary of a data constructor.  For constructors of the same data type,
--   two summaries are equal iff they were created from the same constructor
--   or deconstrutor.
type ConInstSummary = Maybe Var

-- | A constructor instance appearing in a data constructor application
data ConInst =
    VarCon !Var [Type] [Type]
  | TupleCon [Type]

instance NFData ConInst where
  rnf (VarCon v ss ts) = rnf v `seq` rnf ss `seq` rnf ts
  rnf (TupleCon ts) = rnf ts

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

conFieldKinds :: EvalMonad m => ConInst -> m [BaseKind]
conFieldKinds (VarCon op _ _) = do
  Just data_con <- lookupDataCon op
  return $ dataConFieldKinds data_con

conFieldKinds (TupleCon types) =
  liftTypeEvalM $ mapM typeBaseKind types

conType :: EvalMonad m => ConInst -> m ([Type], Type)
conType (VarCon v ty_args ex_types) = do
  Just data_con <- lookupDataCon v
  instantiateDataConTypeWithExistentials data_con (ty_args ++ ex_types)

conType (TupleCon ty_args) = do
  kinds <- liftTypeEvalM $ mapM typeBaseKind ty_args
  return (ty_args, UTupleT kinds `typeApp` ty_args)

isVarCon (VarCon {}) = True
isVarCon _           = False

-- | A constructor instance appearing in a pattern match
data DeConInst =
    VarDeCon !Var [Type] [Binder]
  | TupleDeCon [Type]

instance NFData DeConInst where
  rnf (VarDeCon v ts bs) = rnf v `seq` rnf ts `seq` rnf bs
  rnf (TupleDeCon ts) = rnf ts

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

deConFieldKinds :: EvalMonad m => DeConInst -> m [BaseKind]
deConFieldKinds (VarDeCon op _ _) = do
  Just data_con <- lookupDataCon op
  return $ dataConFieldKinds data_con

deConFieldKinds (TupleDeCon types) =
  liftTypeEvalM $ mapM typeBaseKind types

isVarDeCon (VarDeCon {}) = True
isVarDeCon _             = False

instance HasSourcePos (BaseExp s) where
  getSourcePos e = getSourcePos (expInfo e)

data BaseFun s =
  Fun { funInfo       :: ExpInfo
      , funTyParams   :: [TyPat]     -- ^ Type parameters
      , funParams     :: [Pat s]     -- ^ Object parameters
      , funReturn     :: Type        -- ^ Return type
      , funBody       :: Exp s
      }

instance (NFData (Exp s), NFData (Alt s), NFData (Pat s), NFData (Fun s)) => NFData (BaseFun s) where
  rnf (Fun inf ty_params params ret body) =
    rnf inf `seq` rnf ty_params `seq` rnf params `seq` rnf ret `seq` rnf body

-- | A constant value.
--
--   A global constant value may be defined; it will be created before 
--   execution begins.  A constant value may contain only variable, literal,
--   and constructor terms.
data Constant s =
  Constant { constInfo :: ExpInfo
           , constType :: Type
           , constExp  :: Exp s
           }

-- | An entity that can be defined in a global definition group.
data Ent s = FunEnt !(Fun s) | DataEnt !(Constant s)

-- | A function definition
data Def t s =
  Def
  { definiendum :: Var
  , defAnnotation :: {-#UNPACK#-}!DefAnn
  , definiens :: t s
  }

instance NFData (t s) => NFData (Def t s) where
  rnf (Def v _ ens) = rnf v `seq` rnf ens

-- | A function definition
type FDef s = Def Fun s

-- | A global definition
type GDef s = Def Ent s

mkDef :: Var -> t s -> Def t s
mkDef v f = Def v defaultDefAnn f

-- | Create a wrapper function as part of a worker-wrapper transformation.
--
--   The wrapper function inherits some properties of the original 
--   function.  The wrapper function, not the worker,
--   is the one that code outside the module sees.
mkWrapperDef :: DefAnn -> Var -> t s -> Def t s
mkWrapperDef original_ann v f = let
  annotation =
    defaultDefAnn { defAnnInlinePhase = InlWrapper

                  -- The wrapper function is exported iff
                  -- the original function is exported
                  , defAnnExported = defAnnExported original_ann}
  in Def v annotation f

-- | Create a worker function as part of a worker-wrapper transformation.
--
--   The worker function inherits the inlining-related properties of the 
--   original function.
mkWorkerDef :: DefAnn -> Var -> t s -> Def t s
mkWorkerDef original_ann v f = let
  annotation =
    defaultDefAnn { -- Inherit inlining-related properties.
                    -- Can't inherit inlining patterns, since they may no 
                    -- longer be valid after this transformation. 
                    -- If there was an inlining pattern, then mark the
                    -- annotation 'InlineNever' to avoid runaway inlining.
                    defAnnInlinePhase = defAnnInlinePhase original_ann
                  , defAnnInlineRequest = if isNothing $ defAnnInlinePattern original_ann
                                          then defAnnInlineRequest original_ann
                                          else InlNever
                  , defAnnJoinPoint = defAnnJoinPoint original_ann
                  }
  in Def v annotation f

mapDefiniens :: (t s -> t s') -> Def t s -> Def t s'
{-# INLINE mapDefiniens #-}
mapDefiniens f def = def {definiens = f $ definiens def}

mapMDefiniens :: Monad m => (t s -> m (t s')) -> Def t s -> m (Def t s')
{-# INLINE mapMDefiniens #-}
mapMDefiniens f def = do fun <- f (definiens def)
                         return $ def {definiens = fun}

modifyDefAnnotation :: (DefAnn -> DefAnn) -> Def t s -> Def t s
modifyDefAnnotation f d = d {defAnnotation = f (defAnnotation d)}

defIsWrapper :: Def t s -> Bool
defIsWrapper def = defAnnInlinePhase (defAnnotation def) == InlWrapper

-- | Annotations on a function definition
data DefAnn =
  DefAnn
  { -- | A tag controlling when inlining occurs
    defAnnInlinePhase :: !InliningAnnotation
    
    -- | A tag controlling how aggressively to inline
  , defAnnInlineRequest :: !InliningEagerness

    -- | An optional tag restricting whether to inline based on parameter
    --   values at the callsite
  , defAnnInlinePattern :: !(Maybe ConPatterns)

    -- | True for functions that are very cheap to re-execute.
  , defAnnConlike :: !Bool

    -- | True for definitions that were created by the case-of-case
    --   transformation.  A lower inlining threshold is used for such
    --   definitions.
  , defAnnJoinPoint :: !Bool
    
    -- | Whether the function is visible to triolet code outside the
    --   current module.  This flag doesn't indicate whether the function
    --   is exported to other languages.
  , defAnnExported :: !Bool
    
    -- | The demand on this definition,
    -- as determined by demand analysis
  , defAnnUses :: !Dmd

    -- | Whether this function is definitely called.
    --   Defaults to 'False' for functions.
    --   Ignored for non-functions.
  , defAnnCalled :: !Bool
  }

defaultDefAnn :: DefAnn
defaultDefAnn =
  DefAnn InlNormal InlConservatively Nothing
         False False False (Dmd ManyUnsafe Used) False

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
  | InlPostfinal                -- ^ A sequential loop function.  The function
                                --   should be inlined after eliminating
                                --   redundant copying.
    deriving (Eq, Enum, Show)

-- | How eagerly to decide whether to inline
data InliningEagerness =
    InlNever
  | InlConservatively
  | InlAggressively
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
  , modImports :: [GDef s]
  , modDefs :: [DefGroup (GDef s)]
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
  Just (op, ts, xs)

unpackPolymorphicCall _ = Nothing

-- | Return True iff this is a dictionary type constructor.
isDictionaryTypeCon :: Var -> Bool
isDictionaryTypeCon v =
  v `elem` [ coreBuiltin The_Repr
           , coreBuiltin The_TraversableDict
           , coreBuiltin The_ShapeDict
           , coreBuiltin The_IndexableDict
           , coreBuiltin The_EqDict
           , coreBuiltin The_OrdDict
           , coreBuiltin The_AdditiveDict
           , coreBuiltin The_MultiplicativeDict
           , coreBuiltin The_FractionalDict
           , coreBuiltin The_RemainderDict
           , coreBuiltin The_FloatingDict
           , coreBuiltin The_VectorDict
           ]

-- | Return True if this is a singleton type constructor.
--   Return False if not a singleton type constructor, or if unknown.
--
--   Singleton types are data types that have exactly one value.
isSingletonCon :: Var -> Bool
isSingletonCon v = isDictionaryTypeCon v


{-
-- | Return True iff this is a dictionary data constructor.
isDictionaryDataCon :: Var -> Bool
isDictionaryDataCon v =
  v `elem` [ -- There's no data constructor for "Repr" in System F
             coreBuiltin The_traversableDict
           , coreBuiltin The_shapeDict
           , coreBuiltin The_indexableDict
           , coreBuiltin The_eqDict
           , coreBuiltin The_ordDict
           , coreBuiltin The_additiveDict
           , coreBuiltin The_multiplicativeDict
           , coreBuiltin The_fractionalDict
           , coreBuiltin The_remainderDict
           , coreBuiltin The_floatingDict
           , coreBuiltin The_vectorDict
           ]

-- | Return True iff this is a @Repr@ dictionary constructor.
isReprCon :: Var -> Bool
isReprCon v =
  v `elem` [ coreBuiltin The_repr_int
           , coreBuiltin The_repr_float
           , coreBuiltin The_repr_bool
           , coreBuiltin The_repr_list
           , coreBuiltin The_repr_append_list
           , coreBuiltin The_repr_arr
           , coreBuiltin The_repr_array0
           , coreBuiltin The_repr_array1
           , coreBuiltin The_repr_array2
           , coreBuiltin The_repr_array3
           , coreBuiltin The_repr_blist
           , coreBuiltin The_repr_barray1
           , coreBuiltin The_repr_barray2
           , coreBuiltin The_repr_barray3
           , coreBuiltin The_repr_Tuple2
           , coreBuiltin The_repr_Tuple3
           , coreBuiltin The_repr_Tuple4
           , coreBuiltin The_repr_Box
           , coreBuiltin The_repr_Stream
           , coreBuiltin The_repr_StuckRef
           , coreBuiltin The_repr_Ref
           ]
-}