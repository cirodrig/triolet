{-| Demand types.

Demand types represent an approximation of how a value is used.  Demand
types annotated onto variable bindings influence other transformations,
particularly inlining and dead code elimination.

The analysis is a combination of inlining information described in
Simon Peyton Jones and Simon Marlow, \"Secrets of the Glasgow Haskell
Compiler inliner\", and use information described in Simon Peyton Jones and
Will Partain, \"Measuring the Effectiveness of a Simple Strictness Analyzer.\"
We do not use strictness information as in the latter paper, but we do use
information about how a value is demanded.
-}

{-# LANGUAGE TypeSynonymInstances #-}
module SystemF.Demand where

import Control.Monad
import Data.Function
import qualified Data.IntMap as IntMap
import qualified Data.Set as Set
import Data.List
import Data.Maybe

import Common.Error
import Common.Identifier
import SystemF.Syntax
import {-# SOURCE #-} SystemF.Rename
import Type.Environment
import qualified Type.Rename as Rename
import Type.Type
import Type.Eval

-------------------------------------------------------------------------------
-- The dataflow domain

class Dataflow a where
  -- | The least element.  This is the most specific possible value,
  --   and the identity element of 'joinPar' and 'joinSeq'.
  bottom :: a

  -- | Join two elements derived from mutually exclusive code paths
  joinPar :: a -> a -> a
  -- | Join two elements derived from non-exclusive code paths.
  --
  --   For any a and b, @joinPar a b <= joinSeq a b@.
  joinSeq :: a -> a -> a

joinPars :: Dataflow a => [a] -> a
joinPars xs = foldl' joinPar bottom xs

joinSeqs :: Dataflow a => [a] -> a
joinSeqs xs = foldl' joinSeq bottom xs

instance Dataflow a => Dataflow (IntMap.IntMap a) where
  bottom = IntMap.empty
  joinPar m1 m2 = IntMap.unionWith joinPar m1 m2
  joinSeq m1 m2 = IntMap.unionWith joinSeq m1 m2

showDmd (Dmd m s) =
  "[" ++ showMultiplicity m ++ ":" ++ showSpecificity s ++ "]"

instance Dataflow Dmd where
  bottom = Dmd bottom bottom
  joinPar (Dmd m1 s1) (Dmd m2 s2) = Dmd (joinPar m1 m2) (joinPar s1 s2)
  joinSeq (Dmd m1 s1) (Dmd m2 s2) = Dmd (joinSeq m1 m2) (joinSeq s1 s2)

showMultiplicity :: Multiplicity -> String
showMultiplicity Dead = "0"
showMultiplicity OnceSafe = "1"
showMultiplicity ManySafe = "*"
showMultiplicity OnceUnsafe = "1+"
showMultiplicity ManyUnsafe = "*+"

-- | Determine whether the 'Multiplicity' indicates that the value is
--   used at most once when it is executed.
safeMultiplicity :: Multiplicity -> Bool
safeMultiplicity Dead = True
safeMultiplicity OnceSafe = True
safeMultiplicity ManySafe = True
safeMultiplicity _ = False

-- | Determine whether the 'Multiplicity' indicates that the value is
--   mentioned in exactly one place.
singleMultiplicity :: Multiplicity -> Bool
singleMultiplicity OnceSafe = True
singleMultiplicity OnceUnsafe = True
singleMultiplicity _ = False

instance Dataflow Multiplicity where
  bottom = Dead

  joinPar Dead x = x
  joinPar x Dead = x
  joinPar x y = if safeMultiplicity x && safeMultiplicity y
                then ManySafe
                else ManyUnsafe

  joinSeq Dead x = x
  joinSeq x Dead = x
  joinSeq _ _    = ManyUnsafe

-- | Compare two specificities based /only/ on their head constructor. 
--   The result is an approximation to the partial ordering.
--   If @x `ltSpecificityConstructor` y@ is 'True', then @x < y@ in the
--   partial ordering.  The converse is not necessarily true.
{-# INLINE ltSpecificityConstructor #-}
ltSpecificityConstructor :: Specificity -> Specificity -> Bool
ltSpecificityConstructor Used       _         = False
ltSpecificityConstructor _          Used      = True 
ltSpecificityConstructor Copied     Inspected = True
ltSpecificityConstructor (Decond{}) Inspected = True
ltSpecificityConstructor _          Unused    = False
ltSpecificityConstructor Unused     _         = True

-- Remaining cases are 'Written', 'Read', which are bounded by the
-- top and bottom of the lattice
ltSpecificityConstructor _          _         = False

instance Dataflow Specificity where
  bottom = Unused

  -- If speicifities are equal, the result is unchanged
  joinPar Used Used = Used
  joinPar Unused Unused = Unused
  joinPar Copied Copied = Copied
  joinPar Inspected Inspected = Inspected

  -- If one constructor is less than another, then take the greater of the two
  joinPar x y | x `ltSpecificityConstructor` y = y
              | y `ltSpecificityConstructor` x = x

  -- The remaining cases are nontrivial.
  -- Constructors are equal or incomparable.
  joinPar (Decond con1@(VarDeCon decon1 _ _) specs1)
          (Decond (VarDeCon decon2 _ _) specs2) =
    if decon1 == decon2
    then if length specs1 /= length specs2
         then mismatchedSpecificityDeconstructors
         else Decond con1 $ zipWith joinPar specs1 specs2
    else Inspected
  joinPar (Decond con1@(TupleDeCon _) specs1)
          (Decond (TupleDeCon _) specs2) =
    if length specs1 /= length specs2
    then mismatchedSpecificityDeconstructors
    else Decond con1 $ zipWith joinPar specs1 specs2
  joinPar (Decond _ _) (Decond _ _) =
    -- This case indicates a type mismatch
    internalError "Specificity.join: Type error detected"

  joinPar Copied (Decond {}) = Inspected
  joinPar (Decond {}) Copied = Inspected

  joinPar (Written v1 h1) (Written v2 h2) =
    -- Unify variables by renaming v2 to v1
    let h2' = renameHeapMap (Rename.singleton v2 v1) h2
        -- Join both maps; absent entries are 'Unused'
        h' = outerJoinHeapMap (joinPar `on` fromMaybe Unused) h1 h2'
    in Written v1 h'
  joinPar (Written {}) _ = Inspected
  joinPar _ (Written {}) = Inspected

  joinPar (Read h1) (Read h2) =
    -- Join both maps; absent entries are 'Unused'
    Read $ outerJoinHeapMap (joinPar `on` fromMaybe Unused) h1 h2

  joinPar (Read _) _ = Inspected
  joinPar _ (Read _) = Inspected

  joinPar _ _ = internalError "Specificity.join: Not implemented for these values"
  
  joinSeq = joinPar

mismatchedSpecificityDeconstructors =
  internalError "Specificity.join: Mismatched deconstructors"

showSpecificity :: Specificity -> String
showSpecificity Unused = "0"
showSpecificity (Decond mono_con spcs) =
  "D{" ++ showmv ++ concatMap showDmd spcs ++ "}"
  where
    showmv =
      case mono_con
      of VarDeCon c tys ty_args
           | null tys && null ty_args -> show c ++ ":"
           | otherwise -> "(" ++ show c ++  " ...):"
         TupleDeCon _ -> ""
showSpecificity Copied = "C"
showSpecificity Inspected = "I"
showSpecificity Used = "U"

-- | Demand information for a set of variables
type Dmds = IntMap.IntMap Dmd

-- | Get the demand on a variable
lookupDmd :: Var -> Dmds -> Dmd
lookupDmd v m = fromMaybe bottom $ IntMap.lookup (fromIdent $ varID v) m

-- | Augment a demand's multiplicity by the given multiplicity.
--
--   This transformation merges two sources of uncertainty about how 
--   often a data structure field is used.  A data structure may be
--   used once or many times, and after being deconstructed, its field
--   may be deconstructed once or many times.
--   If the data structure is used many times /or/ the field is used
--   many times, then the multiplicity should be @Unsafe@.
multiplyDmd :: Multiplicity -> Dmd -> Dmd
multiplyDmd m1 (Dmd m2 s) = Dmd (multiplyMultiplicity m1 m2) s

multiplyMultiplicity Dead _ = Dead

-- The following rule isn't used because, even though the value's not used, 
-- we may be unable to remove it syntactically from the program.
-- multiplyMultiplicity _ Dead = Dead

multiplyMultiplicity m1 m2 
  | safe && single = OnceSafe
  | safe           = ManySafe
  | single         = OnceUnsafe
  | otherwise      = ManyUnsafe
  where 
    safe = safeMultiplicity m1 && safeMultiplicity m2
    single = singleMultiplicity m1 && singleMultiplicity m2

-- | Transform the demand information of values that appear under a lambda.
--
--   Safe multiplicity becomes unsafe, beca
lambdaAbstracted :: Dmds -> Dmds
lambdaAbstracted = IntMap.map lambda_abstract
  where
    lambda_abstract dmd = dmd {multiplicity = weaken $ multiplicity dmd}
    
    weaken Dead       = Dead
    weaken OnceSafe   = OnceUnsafe
    weaken ManySafe   = ManyUnsafe
    weaken OnceUnsafe = OnceUnsafe
    weaken ManyUnsafe = ManyUnsafe

-- | Transform the demand information on a coerced value.
--   After coercion, the value's contents no longer match its type, so we
--   force the value to be either 'Used' or 'Unused'.
coerced :: Dmd -> Dmd
coerced (Dmd m Unused) = Dmd m Unused
coerced (Dmd m _)      = Dmd m Used

-- | Transform the demand information of values that appear in code that will be
--   replicated.
--
--   Since many copies of the code will be created, one use becomes many.
replicatedCode :: Dmds -> Dmds
replicatedCode = IntMap.map replicated
  where
    replicated dmd = dmd {multiplicity = weaken $ multiplicity dmd}
    
    weaken Dead = Dead
    weaken OnceSafe = ManySafe
    weaken ManySafe = ManySafe
    weaken OnceUnsafe = ManyUnsafe
    weaken ManyUnsafe = ManyUnsafe

useVariable :: Var -> Dmd -> Dmds
useVariable v dmd = IntMap.singleton (fromIdent $ varID v) dmd

useVariables :: [Var] -> Dmd -> Dmds
useVariables vs dmd = IntMap.fromList [(fromIdent $ varID v, dmd) | v <- vs]

{-
-- | Decide whether the arguments are equal, given that they describe
--   values of the same type.  This function is undefined for
--   specificity arguments of different types.
sameSpecificity :: Specificity -> Specificity -> Bool
sameSpecificity Used Used = True
sameSpecificity Inspected Inspected = True
sameSpecificity (Decond _ spcs1) (Decond _ spcs2) =
  and $ zipWith sameSpecificity spcs1 spcs2
sameSpecificity (Written x s1) (Written y s2) = sameSpecificity s1 s2
sameSpecificity Copied Copied = True

sameSpecificity (Read m1) (Read m2) = 
  let HeapMap assocs = outerJoinHeapMap check_pair m1 m2
  in all snd assocs
  where
    check_pair (Just x) (Just y) = sameSpecificity x y
    check_pair _ _ = False
  
sameSpecificity Unused Unused = True
sameSpecificity _ _ = False
-}

-- | Given the specificity of a piece of data, create the
--   specificity of the initializer that created that data.
initializerSpecificity :: EvalMonad m => Specificity -> m Specificity
initializerSpecificity spc = do
  v <- newAnonymousVar ObjectLevel
  return $ Written v (HeapMap [(v, spc)])

dataFieldDmd m1 BareK (Dmd m2 s) = do s' <- initializerSpecificity s
                                      return $ multiplyDmd m1 $ Dmd m2 s'
dataFieldDmd m1 _     d          = return $ multiplyDmd m1 d

-- | Given the demand on a data constructor application, get the demands on
--   its individual fields.
--
-- Multiplicity: If the expression were inlined into all its use sites,
-- by how much would the field be replicated?
--
-- Specificity: How will the field be used?
deconstructSpecificity :: EvalMonad m => Int -> Dmd -> m [Dmd]
deconstructSpecificity n_fields (Dmd m spc) =
  case spc
  of Decond mono_con spcs
       | length spcs /= n_fields ->
           internalError "deconstructSpecficity: Wrong number of fields"
       | otherwise -> do
           -- Convert specificity info attached to initializers
           field_kinds <- deConFieldKinds mono_con
           zipWithM (dataFieldDmd m) field_kinds spcs

     -- If the aggregate value is unused, all fields are unused.
     -- However, don't mark the fields as dead because they're still used
     -- in the expression.
     Unused -> let m' = case m of {Dead -> OnceSafe; _ -> m}
               in return $ replicate n_fields (Dmd m' Unused)

     -- All other usages produce an unknown effect on fields 
     _ -> return $ replicate n_fields unknownDmd

initializerResultSpecificity target_var spc =
  case spc
  of Written target_binder s ->
       Rename.rename (Rename.singleton target_binder target_var) $ Read s
     Unused -> Unused
     _ -> Used

heapItemSpecificity index spc =
  case spc
  of Read (HeapMap xs) -> fromMaybe Unused $ lookup index xs
     Unused -> Unused
     _ -> Used