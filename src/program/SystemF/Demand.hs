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

import qualified Data.IntMap as IntMap
import Data.List
import Data.Maybe

import Common.Error
import Common.Identifier
import Type.Environment
import Type.Type

-------------------------------------------------------------------------------
-- The dataflow domain

class Dataflow a where
  -- | The least element
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

-- | Variables are assigned a demand in 'Dmd'
data Dmd = Dmd { multiplicity :: !Multiplicity
               , specificity :: !Specificity
               }

-- | The default demand value, 
--   assigned to variables before demand analysis has run.
unknownDmd :: Dmd
unknownDmd = Dmd ManyUnsafe Used

showDmd (Dmd m s) =
  "[" ++ showMultiplicity m ++ ":" ++ showSpecificity s ++ "]"

instance Dataflow Dmd where
  bottom = Dmd bottom bottom
  joinPar (Dmd m1 s1) (Dmd m2 s2) = Dmd (joinPar m1 m2) (joinPar s1 s2)
  joinSeq (Dmd m1 s1) (Dmd m2 s2) = Dmd (joinSeq m1 m2) (joinSeq s1 s2)

-- | How many times a variable is used.
data Multiplicity =
    Dead            -- ^ Not used
  | OnceSafe        -- ^ Used once, not under lambda
  | ManySafe        -- ^ Used in multiple mutually-exclusive locations
  | OnceUnsafe      -- ^ Used once under a lambda
  | ManyUnsafe      -- ^ Used many times
  deriving(Eq)

showMultiplicity :: Multiplicity -> String
showMultiplicity Dead = "0"
showMultiplicity OnceSafe = "1"
showMultiplicity ManySafe = "∞"
showMultiplicity OnceUnsafe = "1+"
showMultiplicity ManyUnsafe = "∞+"

safeMultiplicity :: Multiplicity -> Bool
safeMultiplicity Dead = True
safeMultiplicity OnceSafe = True
safeMultiplicity ManySafe = True
safeMultiplicity _ = False

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

-- | What part of a value is used.
data Specificity =
    Used              -- ^ Used in an unknown way.  This is the top value.
  | Inspected
    -- ^ Deconstructed by a case statement or read by 'copy'
  | Decond !(Maybe Var) [Specificity]
    -- ^ Deconstructed at a known constructor or read by 'load'.
    --   Includes a list describing how each field is used.  There is one list
    --   member for each value field; none for type fields.
  | Unused            -- ^ Not used at all.  This is the bottom value.

instance Dataflow Specificity where
  bottom = Unused

  joinPar Unused x = x
  joinPar x Unused = x
  joinPar (Decond decon1 specs1) (Decond decon2 specs2) =
    if decon1 == decon2
    then if length specs1 /= length specs2
         then internalError "Specificity.join: Mismatched deconstructors"
         else Decond decon1 $ zipWith joinPar specs1 specs2
    else Inspected
  joinPar Inspected (Decond {}) = Inspected
  joinPar (Decond {}) Inspected = Inspected
  joinPar Inspected Inspected = Inspected
  joinPar Used _ = Used
  joinPar _ Used = Used
  
  joinSeq = joinPar

showSpecificity :: Specificity -> String
showSpecificity Unused = "0"
showSpecificity (Decond mv spcs) =
  "D{" ++ showmv mv ++ concatMap showSpecificity spcs ++ "}"
  where
    showmv Nothing = ""
    showmv (Just c) = show c ++ ":"
showSpecificity Inspected = "I"
showSpecificity Used = "U"

-- | Demand information for a set of variables
type Dmds = IntMap.IntMap Dmd

-- | Get the demand on a variable
lookupDmd :: Var -> Dmds -> Dmd
lookupDmd v m = fromMaybe bottom $ IntMap.lookup (fromIdent $ varID v) m

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

useVariable :: Var -> Dmd -> Dmds
useVariable v dmd = IntMap.singleton (fromIdent $ varID v) dmd
