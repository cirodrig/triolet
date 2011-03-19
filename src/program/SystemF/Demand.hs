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
import qualified Data.Set as Set
import Data.List
import Data.Maybe

import Common.Error
import Common.Identifier
import Type.Environment
import Type.Type
import Type.Rename

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
showMultiplicity ManySafe = "*"
showMultiplicity OnceUnsafe = "1+"
showMultiplicity ManyUnsafe = "*+"

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
    -- ^ Deconstructed by a case statement or read by 'copy'.
  | Decond !Var [Type] [(Var, Type)] [Specificity]
    -- ^ Deconstructed at a known constructor.
    --
    --   We save the type arguments and existential type parameters
    --   of the data constructor
    --   so that we can create a @case@ statement from this info.
    --
    --   Includes a list describing how each field is used.  There is one list
    --   member for each value field.
  | Loaded !Repr Type Specificity
    -- ^ Loaded at the given type and representation.  The representation
    --   is either 'Value' or 'Boxed'.
  | Unused            -- ^ Not used at all.  This is the bottom value.

instance Renameable Specificity where
  rename rn spc =
    case spc
    of Decond con ty_args ex_types spcs ->
         Decond con (rename rn ty_args) [(v, rename rn t) | (v, t) <- ex_types]
         (rename rn spcs)
       Loaded repr ty spc ->
         Loaded repr (rename rn ty) (rename rn spc)
       
       -- Other constructors don't mention variables
       _ -> spc

  freshen spc =
    case spc
    of Decond con ty_args ex_types spcs -> do
         -- Freshen the existential variables 
         new_evars <- mapM newClonedVar $ map fst ex_types
         let rn = renaming [(old_v, new_v)
                           | ((old_v, _), new_v) <- zip ex_types new_evars]
             ex_types' = [(new_v, k) | ((_, k), new_v) <- zip ex_types new_evars]
         return $ Decond con ty_args ex_types' (rename rn spcs)
       -- Other constructors don't bind new variables
       _ -> return spc

  freeVariables spc =
    case spc
    of Used -> Set.empty
       Inspected -> Set.empty
       Decond v tys ex_var_bindings spcs ->
         let ex_vars = map fst ex_var_bindings
             field_fvs = foldr Set.delete (freeVariables spcs) ex_vars
         in freeVariables tys `Set.union`
            freeVariables (map snd ex_var_bindings) `Set.union`
            field_fvs
       Loaded _ ty spc -> freeVariables ty `Set.union` freeVariables spc
       Unused -> Set.empty

-- | Construct a 'Specificity' for a value used as the reference parameter of 
--   a load.  The 'Repr' argument indicates whether the loaded data is boxed.
loadSpecificity :: Repr -> Type -> Specificity -> Specificity
loadSpecificity repr ty spc = Loaded repr ty spc

instance Dataflow Specificity where
  bottom = Unused

  joinPar Unused x = x
  joinPar x Unused = x
  joinPar (Decond decon1 t1 e1 specs1) (Decond decon2 _ _ specs2) =
    if decon1 == decon2
    then if length specs1 /= length specs2
         then mismatchedSpecificityDeconstructors
         else Decond decon1 t1 e1 $ zipWith joinPar specs1 specs2
    else Inspected
  joinPar (Loaded r1 t1 s1) (Loaded r2 _ s2) =
    if r1 /= r2
    then mismatchedSpecificityDeconstructors
    else Loaded r1 t1 (joinPar s1 s2)
  joinPar (Decond {}) (Loaded {}) = mismatchedSpecificityDeconstructors
  joinPar (Loaded {}) (Decond {}) = mismatchedSpecificityDeconstructors
  joinPar Inspected (Decond {}) = Inspected
  joinPar Inspected (Loaded {}) = Inspected
  joinPar (Decond {}) Inspected = Inspected
  joinPar (Loaded {}) Inspected = Inspected
  joinPar Inspected Inspected = Inspected
  joinPar Used _ = Used
  joinPar _ Used = Used
  
  joinSeq = joinPar

mismatchedSpecificityDeconstructors =
  internalError "Specificity.join: Mismatched deconstructors"

showSpecificity :: Specificity -> String
showSpecificity Unused = "0"
showSpecificity (Decond c tys ty_args spcs) =
  "D{" ++ showmv ++ concatMap showSpecificity spcs ++ "}"
  where
    showmv | null tys && null ty_args = show c ++ ":"
           | otherwise = "(" ++ show c ++ " ...):"
showSpecificity (Loaded r _ spc) = "L{" ++ showSpecificity spc ++ "}"
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
