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
import qualified Data.IntMap as IntMap
import qualified Data.Set as Set
import Data.List
import Data.Maybe

import Common.Error
import Common.Identifier
import SystemF.Syntax
import Type.Environment
import Type.Type
import Type.Rename
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

-- | A 'Dmd' can be renamed by renaming its specificity.
--   The 'multiplicity' field does not mention variable names.
instance Renameable Dmd where
  rename rn dmd = dmd {specificity = rename rn $ specificity dmd}
  freshen f dmd = do spc <- freshen f $ specificity dmd
                     return $ dmd {specificity = spc}
  freeVariables dmd = freeVariables $ specificity dmd

instance Substitutable Dmd where
  substitute s dmd = do
    spc <- substitute s $ specificity dmd
    return $ Dmd (multiplicity dmd) spc

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

instance Renameable Specificity where
  rename rn spc =
    case spc
    of Decond (MonoCon con ty_args ex_types) spcs ->
         let ty_args' = rename rn ty_args
         in renameBindings rn ex_types $ \rn' ex_types' ->
            let mono_con = MonoCon con ty_args' ex_types'
            in Decond mono_con (rename rn' spcs)
       
       Decond (MonoTuple types) spcs ->
         let types' = rename rn types
         in Decond (MonoTuple types') (rename rn spcs)

       Written spc -> Written (rename rn spc)

       Read (HeapMap xs) ->
         Read (HeapMap [((), rename rn val) | ((), val) <- xs])
       
       -- Other constructors don't mention variables
       _ -> spc

  freshen f spc =
    case spc
    of Decond (MonoCon con ty_args ex_types) spcs -> do
         -- Freshen the existential variables 
         new_evars <- mapM (newClonedVar . binderVar) ex_types
         let rn = renaming [(old_v, new_v)
                           | (old_v ::: _, new_v) <- zip ex_types new_evars]
             ex_types' = [new_v ::: k | (_ ::: k, new_v) <- zip ex_types new_evars]
         return $ Decond (MonoCon con ty_args ex_types') (rename rn spcs)

       -- Other constructors don't bind new variables
       Decond (MonoTuple _) _ -> return spc
       _ -> return spc

  freeVariables spc =
    case spc
    of Used -> Set.empty
       Inspected -> Set.empty
       Decond (MonoCon v tys ex_var_bindings) spcs ->
         let ex_vars = [v | v ::: _ <- ex_var_bindings]
             ex_kinds = [k | _ ::: k <- ex_var_bindings]
             field_fvs = foldr Set.delete (freeVariables spcs) ex_vars
         in freeVariables tys `Set.union`
            freeVariables ex_kinds `Set.union`
            field_fvs
       Decond (MonoTuple tys) spcs ->
         freeVariables tys `Set.union` freeVariables spcs
       Unused -> Set.empty

instance Substitutable Specificity where
  substitute s spc =
    case spc
    of Decond (MonoCon v tys ex_var_bindings) spcs -> do
         tys' <- mapM (substitute s) tys
         substituteBindings s ex_var_bindings $ \s' ex_var_bindings' -> do 
           spcs' <- mapM (substitute s') spcs
           return $ Decond (MonoCon v tys' ex_var_bindings') spcs'
       Decond (MonoTuple tys) spcs -> do
         tys' <- mapM (substitute s) tys
         spcs' <- mapM (substitute s) spcs
         return $ Decond (MonoTuple tys') spcs'
       
       Written spc' -> liftM Written $ substitute s spc'

       Read _ -> internalError "substitute: Not implemented"
       
       -- Other terms don't mention variables
       Used -> return spc
       Inspected -> return spc
       Unused -> return spc

instance Dataflow Specificity where
  bottom = Unused

  joinPar Unused x = x
  joinPar x Unused = x
  joinPar (Decond con1@(MonoCon decon1 _ _) specs1)
          (Decond (MonoCon decon2 _ _) specs2) =
    if decon1 == decon2
    then if length specs1 /= length specs2
         then mismatchedSpecificityDeconstructors
         else Decond con1 $ zipWith joinPar specs1 specs2
    else Inspected
  joinPar (Decond con1@(MonoTuple _) specs1)
          (Decond (MonoTuple _) specs2) =
    if length specs1 /= length specs2
    then mismatchedSpecificityDeconstructors
    else Decond con1 $ zipWith joinPar specs1 specs2
  joinPar (Decond _ _) (Decond _ _) =
    -- This case indicates a type mismatch
    internalError "Specificity.join: Type error detected"
  joinPar Inspected (Decond {}) = Inspected
  joinPar (Decond {}) Inspected = Inspected
  joinPar Inspected Inspected = Inspected
  joinPar Used _ = Used
  joinPar _ Used = Used
  
  joinSeq = joinPar

mismatchedSpecificityDeconstructors =
  internalError "Specificity.join: Mismatched deconstructors"

showSpecificity :: Specificity -> String
showSpecificity Unused = "0"
showSpecificity (Decond mono_con spcs) =
  "D{" ++ showmv ++ concatMap showSpecificity spcs ++ "}"
  where
    showmv =
      case mono_con
      of MonoCon c tys ty_args
           | null tys && null ty_args -> show c ++ ":"
           | otherwise -> "(" ++ show c ++  " ...):"
         MonoTuple _ -> ""
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

useVariables :: [Var] -> Dmd -> Dmds
useVariables vs dmd = IntMap.fromList [(fromIdent $ varID v, dmd) | v <- vs]

-- | Decide whether the arguments are equal, given that they describe
--   values of the same type.  This function is undefined for
--   specificity arguments of different types.
sameSpecificity :: Specificity -> Specificity -> Bool
sameSpecificity Used Used = True
sameSpecificity Inspected Inspected = True
sameSpecificity (Decond _ spcs1) (Decond _ spcs2) =
  and $ zipWith sameSpecificity spcs1 spcs2
sameSpecificity (Written s1) (Written s2) = sameSpecificity s1 s2

sameSpecificity (Read m1) (Read m2) = 
  let HeapMap assocs = outerJoinHeapMap check_pair m1 m2
  in all snd assocs
  where
    check_pair (Just x) (Just y) = sameSpecificity x y
    check_pair _ _ = False
  
sameSpecificity Unused Unused = True
sameSpecificity _ _ = False


-- | Given the specificity of a data constructor application, get the
--   specificity of its individual fields as they appear in a constructor
--   application
deconstructSpecificity :: TypeEnv -> Int -> Specificity -> [Specificity]
deconstructSpecificity tenv n_fields spc =
  case spc
  of Decond mono_con spcs
       | length spcs /= n_fields ->
         internalError "deconstructSpecficity: Wrong number of fields"
       | otherwise ->
           case mono_con
           of MonoCon con _ _ ->
                let Just dcon_type = lookupDataCon con tenv
                    field_kinds = dataConFieldKinds tenv dcon_type
                    from_field BareK spc = Written spc
                    from_field _     spc = spc
                in zipWith from_field field_kinds spcs
              MonoTuple _ ->
                -- Unboxed tuples have no bare fields
                spcs

     -- If the aggregate value is unused, all fields are unused
     Unused -> replicate n_fields Unused

     -- All other usages produce an unknown effect on fields 
     _ -> replicate n_fields Used

fromWrittenSpecificity spc =
  case spc
  of Written s -> s
     Unused -> Unused
     _ -> Used

fromReadSpecificity spc i =
  case spc
  of Read (HeapMap xs) -> fromMaybe Unused $ lookup i xs
     Unused -> Unused
     _ -> Used