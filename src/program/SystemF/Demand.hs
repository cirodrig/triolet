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

-- | Dataflow semilattices extend to products in the obvious way
instance (Dataflow a, Dataflow b) => Dataflow (a, b) where
  bottom = (bottom, bottom)
  joinPar (u, x) (v, y) = (joinPar u v, joinPar x y)
  joinSeq (u, x) (v, y) = (joinSeq u v, joinSeq x y)

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

-- Remaining cases are 'Called', 'Read', which are bounded by the
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

  joinPar (Called n1 mv1 h1) (Called n2 mv2 h2)
    | n1 /= n2 = Called (min n1 n2) Nothing Used
    | otherwise =
        case (mv1, mv2)
        of (Just v1, Just v2) ->
             -- Unify variables by renaming v2 to v1
             let h2' = Rename.rename (Rename.singleton v2 v1) h2
                 h' = joinPar h1 h2'
             in Called n1 (Just v1) h'
           (Nothing, Nothing) ->
             Called n1 Nothing (joinPar h1 h2)
           _ ->
             -- Cannot represent return specificity precisely
             Called n1 Nothing Used

  joinPar (Called {}) _ = Inspected
  joinPar _ (Called {}) = Inspected

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

instance Dataflow CallDmd where
  bottom = CallUnused

  -- On alternative paths, the least specific demand takes precedence,
  -- except don't mark it 'unused' if there's a chance that it's used.
  joinPar CallUnused CallUnused = CallUnused
  joinPar x y                   = min nonCallDmd (min x y)

  -- On a single path, the most specific demand takes precedence
  joinSeq x y = max x y

-- | Demand analysis associates a 'Dmd' and a 'CallDmd' with each variable
--   and each expression
type VarDmd = (Dmd, CallDmd)

-- | Demand information for a set of variables
type Dmds = IntMap.IntMap VarDmd

-- | Get the demand on a variable
lookupDmd :: Var -> Dmds -> VarDmd
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
--   If the function is used exactly once (multiplicity is 'OnceSafe')
--   and it's definitely called, then demand information is unchanged.
--
--   If the function is definitely called, then demand information is
--   unchanged.
--
--   Otherwise, safe multiplicity becomes unsafe and
--   definitely-called becomes maybe-called.
lambdaAbstracted :: Multiplicity -- ^ Multiplicity at which function is used
                 -> Bool         -- ^ Whether function is definitely called
                 -> Dmds
                 -> Dmds
lambdaAbstracted call_mult called dmds
  | call_mult == OnceSafe && called = dmds
  | called                          = IntMap.map called_lambda dmds
  | otherwise                       = IntMap.map unknown_lambda dmds
  where
    -- The lambda function is called at least once.
    -- Multiplicities become unsafe because it may be called many times.
    -- Call demands are unchanged.
    called_lambda (dmd, cd) =
      (dmd {multiplicity = weaken $ multiplicity dmd}, cd)
    
    -- The lambda function is called an unknown number of times.
    -- Multiplicities become unsafe because it may be called many times.
    -- Call demands become 'used' because function calls in the function body
    -- may never be executed.
    unknown_lambda (dmd, cd) =
      (dmd {multiplicity = weaken $ multiplicity dmd}, weaken_c cd)

    weaken Dead       = Dead
    weaken OnceSafe   = OnceUnsafe
    weaken ManySafe   = ManyUnsafe
    weaken OnceUnsafe = OnceUnsafe
    weaken ManyUnsafe = ManyUnsafe

    weaken_c CallUnused   = CallUnused
    weaken_c (CallUsed _) = nonCallDmd

-- | Transform the demand information on a coerced value.
--   After coercion, the value's contents no longer match its type, so we
--   force the value to be either 'Used' or 'Unused'.
coerced :: VarDmd -> VarDmd
coerced (Dmd m Unused, _) = (Dmd m Unused, CallUnused)
coerced (Dmd m _, _)      = (Dmd m Used, nonCallDmd)

-- | Transform the demand information of values that appear in code
--   that will be replicated zero or more times.
--
--   Since many copies of the code will be created, one use becomes many.
replicatedCode :: Dmds -> Dmds
replicatedCode = IntMap.map replicated
  where
    replicated (dmd, cd) =
      (dmd {multiplicity = weaken $ multiplicity dmd}, weaken_c cd)
    
    weaken Dead = Dead
    weaken OnceSafe = ManySafe
    weaken ManySafe = ManySafe
    weaken OnceUnsafe = ManyUnsafe
    weaken ManyUnsafe = ManyUnsafe

    weaken_c CallUnused   = CallUnused
    weaken_c (CallUsed _) = nonCallDmd

useVariable :: Var -> VarDmd -> Dmds
useVariable v dmd = IntMap.singleton (fromIdent $ varID v) dmd

useVariables :: [Var] -> VarDmd -> Dmds
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

-- | Construct the specificity of a function
calledSpecificity n Nothing  (Called n' mv spc) = Called (n + n') mv spc
calledSpecificity n Nothing  spc = spc
calledSpecificity 0 (Just _) spc = internalError "calledSpecificity"
calledSpecificity n (Just v) spc = Called n (Just v) spc

-- | Given the specificity of a piece of data, create the
--   specificity of the initializer that created that data.
initializerSpecificity :: EvalMonad m => Specificity -> m Specificity
initializerSpecificity spc = do
  v <- newAnonymousVar ObjectLevel
  return $ Called 1 (Just v) (Read (HeapMap [(v, spc)]))

dataFieldDmd m1 BareK (Dmd m2 s) = do
  -- A definitely-called initializer function
  s' <- initializerSpecificity s
  return (multiplyDmd m1 $ Dmd m2 s', CallUsed 1)

dataFieldDmd m1 _ d =
  return (multiplyDmd m1 d, nonCallDmd)

-- | Given the demand on a data constructor application, get the demands on
--   its individual fields.
--
-- Multiplicity: If the expression were inlined into all its use sites,
-- by how much would the field be replicated?
--
-- Specificity: How will the field be used?
deconstructSpecificity :: EvalMonad m => ConInst -> Int -> Dmd -> m [VarDmd]
deconstructSpecificity con_inst n_fields (Dmd m spc) =
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
               in return $ replicate n_fields (Dmd m' Unused, CallUnused)

     -- All other usages produce an unknown effect on fields, and
     -- demand values of initializers.
     _ -> case con_inst
          of VarCon con _ _ -> do
               -- Find initializers
               Just data_con <- lookupDataCon con
               let field_demands = [kind_demand k
                                   | (_, k) <- dataConFields data_con]
               return field_demands
             TupleCon xs ->
               return $ replicate (length xs) unknownVarDmd
  where
    kind_demand BareK = (unknownDmd, CallUsed 1)
    kind_demand _     = unknownVarDmd

unknownVarDmd = (unknownDmd, nonCallDmd)

-- | Get the demand on a function at the site of a function call, given
--   the number of arguments and the demand on its result
calleeDmd :: Int -> VarDmd -> VarDmd
calleeDmd 0 d = d               -- No change if no arguments are applied
calleeDmd n_args (Dmd m result_s, result_call_dmd) =
  let call_s =
        calledSpecificity n_args Nothing result_s
      call_dmd =
        -- Add the number of arguments applied here to the number of arguments 
        -- applied later
        let result_args = case result_call_dmd
                          of CallUsed n -> n
                             CallUnused -> 0
        in CallUsed (n_args + result_args)
  in (Dmd m call_s, call_dmd)

-- | Check whether the function is certain to be passed at least N
--   arguments
isCalledWithArity :: CallDmd -> Int -> Bool
CallUnused `isCalledWithArity` _ = False
CallUsed m `isCalledWithArity` n = m >= n

-- | Get the demand on a function's return type, given the demand on the
--   function.
--
-- Multiplicity: If the function were inlined into all its use sites,
-- by how much would the return value be replicated?
--
-- Specificity: How will the return value be used?
returnTypeDmd :: Int -> Maybe Var -> VarDmd -> VarDmd
returnTypeDmd n_params m_target_var (Dmd m s, call_dmd) = let
  -- Is this function definitely called?
  call_dmd' =
    case call_dmd
    of CallUnused -> CallUnused
       CallUsed n -> CallUsed (if n > n_params then n - n_params else 0)

  s' = returnTypeSpecificity n_params m_target_var s
  in (Dmd ManyUnsafe s', call_dmd')

-- | Get the specificity of a function's return type, given the function's
--   specificity
returnTypeSpecificity :: Int -> Maybe Var -> Specificity -> Specificity
returnTypeSpecificity n_params m_target_var spc =
  case spc
  of Called n_demanded_params m_binder s
       | n_params == n_demanded_params -> 
           case (m_binder, m_target_var)
           of (Just target_binder, Just v) ->
                Rename.rename (Rename.singleton target_binder v) s
              (Nothing, _) ->
                s
              _ -> Used         -- Cannot rename appropriately

       | n_params < n_demanded_params ->
           Called (n_demanded_params - n_params) m_binder s

       | otherwise -> Used
     Unused -> Unused
     _ -> Used

initializerResultSpecificity target_var spc =
  case spc
  of Called 1 (Just target_binder) s ->
       Rename.rename (Rename.singleton target_binder target_var) s
     Unused -> Unused
     _ -> Used

heapItemSpecificity index spc =
  case spc
  of Read (HeapMap xs) -> fromMaybe Unused $ lookup index xs
     Unused -> Unused
     _ -> Used
