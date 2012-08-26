{-| Layout computation.

This module provides for computation of information that follows the structure
of a data type's layout.
-}

{-# LANGUAGE FlexibleInstances #-}
module SystemF.Datatypes.ComputeLayout
       (Entry, Compute,
        runComputation,
        runSubcomputation,
        lookupOrCreatePremise,
        Algorithm(..),
        computeIntValue,
        computeFieldLayout,
        computeObjectLayout,
        computeAlgObjectLayout)
where

import Control.Monad
import Control.Monad.ST
import Control.Monad.Trans
import qualified Data.Set as Set
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import Common.Supply
import Common.MonadLogic
import Builtins.Builtins
import Type.Type
import Type.Environment
import Type.Compare
import Type.Rename(Renameable(..))
import Type.Substitute(freshen)
import Type.Eval


type Entry a = (BaseKind, Type, a)

-- | State of a layout computation.
--
--   Parameter 'ev' is evidence for a piece of information.
--   Parameter 'deriv' is a derivation of a piece of evidence.
data ComputeState ev deriv =
  ComputeState
  { -- | Parameters to the computation
    premises :: [Entry ev]

    -- | A sequence of layout derivations.
    --   Derivations earlier in the list may depend on derivations later
    --   in the list.
  , derivations :: [Entry (ev, deriv)]
  }

data ComputeContext =
  Ctx
  { ctxVarSupply    :: {-#UNPACK#-} !(IdentSupply Var)
  , ctxTypeEnv      :: TypeEnv

    -- | Type variables that cannot be mentioned in a premise.
  , ctxInaccessible :: [Var]
  }

-- | A layout computation.
newtype Compute ev deriv a =
  Compute (ComputeContext ->
           ComputeState ev deriv ->
           IO (ComputeState ev deriv, a))

instance Monad (Compute ev deriv) where
  return x = Compute $ \_ s -> return (s, x)
  m >>= k = Compute $ \ctx s -> do
    let Compute f = m
    (s', x) <- f ctx s
    let Compute g = k x
    g ctx s'

instance TypeEnvMonad (Compute ev deriv) where
  type TypeFunctionInfo (Compute ev deriv) = TypeFunction
  getTypeEnv = Compute (\ctx s -> return (s, ctxTypeEnv ctx))
  askTypeEnv f = Compute (\ctx s -> return (s, f $ ctxTypeEnv ctx))
  assumeWithProperties v t b (Compute f) = Compute $ \ctx s ->
    let ctx' = ctx {ctxTypeEnv =
                       insertTypeWithProperties v t b $ ctxTypeEnv ctx}
    in f ctx' s

instance MonadIO (Compute ev deriv) where
  liftIO m = Compute $ \_ s -> do
    x <- m
    return (s, x)

instance Supplies (Compute ev deriv) (Ident Var) where
  fresh = Compute $ \ctx s -> do
    x <- supplyValue (ctxVarSupply ctx)
    return (s, x)

  supplyToST f = Compute $ \ctx s -> do
    x <- liftIO $ stToIO (f (unsafeIOToST $ supplyValue (ctxVarSupply ctx)))
    return (s, x)

instance EvalMonad (Compute ev deriv) where
  liftTypeEvalM m = Compute $ \ctx s -> do
    x <- runTypeEvalM m (ctxVarSupply ctx) (ctxTypeEnv ctx)
    return (s, x)

getState :: Compute ev deriv (ComputeState ev deriv)
getState = Compute $ \_ s -> return (s, s)

getInaccessible :: Compute e d [Var]
getInaccessible = Compute $ \ctx s -> return (s, ctxInaccessible ctx)

modifyState :: (ComputeState e d -> ComputeState e d) -> Compute e d ()
modifyState f = Compute $ \_ s -> return (f s, ())

-- | Add a type variable binding to the type environment and make it
--   inaccessible
assumeInaccessible :: Binder -> Compute e d a -> Compute e d a
assumeInaccessible (v ::: k) (Compute f) =
  assume v k $ Compute $ \ctx s -> f (add_v ctx) s
  where
    add_v ctx = ctx {ctxInaccessible = v : ctxInaccessible ctx}

assumeInaccessibleList :: [Binder] -> Compute e d a -> Compute e d a
assumeInaccessibleList bs m = foldr assumeInaccessible m bs

-- | The result of searching the environment for a layout for the given type
data SearchResult a =
    Found a                     -- ^ Matching entry was found
  | NotFound                    -- ^ Matching entry was not found

-- | Search for a premise or derivation matching the given type
searchEnvironment :: forall ev deriv.
                     BaseKind
                  -> Type
                  -> Compute ev deriv (SearchResult ev)
searchEnvironment kind ty = do
  st <- getState
  -- Search in this order
  search (premises st) from_premise $
    search (derivations st) from_derivation $
    return NotFound
  where
    -- Search the list.  If not found, go to continuation.
    search :: forall a.
              [Entry a]
           -> (a -> SearchResult ev)
           -> Compute ev deriv (SearchResult ev)
           -> Compute ev deriv (SearchResult ev)
    search list extract k = do
      x <- findM match_entry list
      case x of
        Just (_, _, x) -> return $ extract x
        Nothing        -> k

    from_premise x = Found x
    from_derivation (x, _) = Found x

    match_entry :: forall a. Entry a -> Compute ev deriv Bool
    match_entry (kind2, ty2, _)
      | kind /= kind2 = return False
      | otherwise = compareTypes ty ty2

-- | Return 'True' if a type mentions an inaccessible variable
checkInaccessible :: Type -> Compute e d Bool
checkInaccessible ty = do
  ty' <- normalize ty
  vars <- getInaccessible

  -- Are any of the inaccessible variables mentioned by 'ty'?
  let fv = freeVariables ty'
  return $ any (`Set.member` fv) vars

-- | Insert a premise into the environment
insertPremise :: forall e d. BaseKind -> Type -> e -> Compute e d ()
insertPremise kind ty evidence = Compute $ \_ s -> return (insert s, ())
  where
    insert s = s {premises = (kind, ty, evidence) : premises s}

-- | Insert a derivation into the environment
insertDerivation :: forall e d. BaseKind -> Type -> e -> d -> Compute e d ()
insertDerivation kind ty e d = Compute $ \_ s -> return (insert s, ())
  where
    insert s = s {derivations = (kind, ty, (e, d)) : derivations s}

runComputation :: Compute e d a
               -> TypeEvalM ([Entry e], [Entry (e, d)], a)
runComputation (Compute f) = TypeEvalM $ \var_supply tenv -> do
  (s, x) <- f (Ctx var_supply tenv []) (ComputeState [] [])
  -- Reverse the derivation list so that dependent derivations are at the end
  return (premises s, reverse (derivations s), x)

runSubcomputation :: (Entry e -> Compute e' d' d)
                     -- ^ Derive a premise required by the subcomputation 
                  -> ([Entry (e, d)] -> a -> Compute e' d' b)
                     -- ^ Create a value from the subcomputation
                  -> Compute e d a
                     -- ^ Subcomputation
                  -> Compute e' d' b
                     -- ^ Transformed computation
runSubcomputation derive_premise create_result (Compute f) = do
  -- Run the computation
  (local_st, y) <- Compute $ \ctx st -> do
    let local_st = ComputeState [] []
    x <- f ctx local_st
    return (st, x)

  -- Derive each premise required by the subcomputation.
  let premise_derivation entry@(k, t, e) = do
        d <- derive_premise entry
        return (k, t, (e, d))
  p_derivs <- mapM premise_derivation $ premises local_st

  -- Create and return a value.
  -- Reverse the derivation list so that the dependent derivations are at
  -- the end.
  let derivs = derivations local_st ++ p_derivs
  create_result (reverse derivs) y

-------------------------------------------------------------------------------

-- | A layout computation algorithm
data Algorithm e d =
  Algorithm
  { -- | Create a new evidence value that can stand for a derivation
    lcNewEvidence :: BaseKind -> Type -> Compute e d e
    
    -- The remaining methods construct derivations
    -- | Use evidence in a derivation
  , lcUseEvidence :: BaseKind -> Type -> e -> d
    -- | The layout derivation for an 'int' type.
    --   Corresponds to @ReprVal int@.
  , lcIntType :: Compute e d d
    -- | The layout derivation for a 'uint' type.
    --   Corresponds to @ReprVal uint@.
  , lcUintType :: Compute e d d
    -- | The layout derivation for a 'float' type
    --   Corresponds to @ReprVal float@.
  , lcFloatType :: Compute e d d
    -- | The layout derivation for a 'bool' type
    --   Corresponds to @ReprVal bool@.
  , lcBoolType :: Compute e d d
    -- | The layout derivation for a unit type.
    --   Must return the same result as @lcTag _ ValK 1@.
  , lcUnitType :: Type -> Compute e d d
    -- | The layout derivation for an uninhabited type.
    --   Uninhabited types should be given some layout,
    --   but it doesn't matter what since they will never be created.
  , lcUninhabited :: BaseKind -> Type -> Compute e d d
    -- | The layout derivation for a boxed object
  , lcBox :: Type -> Compute e d d
    -- | The layout derivation for an array, given the
    --   array size and array element layout
  , lcArrType :: d -> d -> Compute e d d
    -- | The layout derivation for a sum or enum tag
  , lcTag :: BaseKind -> Int -> d
    -- | The layout derivation for a union
  , lcUnion :: [d] -> Compute e d d
    -- | The layout derivation for a product
  , lcProduct :: [d] -> Compute e d d
    -- | Turn a combination of tags, unions, and products into a layout
    -- derivation for an algebraic datatype
  , lcAlgType :: BaseKind -> Type -> d -> Compute e d d
    -- | The layout derivation for a type-indexed integer, given a 
    --   type-level integer
  , lcTypeInt :: Integer -> Compute e d d
  }

-- | Add a new premise to the environment
newPremise :: forall e d.
              Algorithm e d
           -> BaseKind
           -> Type
           -> Compute e d e
newPremise lc kind ty = do
  e <- lcNewEvidence lc kind ty
  insertPremise kind ty e
  return e

-- | If the type is available as a premise, get the premise
lookupPremise :: BaseKind -> Type -> Compute e d (Maybe e)
lookupPremise kind t = do
  result <- searchEnvironment kind t
  case result of
    Found x      -> return $ Just x
    NotFound     -> return Nothing

-- | If the type is available as a premise, get the premise; otherwise,
--   create a new premise
lookupOrCreatePremise :: Algorithm e d -> BaseKind -> Type
                      -> Compute e d e
lookupOrCreatePremise lc kind t = do
  result <- lookupPremise kind t
  case result of
    Just x  -> return x
    Nothing -> checkInaccessible t >>= make_premise
  where
    make_premise False = newPremise lc kind t

    -- If an inaccessible variable was mentioned, the input was invalid
    make_premise True  = error "lookupOrCreatePremise: Inaccessible type"

-- | Associate a derivation with a variable
saveDerivation :: Algorithm e d -> BaseKind -> Type -> d -> Compute e d e
saveDerivation lc kind ty derivation = do
  e <- lcNewEvidence lc kind ty
  insertDerivation kind ty e derivation
  return e

-------------------------------------------------------------------------------

-- | Compute the layout of a type-level integer
computeIntValue :: Algorithm e d -> Type -> Compute e d d
computeIntValue lc ty = do
  ty' <- reduceToWhnf ty
  let evidence_type = varApp (coreBuiltin The_IInt) [ty']
  case fromVarApp ty' of
    Just (v, []) -> lcUseEvidence lc IntIndexK ty `liftM`
                    lookupOrCreatePremise lc ValK evidence_type
    Nothing      -> internalError "computeIntValue: Not implemented for this type"

-- | Compute the layouts of the fields of a data constructor,
--   given the universal type arguments
computeDataConFieldLayouts :: Algorithm e d
                           -> Var    -- ^ Data constructor
                           -> [Type] -- ^ Universal type arguments
                           -> Compute e d [d] -- ^ Returns field layouts
computeDataConFieldLayouts lc dcon ty_args = do
  tenv <- getTypeEnv
  let Just dcon_type = lookupDataCon dcon tenv
  (ex_binders, field_types, _) <-
    instantiateDataConTypeWithFreshVariables dcon_type ty_args

  -- Add the existential types to the environment
  assumeInaccessibleList ex_binders $ do
    local_tenv <- getTypeEnv

    -- Get layout of each field
    forM field_types $ \ft -> do
      let field_kind = toBaseKind $ typeKind local_tenv ft
      computeFieldLayout lc field_kind ft

-- | Compute the layout of an algebraic data type.
--   The layout is expressed in terms of tags, unions, and products.
computeAlgObjectLayout :: Algorithm e d
                       -> BaseKind
                       -> DataType
                       -> [Type]
                       -> Compute e d d
computeAlgObjectLayout lc kind dtype args = do
  -- Compute the layouts of each field of each constructor
  field_layouts <-
    mapM (\c -> computeDataConFieldLayouts lc c args) $
    dataTypeDataConstructors dtype

  -- Compute the layout of the tag value.  Single-constructor types
  -- may not need a tag.
  let con     = dataTypeCon dtype
      tag     = lcTag lc kind (length field_layouts)
      product = lcProduct lc
      union   = lcUnion lc

  case field_layouts of
    [] -> lcUninhabited lc kind (varApp con args)

    -- Enum layout: one or more constructors, no fields.
    -- Object is represented by a tag only.
    xs | all null xs -> return tag

    -- Product layout: one constructor.
    -- Tag is included for boxed objects only.
    [fs] | kind == BoxK -> product (tag : fs)
         | otherwise    -> product fs

    -- Sum-of-products layout, the most general case.
    -- Tag each member, then take the union of all members.
    fss -> mapM (product . (tag:)) fss >>= union

-- | Compute the layout of a data type application
computeTypeAppSize :: Algorithm e d -> BaseKind -> Var -> DataType -> [Type]
                   -> Compute e d d
computeTypeAppSize lc kind con dtype args
  | kind /= ValK && kind /= BareK && kind /= BoxK =
      internalError "computeTypeAppSize: Unexpected kind"

  -- Handle special cases
  | con `isCoreBuiltin` The_arr = do
      let [size, element] = args
      int_evidence <- computeIntValue lc size
      element_evidence <- computeFieldLayout lc BareK element
      lcArrType lc int_evidence element_evidence

  | con `isCoreBuiltin` The_int = lcIntType lc
  | con `isCoreBuiltin` The_uint = lcUintType lc
  | con `isCoreBuiltin` The_float = lcFloatType lc
  | con `isCoreBuiltin` The_bool = lcBoolType lc

  -- General cases are algebraic data types
  | otherwise = do
      algebraic_layout <- computeAlgObjectLayout lc kind dtype args

      -- Summarize the algebraic data type's layout
      lcAlgType lc kind (varApp con args) algebraic_layout

-- | Compute the layout of an object field with the given type
computeFieldLayout :: Algorithm e d -> BaseKind -> Type
                   -> Compute e d d
computeFieldLayout lc k ty 
  | k == BoxK               = lcBox lc ty
  | k == BareK || k == ValK = computeObjectLayout lc k ty

-- | Compute the layout of an object with the given type
computeObjectLayout :: Algorithm e d -> BaseKind -> Type
                    -> Compute e d d

computeObjectLayout lc kind ty
  | kind /= ValK && kind /= BareK && kind /= BoxK =
      internalError "computeObjectLayout: Unexpected kind"

computeObjectLayout lc kind ty = do
  tenv <- getTypeEnv
  ty' <- reduceToWhnf ty

  -- Freshen and normalize head before inspecting
  computeObjectLayout' lc tenv kind =<< freshen ty'

computeObjectLayout' :: Algorithm e d -> TypeEnv -> BaseKind -> Type
                     -> Compute e d d
computeObjectLayout' lc tenv kind ty =
  case fromTypeApp ty
  of (VarT con, args)
       | Just dtype <- lookupDataType con tenv ->
           -- This is a data type application
           computeTypeAppSize lc kind con dtype args

       | otherwise ->
           -- This is an unreduceable type function or variable application
           lcUseEvidence lc kind ty `liftM` lookupOrCreatePremise lc kind ty
     (CoT _, _) ->
       -- Coercions translate to unit values
       lcUnitType lc ty
     (AnyT _, _) ->
       internalError "computeObjectLayout: Not implemented for any type"
     (UTupleT field_kinds, _) ->
       internalError "computeObjectLayout: Not implemented for unboxed tuples"

     -- Other terms don't take parameters 
     (FunT {}, []) ->
       lcBox lc ty
     (AllT binder rng, []) ->
       -- A 'forall' type has the same layout as its range
       assumeInaccessible binder $ computeObjectLayout lc kind rng

     _ -> internalError "computeObjectLayout: Unexpected type"

