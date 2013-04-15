{-| Structural type computation.

This module computes what is really in a data type, after we strip off 
its type information.  It is \"structural\" in the sense that two types
look the same after transformation iff they have the same contents.

The 'Structure' computed from a type by 'computeStructure' specifies
what the outermost term is made of, in terms of the concrete memory
layout strategies that the compiler knows about.  Each field is
described by a type.  The code in 'SystemF.Datatypes.Size' goes
further and computes how to actually map data to memory or registers.
A 'Structure' can only be computed for kinds inhabited by data types
(that is, @box@, @val@, and @bare@).  Only primitive types, arrays, 
and algebraic data types have a structure.

The function 'computeDataSizes' computes which type paramters of a 
type constructor influence its memory layout.
-}

module SystemF.Datatypes.Structure
       (withIndependentType,
        withIndependentTypes,
        Data(..), Boxing(..), ifBoxed,
        DeConInst(..), deConExTypes, 
        Alternative(..), Alternatives, nullaryAlternative, findAlternative,
        Forall(..),
        Structure(..),
        computeStructure,
        StructuralTypeVariance(..),
        computeDataSizes)
where

import Control.Monad
import Control.Monad.ST
import Control.Monad.Trans
import qualified Data.IntMap as IntMap
import Data.List
import Data.Maybe
import Data.Monoid hiding((<>))
import qualified Data.Set as Set
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import Common.Supply
import Common.MonadLogic
import Common.PrecDoc
import Type.Type
import Type.Environment
import Type.Compare
import Type.Rename(Renameable(..))
import qualified Type.Substitute as S
import Type.Eval
import SystemF.Syntax(DeConInst(..), deConExTypes)
import qualified LowLevel.Syntax as L
import LowLevel.CodeTypes
import qualified LowLevel.Print

-- | The structure of the outermost term of a data type.
data Structure =
    PrimStruct !PrimType               -- ^ A primitive type
  | BoolStruct                         -- ^ The boolean type.  This type is
                                       --   special-cased because it has
                                       --   different representations in memory
                                       --   and in local variables.
  | ArrStruct Type Type                -- ^ An array
  | DataStruct {-# UNPACK #-}!Data     -- ^ An algebraic data type
  | ForallStruct {-# UNPACK #-}!Forall -- ^ A universally quantified type
  | VarStruct Type                     -- ^ Variable structure
  | UninhabitedStruct                  -- ^ A type having no values

-- | An algebraic data structure
data Data = Data !Boxing Alternatives

-- | Whether an algebraic data type is boxed.  Boxing affects how data types
--   are represented in memory.
--
--   A boxed type's tag is always stored in a word, while an unboxed type's
--   tag size varies.  Unboxed sum types have a fixed size, but boxed sums
--   can have a different size depending on constructor.
data Boxing = IsBoxed | NotBoxed

ifBoxed :: Boxing -> a -> Maybe a
ifBoxed IsBoxed  x = Just x
ifBoxed NotBoxed _ = Nothing

-- | A member of a sum-of-products type
data Alternative = Alternative !DeConInst [(BaseKind, Type)]
type Alternatives = [Alternative]

nullaryAlternative (Alternative _ []) = True
nullaryAlternative _                  = False

-- | Find an alternative by its data constructor
findAlternative :: Var -> Alternatives -> Alternative
findAlternative con xs = case find is_alternative xs of Just x -> x
  where
    is_alternative (Alternative (VarDeCon c _ _) _) = con == c
    is_alternative _ = False

-- | A universally quantified data structure
data Forall = Forall Binder Type

pprStructure :: Structure -> Doc
pprStructure (PrimStruct pt) =
  LowLevel.Print.pprPrimType pt
pprStructure BoolStruct =
  LowLevel.Print.pprPrimType BoolType
pprStructure (ArrStruct size elem) =
  pprTypePrec elem ? atomicPrec <> brackets (pprType size)

pprStructure (DataStruct _) = text "(DataStruct {})"
pprStructure (ForallStruct _) = text "(ForallLayout {})"
pprStructure (VarStruct t) = text "layout" <+> pprTypePrec t ?+ appPrec
pprStructure UninhabitedStruct = text "_|_"

-------------------------------------------------------------------------------

valFields, bareFields, valAndBareFields :: [KindedType] -> [Type]
valFields xs = [t | KindedType ValK t <- xs]
bareFields xs = [t | KindedType BareK t <- xs]
valAndBareFields xs = [t | KindedType k t <- xs, k == ValK || k == BareK]

-- | Run some computation in a local environment and verify that its return
--   value does not mention bound variables.
withIndependentType :: (EvalMonad m, Renameable a) => Binder -> m a -> m a
withIndependentType b m =
  withIndependent "withIndependentType" bound_var_not_mentioned
  (assumeBinder b) m
  where
    bound_var_not_mentioned x =
      not $ binderVar b `Set.member` freeVariables x

-- | Run some computation in a local environment and verify that its return
--   value does not mention bound variables.
withIndependentTypes :: (EvalMonad m, Renameable a) => [Binder] -> m a -> m a
withIndependentTypes bs m =
  withIndependent "withIndependentTypes" bound_var_not_mentioned 
  (assumeBinders bs) m
  where
    bound_var_not_mentioned x =
      let fv = freeVariables x
      in not $ or [binderVar b `Set.member` fv | b <- bs]

-- | Helper function for 'withIndependentType' and 'withIndependentTypes'
withIndependent :: EvalMonad m =>
                   String
                -> (a -> Bool)
                -> (m a -> m a)
                -> (m a -> m a)
withIndependent context_name check transform m = transform $ do
  x <- m
  if check x
    then return x
    else internalError $
         context_name ++ ": Layout depends on bound type variable"

-------------------------------------------------------------------------------
-- Getting the structure of a type

-- | Compute the structure of the outermost component of the type.
--   Check the head of the type and decide which structure applies.
computeStructure :: EvalMonad m => Type -> m Structure
computeStructure t = liftTypeEvalM $ do
  t' <- reduceToWhnf t
  case fromVarApp t' of
    -- Non-algebraic type constructors and Bool are handled specially
    Just (con, [])
      | con == intV -> return $ PrimStruct trioletIntType
      | con == uintV -> return $ PrimStruct trioletUintType
      | con == floatV -> return $ PrimStruct trioletFloatType
      {-  | con `isCoreBuiltin` The_bool -> return BoolStruct -}

    Just (con, [size, element])
      | con == arrV -> return $ ArrStruct size element

    -- Others are either variables or data type constructors
    Just (con, args) -> do
      m_data_type <- lookupDataType con
      case m_data_type of
        -- Compute layout of a data type
        Just dtype -> computeDataStructure dtype args

        -- Otherwise it's a type variable and we can't get its layout
        Nothing    -> return $ VarStruct t'

    Nothing ->
      case fromTypeApp t'
      of (AllT b t1, [])  -> return $ ForallStruct (Forall b t1)
         (CoT _, [_, _])  -> return $ PrimStruct UnitType
         (UTupleT ks, fs) -> return $ unboxedTupleStructure ks fs
         _ -> traceShow (pprType t') $ internalError "computeStructure: Unexpected type"

-- | Compute the structure of an object field.
--   If it's boxed, return a pointer type; otherwise, get the type's structure.
computeFieldStructure :: EvalMonad m => Type -> m Structure
computeFieldStructure t = do
  k <- typeBaseKind t
  case k of
    BoxK -> return $ PrimStruct OwnedType
    BareK -> computeStructure t
    ValK -> computeStructure t
    _ -> internalError "computeFieldLayout: Invalid kind"

-- | Compute the structure of a data type, given as a data type definition
--   and type arguments.
computeDataStructure :: EvalMonad m => DataType -> [Type] -> m Structure
computeDataStructure dtype args 
  | n_data_constructors == 0 = return UninhabitedStruct 
  | otherwise = do
  -- Compute field types of all data constructors of the data type
  layouts <- mapM alternative_layout $ dataTypeDataConstructors dtype

  return $ DataStruct $ Data boxing layouts
  where
    n_data_constructors = length $ dataTypeDataConstructors dtype

    -- Compute the layout of one data constructor
    alternative_layout con = do
      Just dcon_type <- lookupDataCon con
      (binders, fields, _) <-
        instantiateDataConTypeWithFreshVariables dcon_type args
      let field_kinds = dataConFieldKinds dcon_type
      let decon_instance = VarDeCon con args binders

      return $ Alternative decon_instance (zip field_kinds fields)

    -- Boxed types have an object header
    boxing =
      case dataTypeKind dtype
      of BoxK -> IsBoxed
         _    -> NotBoxed

-- | The structure of an unboxed tuple type whose fields have the given
--   kinds and types.
unboxedTupleStructure :: [BaseKind] -> [Type] -> Structure
unboxedTupleStructure ks fs =
  DataStruct $ Data NotBoxed [Alternative (TupleDeCon fs) (zip ks fs)]

-------------------------------------------------------------------------------
-- Find the types that affect variable structural components within a given
-- type

-- | Compute all structural subterms of a given type.  Return those subterms
--   whose head is a free variable or a type function application.
--
--   It is an error if any subterms depend on a bound type.
variableStructuralSubterms :: Type -> UnboxedTypeEvalM [KindedType]
variableStructuralSubterms ty = do
  l <- computeStructure ty
  case l of
    PrimStruct _ ->
      return []
    BoolStruct ->
      return []
    ArrStruct size element ->
      mappend `liftM`
      int_subterm size `ap`
      variableStructuralSubterms element
    DataStruct (Data _ alts) ->
      liftM mconcat $ mapM alternative_types alts
    ForallStruct (Forall b t) ->
      withIndependentType b $ variableStructuralSubterms t
    VarStruct t -> do
      base_kind <- typeBaseKind t
      return [KindedType base_kind t]
  where
    -- If the given type of kind @intindex@ is variable, return it
    -- otherwise return nothing
    int_subterm ty = do
      is_variable_int <- isVariableIntSubterm ty
      return $! if is_variable_int then [KindedType IntIndexK ty] else []

    -- Get the variable types found in value and bare fields of a
    -- Data alternative
    alternative_types (Alternative decon fields) =
      withIndependentTypes (deConExTypes decon) $
      concatVariableStructuralSubterms $
      valAndBareFields [KindedType k t | (k, t) <- fields]

concatVariableStructuralSubterms :: [Type] -> UnboxedTypeEvalM [KindedType]
concatVariableStructuralSubterms ts =
  liftM mconcat $ mapM variableStructuralSubterms ts

-- | If the type-level integer term is constant, return an empty list.
--   Otherwise, return a list containing the term.
isVariableIntSubterm :: Type -> UnboxedTypeEvalM Bool
isVariableIntSubterm ty = do
  ty' <- reduceToWhnf ty
  case ty' of
    IntT _ -> return False
    _      -> return True

-- | Information about how a structural data type varies with its type
--   parameters.  This information is generated for algebraic data types
--   from an analysis of the data type.
data StructuralTypeVariance =
  StructuralTypeVariance
  { -- | Type parameters.
    --   These are exactly the same as the data type's type parameters.
    dtsTyParams :: [Binder]

    -- | Size parameter types
  , dtsSizeParamTypes :: [KindedType]

    -- | Statically fixed types
  , dtsStaticTypes :: [KindedType]
  }

-- | Create data type size information for a type whose structure does not
--   vary with its parameters.
invariantStructure :: [Binder] -> StructuralTypeVariance
invariantStructure bs = StructuralTypeVariance bs [] []

-- | Compute size information for a data type constructor.
--   Returns a list of size parameter types and a list of statically fixed
--   types.
computeDataSizes :: DataType -> UnboxedTypeEvalM StructuralTypeVariance
computeDataSizes dtype
  | not $ dataTypeIsAlgebraic dtype =
    internalError "computeDataSizes: nonalgebraic type"
    
  | otherwise =
    assumeBinders params $ do
      -- Get its layout
      layout <- computeStructure data_type
      case layout of
        DataStruct (Data _ alts) -> do
          -- Find types
          types <- mapM computeAltSizes alts

          -- Remove duplicates from the lists
          let (size_parameter_types, static_types) = mconcat types
          sp2 <- nubKindTypeList size_parameter_types
          st2 <- nubKindTypeList static_types
          return $ StructuralTypeVariance params sp2 st2

        UninhabitedStruct -> invariant
        PrimStruct _ -> invariant
        BoolStruct -> invariant

        _ -> internalError "computeDataSizes: Unexpected layout"

  where
    params = dataTypeParams dtype
    data_type = dataTypeCon dtype `varApp` map (VarT . binderVar) params

    -- This is returned for invariant data types
    invariant = return $ invariantStructure params

    rename_binder (v ::: k) = do
      v' <- newClonedVar v
      return (v' ::: k)

computeAltSizes ::  Alternative -> UnboxedTypeEvalM ([KindedType], [KindedType])
computeAltSizes (Alternative decon fields) =
  withIndependentTypes (deConExTypes decon) $ do
    -- Bare fields produce size parameters
    sizes <- concatVariableStructuralSubterms $ bareFields [KindedType k t | (k, t) <- fields]

    -- Val fields produce static types
    static <- concatVariableStructuralSubterms $ valFields [KindedType k t | (k, t) <- fields]
    return (sizes, static)

{-
-- | Compute size information for each data type in the environment.
--   Update the type environment with computed new size information.
computeAllDataSizes :: IdentSupply Var
                    -> ITypeEnvBase UnboxedMode
                    -> IO (ITypeEnvBase UnboxedMode)
computeAllDataSizes var_supply env = do
  let data_constructors = getAllDataTypeConstructors env
  env' <- thawTypeEnv env
  runTypeEvalM (compute data_constructors) var_supply env'
  where
    compute data_constructors = do
      xs <- mapM compute_size_info $ IntMap.elems data_constructors
      liftIO $ print $ pprDataSizes xs      -- DEBUG: print results
      return ()

    -- Compute size information for each data type constructor
    compute_size_info dtype = do
      info <- if dataTypeIsAlgebraic dtype
              then computeDataSizes dtype
              else return $ StructuralTypeVariance (dataTypeParams dtype) [] []

      -- Insert into type environment
      setSizeParameters (dataTypeCon dtype) (dtsSizeParamTypes info)

      return (dataTypeCon dtype, info)
-}

-- | Remove duplicate types from the list
nubTypeList :: [Type] -> UnboxedTypeEvalM [Type]
nubTypeList xs = go id xs
  where
    go h (x:xs) =
      let continue h' = go h' xs
      in ifM (search x xs) (continue h) (continue (h . (x:)))

    go h [] = return (h [])

    search x xs = anyM (compareTypes x) xs

-- | Remove duplicate types from the list
nubKindTypeList :: [KindedType] -> UnboxedTypeEvalM [KindedType]
nubKindTypeList xs = go id xs
  where
    go h (x:xs) =
      let continue h' = go h' xs
      in ifM (search x xs) (continue h) (continue (h . (x:)))

    go h [] = return (h [])

    search x xs = anyM (compare_type x) xs
      where
        -- First check if kinds are the same
        -- Then compare types
        compare_type (KindedType k1 x1) (KindedType k2 x2)
          | k1 == k2  = compareTypes x1 x2
          | otherwise = return False

-- | Produce a debug dump of the information computed by 'computeAllDataSizes'
pprDataSizes xs =
  vcat [hang (pprVar con) 8 $ text "|->" <+> ppr_sizes x| (con, x) <- xs]
  where
    ppr_sizes (StructuralTypeVariance binders size_params fixed_types) =
      text "forall" <+> sep [parens (pprVar v <+> colon <+> pprType t)
                            | v ::: t <- binders] $$
      parens (fsep $ punctuate comma $ map (pprType . discardBaseKind) size_params) $$
      parens (fsep $ punctuate comma $ map (pprType . discardBaseKind) fixed_types)

