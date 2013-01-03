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
        Alternative(..), Alternatives, nullaryAlternative,
        Forall(..),
        Structure(..),
        computeStructure,
        StructuralTypeVariance(..),
        computeDataSizes,
        computeAllDataSizes)
where

import Control.Monad
import Control.Monad.ST
import Control.Monad.Trans
import qualified Data.IntMap as IntMap
import qualified Data.Set as Set
import Data.Maybe
import Data.Monoid hiding((<>))
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import Common.Supply
import Common.MonadLogic
import Common.PrecDoc
import Builtins.Builtins
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
data Alternative = Alternative !DeConInst [(Type, BaseKind)]
type Alternatives = [Alternative]

nullaryAlternative (Alternative _ []) = True
nullaryAlternative _                  = False

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

valFields, bareFields, valAndBareFields :: [(Type, BaseKind)] -> [Type]
valFields xs = [t | (t, ValK) <- xs]
bareFields xs = [t | (t, BareK) <- xs]
valAndBareFields xs = [t | (t, k) <- xs, k == ValK || k == BareK]

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
                                      
getBaseKind :: TypeEnvMonad m => Type -> m BaseKind
getBaseKind t = do
  tenv <- getTypeEnv
  return $! toBaseKind $ typeKind tenv t

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
      | con `isCoreBuiltin` The_int -> return $ PrimStruct trioletIntType
      | con `isCoreBuiltin` The_uint -> return $ PrimStruct trioletUintType
      | con `isCoreBuiltin` The_float -> return $ PrimStruct trioletFloatType
      | con `isCoreBuiltin` The_bool -> return BoolStruct

    Just (con, [size, element])
      | con `isCoreBuiltin` The_arr -> return $ ArrStruct size element

    -- Others are either variables or data type constructors
    Just (con, args) -> do
      tenv <- getTypeEnv
      case lookupDataType con tenv of
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
  k <- getBaseKind t
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
      tenv <- getTypeEnv
      let Just dcon_type = lookupDataCon con tenv
      (binders, fields, _) <-
        instantiateDataConTypeWithFreshVariables dcon_type args
      let field_kinds = dataConFieldKinds dcon_type
      let decon_instance = VarDeCon con args binders

      return $ Alternative decon_instance (zip fields field_kinds)

    -- Boxed types have an object header
    boxing =
      case dataTypeKind dtype
      of BoxK -> IsBoxed
         _    -> NotBoxed

-- | The structure of an unboxed tuple type whose fields have the given
--   kinds and types.
unboxedTupleStructure :: [BaseKind] -> [Type] -> Structure
unboxedTupleStructure ks fs =
  DataStruct $ Data NotBoxed [Alternative (TupleDeCon fs) (zip fs ks)]

-------------------------------------------------------------------------------
-- Find the types that affect variable structural components within a given
-- type

-- | Compute all structural subterms of a given type.  Return those subterms
--   whose head is a free variable or a type function application.
--
--   It is an error if any subterms depend on a bound type.
variableStructuralSubterms :: Type -> TypeEvalM [Type]
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
    VarStruct t -> return [t]
  where
    -- If the given type of kind @intindex@ is variable, return it
    -- otherwise return nothing
    int_subterm ty =
      ifM (isVariableIntSubterm ty) (return [ty]) (return [])

    -- Get the variable types found in value and bare fields of a
    -- Data alternative
    alternative_types (Alternative decon fields) =
      withIndependentTypes (deConExTypes decon) $
      concatVariableStructuralSubterms $ valAndBareFields fields

concatVariableStructuralSubterms :: [Type] -> TypeEvalM [Type]
concatVariableStructuralSubterms ts =
  liftM mconcat $ mapM variableStructuralSubterms ts

-- | If the type-level integer term is constant, return an empty list.
--   Otherwise, return a list containing the term.
isVariableIntSubterm :: Type -> TypeEvalM Bool
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
  { -- | Type parameters.  These always correspond one-to-one with the
    --   corresponding data type's type parameters.
    --   They are just renamed versions of the data type's type parameters.
    dtsTyParams :: [Binder]

    -- | Size parameter types
  , dtsSizeParamTypes :: [Type]

    -- | Statically fixed types
  , dtsStaticTypes :: [Type]
  }

-- | Create data type size information for a type whose structure does not
--   vary with its parameters.
invariantStructure :: [Binder] -> StructuralTypeVariance
invariantStructure bs = StructuralTypeVariance bs [] []

-- | Compute size information for a data type constructor.
--   Returns a list of size parameter types and a list of statically fixed
--   types.
computeDataSizes :: DataType -> TypeEvalM StructuralTypeVariance
computeDataSizes dtype
  | not $ dataTypeIsAlgebraic dtype =
    internalError "computeDataSizes: nonalgebraic type"
    
  | otherwise = do
    tenv <- getTypeEnv

    -- Create a new type variable for each type parameter
    params <- mapM rename_binder $ dataTypeParams dtype
    let invariant = return $ invariantStructure params

    assumeBinders params $ do
      -- Create a new type
      let data_type = dataTypeCon dtype `varApp` map (VarT . binderVar) params

      -- Get its layout
      layout <- computeStructure data_type
      case layout of
        DataStruct (Data _ alts) -> do
          -- Find types
          types <- mapM computeAltSizes alts

          -- Remove duplicates from the lists
          let (size_parameter_types, static_types) = mconcat types
          sp2 <- nubTypeList size_parameter_types
          st2 <- nubTypeList static_types
          return $ StructuralTypeVariance params sp2 st2

        UninhabitedStruct -> invariant
        PrimStruct _ -> invariant
        BoolStruct -> invariant

        _ -> internalError "computeDataSizes: Unexpected layout"

  where
    rename_binder (v ::: k) = do
      v' <- newClonedVar v
      return (v' ::: k)

computeAltSizes ::  Alternative -> TypeEvalM ([Type], [Type])
computeAltSizes (Alternative decon fields) =
  withIndependentTypes (deConExTypes decon) $ do
    -- Bare fields produce size parameters
    sizes <- concatVariableStructuralSubterms $ bareFields fields

    -- Val fields produce static types
    static <- concatVariableStructuralSubterms $ valFields fields
    return (sizes, static)

-- | Compute size information for each data type in the environment
computeAllDataSizes :: IdentSupply Var -> TypeEnv
                    -> IO [(Var, StructuralTypeVariance)]
computeAllDataSizes var_supply env = do
  xs <- runTypeEvalM compute var_supply env
  
  -- DEBUG: print results
  print $ pprDataSizes xs
  return xs
  where
    data_constructors = IntMap.elems $ getAllDataTypeConstructors env
    compute =
      liftM catMaybes $
      forM data_constructors $ \dtype ->
      if dataTypeIsAlgebraic dtype
      then do
        info <- computeDataSizes dtype
        return $ Just (dataTypeCon dtype, info)
      else return Nothing

-- | Remove duplicate types from the list
nubTypeList :: [Type] -> TypeEvalM [Type]
nubTypeList xs = go id xs
  where
    go h (x:xs) =
      let continue h' = go h' xs
      in ifM (search x xs) (continue h) (continue (h . (x:)))

    go h [] = return (h [])

    search x xs = anyM (compareTypes x) xs

-- | Produce a debug dump of the information computed by 'computeAllDataSizes'
pprDataSizes xs =
  vcat [hang (pprVar con) 8 $ text "|->" <+> ppr_sizes x| (con, x) <- xs]
  where
    ppr_sizes (StructuralTypeVariance binders size_params fixed_types) =
      text "forall" <+> sep [parens (pprVar v <+> colon <+> pprType t)
                            | v ::: t <- binders] $$
      parens (fsep $ punctuate comma $ map pprType size_params) $$
      parens (fsep $ punctuate comma $ map pprType fixed_types)

