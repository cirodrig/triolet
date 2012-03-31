
{-# LANGUAGE Rank2Types, ViewPatterns #-}
module SystemF.Datatypes.TypeLayout (TypeLayout, computeTypeLayouts)
where

import Control.Monad
import Control.Monad.Trans
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import Data.Maybe
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import Common.Label
import Common.MonadLogic
import Builtins.Builtins
import SystemF.Build
import SystemF.Syntax
import SystemF.MemoryIR
import SystemF.PrintMemoryIR
import SystemF.Datatypes.ComputeLayout
import SystemF.Datatypes.RuntimeLayout
import Type.Type
import Type.Environment
import Type.Eval
import Type.Compare

import qualified LowLevel.Build as LL
import qualified LowLevel.Syntax as LL

-- | Layout information for a data type.
data TypeLayout =
  TypeLayout
  { -- | A global variable holding run-time representation information
    --   for this type.  This is a 'Just' value for
    --   types in kinds @bare@ and @val@, and 'Nothing' for other types.
    --
    --   The variable itself is created when the 'DataType' object is 
    --   created.  However, the global variable definition is not generated
    --   here.
    typeRepr :: !(Maybe Var)

    -- | Parameters taken by 'typeRepr'.  This field is undefined if
    --   'typeRepr' is 'Nothing'.
  , typeReprSignature :: ([Binder], [Type])

    -- | The size context of 'ConE' and 'CaseE' expressions.
    --
    --   The binders are universally quantified type variables.
    --   There is one for each binder in 'dataConPatternParams'.
    --
    --   The first list of types is the size context; these are the type
    --   parameters accepted by a 'ConE' or 'CaseE' expression.
    --
    --   The second list is the fixed types.  After instantiation, these 
    --   types must have a fixed layout.
  , typeSizeContext :: ([Binder], [Type], [Type])

    -- | How to compute the size of an object and the layout of each field
    --   when generating low-level code.
    --
    --   The parameters correspond to the size context.
    --   The computation returns a list of (constructor, size, offsets)
    --   tuples.  Each tuple associates a constructor with the size of 
    --   an object and the byte offsets of its fields.
    --   If objects are tagged, the tag is at byte offset 0.
  , typeStaticSizes :: forall m. [LL.Val] -> LL.Gen m [(Var, LL.Val, [LL.Val])]
  }

-- | Compute the layout of all algebraic data types.
--
--   The type environment parameter should be 'mem' types.
computeTypeLayouts :: IdentSupply Var -> TypeEnv
                   -> IO (Map.Map Var TypeLayout)
computeTypeLayouts var_supply tenv = do
  -- Get layouts for all algebraic data types
  let data_types =
        [(k, t) | (k, t) <- IntMap.elems $ getAllDataTypeConstructors tenv
                , dataTypeIsAlgebraic t]
  layouts <- runTypeEvalM (mapM computeADTLayout data_types) var_supply tenv

  -- Collect global definitions into a list
  let global_defs = Rec [d | (_, _, Just d) <- layouts]

  -- Collect layouts into a map
  let layout_map = Map.fromList [(v, t) | (v, t, _) <- layouts]
  return layout_map

-- | Compute the layout of an algebraic data type.
--
--   Return a layout and a global function definition.
computeADTLayout :: (Kind, DataType)
                 -> TypeEvalM (Var, TypeLayout, Maybe (GDef Mem))
computeADTLayout (kind, dtype) = do
  liftIO $ putStrLn $ "Deriving layout for " ++ show (dataTypeCon dtype)

  -- Create variables to stand for the data type's type parameters
  let (param_kinds, range_kind) = fromFunType kind
  let base_kind = toBaseKind range_kind
  typarams <- forM param_kinds $ \k -> do
    v <- newAnonymousVar TypeLevel
    return (v ::: k)

  let ty_args = map (VarT . binderVar) typarams
  let instantiated_type = varApp (dataTypeCon dtype) ty_args

  -- Create objects related to computing layout dynamically
  (dynamic_function, dynamic_signature, dynamic_def) <-
    if base_kind == BareK || base_kind == ValK
    then computeDynamicLayout typarams base_kind instantiated_type
    else return (Nothing,
                 internalError "No repr signature for this type",
                 Nothing)

  -- Compute size contexts
  (context_types, fixed_types) <-
    assumeBinders typarams $ computeSizeContext base_kind dtype ty_args
  let size_context = (typarams, context_types, fixed_types)

  case dynamic_def of
    Just d -> liftIO $ print $ pprGDef d
    Nothing -> return ()

  let type_layout =
        TypeLayout { typeRepr = dynamic_function 
                   , typeReprSignature = dynamic_signature
                   , typeSizeContext = size_context
                   , typeStaticSizes = internalError "TypeLayout: static sizes not defined"
                   }

  return (dataTypeCon dtype, type_layout, dynamic_def)

-- | Compute the dynamic layout function and related information
--   for a type.
computeDynamicLayout typarams base_kind instantiated_dtype = do
  -- Compute the dynamic layout function for this data type
  (premises, derivations, layout) <-
    runComputation $ assumeBinders typarams $ do
      computeObjectLayout adtRepr base_kind instantiated_dtype
  f <- dynamicLayoutFunction base_kind typarams instantiated_dtype premises derivations layout

  -- Determine the parameters of the layout function,
  -- excluding the dummy parameter
  let layout_signature =
        (typarams, [reprType kind ty | (kind, ty, p) <- premises])

  -- Create a global variable representing the function
  v <- newAnonymousVar ObjectLevel
  let def =
        modifyDefAnnotation (\x -> x {defAnnInlineRequest = True}) $
        mkDef v (FunEnt f)

  return (Just v, layout_signature, Just def)

-- | Create a layout function from the given derivation.
--
--   Each premise becomes a parameter.  Each derivation becomes a let
--   expression, except the last, which provides the return value.
dynamicLayoutFunction data_kind typarams data_type premises derivations layout = do
  -- Layout must be represented by a function.  If necessary, add a dummy
  -- parameter with type 'NoneType'.
  dummy_param <-
    if null premises
    then do v <- newAnonymousVar ObjectLevel
            return $ Just $ patM (v ::: VarT (pyonBuiltin The_NoneType))
    else return Nothing

  -- Create a function from the derivations
  let retval = make_retval data_kind layout
      body = foldr bind_derivation retval derivations
      params = case dummy_param
               of Nothing -> map make_parameter premises
                  Just p  -> [p]
      rtype = reprType data_kind data_type
  return $ FunM $ Fun defaultExpInfo (map TyPat typarams) params rtype body
  where
    make_retval ValK (TVal _ e) = e
    make_retval BareK (TBare _ e) = e

    -- Bind a derivation using a let expression
    bind_derivation (kind, ty, (var, deriv)) body =
      let deriv_pat = patM (var ::: reprType kind ty)
          deriv_exp = trExp deriv
      in ExpM $ LetE defaultExpInfo deriv_pat deriv_exp body

    make_parameter (kind, ty, var) = patM (var ::: reprType kind ty)

-- | Compute the size context of a data type.
--   Return the size context and the fixed types.
computeSizeContext :: BaseKind -> DataType -> [Type]
                   -> TypeEvalM ([Type], [Type])
computeSizeContext base_kind dtype ty_args = do
  (premises, _, structure) <-
    runComputation $ do
      computeAlgObjectLayout adtStructureOnly base_kind dtype ty_args

  -- Find all types that affect the layout of the value fields.
  -- These types must have a fixed layout at each case statement.
  fixed_types <- do
    -- Get the type of each value field
    let pre_fixed_types = val_fields structure

    -- Find the types that these depend on
    fixed_premisess <- mapM get_type_premises pre_fixed_types
    let fixed_premises = [t | (_, t, _) <- concat fixed_premisess]

    -- Remove duplicatse
    nubTypeList fixed_premises

  -- Remove premises that are in the list of fixed types
  filtered_premises <-
    removeByType (\(k, ty, _) -> (fromBaseKind k, ty)) fixed_types premises

  -- Get the type of the run-time description for each 'ty'
  let context_types = [reprType k ty | (k, ty, _) <- filtered_premises]

  liftIO $ print $ map pprType fixed_types
  liftIO $ print $ map pprType context_types
  return (context_types, fixed_types)
  where
    -- Get the value-typed fields of a type
    val_fields (TIProduct xs) = concatMap val_fields xs
    val_fields (TIUnion xs)   = concatMap val_fields xs
    val_fields (TVal t _)     = [t]
    val_fields _              = []

    -- Get the premises needed by the layout derivation of a type.
    -- The argument always has kind 'val'.
    get_type_premises ty = do
      (premises, _, _) <- runComputation $ do
        computeObjectLayout adtStructureOnly ValK ty
      return premises

-- | Remove list elements if they appear in the list of discardable types
removeByType :: (a -> (Kind, Type)) -> [Type] -> [a] -> TypeEvalM [a]
removeByType get_type discardable xs = do
  tenv <- getTypeEnv
  let discardable' = [(typeKind tenv t, t) | t <- discardable]

      -- Evaluates to 'True' if 't' is not in the discardable list
      not_member x =
        let !(k, t) = get_type x
        in allM (liftM not . sameTypeAndKind k t) discardable'

  filterM not_member xs

-- | Remove duplicates from the list of types
nubTypeList :: [Type] -> TypeEvalM [Type]
nubTypeList xs = do tenv <- getTypeEnv
                    nubs tenv [] xs
  where
    -- Compare each type against all unique types.
    -- If it's not equal to any of them, add it to the unique list.
    nubs :: TypeEnv -> [(Kind, Type)] -> [Type] -> TypeEvalM [Type]
    nubs tenv uniques (ty:tys) = do
      let kind = typeKind tenv ty
      ifM (anyM (sameTypeAndKind kind ty) uniques)
        (nubs tenv uniques tys)
        (nubs tenv ((kind, ty) : uniques) tys)

    -- Reverse the list to get the original order
    nubs _ uniques [] = return $ reverse $ map snd uniques

-- Check whether the types have the same type. 
-- Compare their kinds first, since 'compareTypes' may give errors
-- for differently-kinded types.
sameTypeAndKind kind ty (k2, t2) = do
  compareTypes k2 kind >&&> compareTypes t2 ty
