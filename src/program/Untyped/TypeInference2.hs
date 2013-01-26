
{-# LANGUAGE FlexibleContexts, ConstraintKinds #-}
module Untyped.TypeInference2 where

import Control.Monad
import Control.Monad.Trans
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import Common.Label
import Common.SourcePos
import Common.Supply
import Untyped.DepAnalysis
import Untyped.Builtins2
import Untyped.Instantiation
import Untyped.Kind
import Untyped.Syntax
import Untyped.TIExp
import Untyped.TIExpConstructors
import Untyped.TIMonad
import Untyped.Type
import Untyped.TypeUnif
import Untyped.TypeInferenceEval
import Untyped.Classes
import Untyped.Print
import Untyped.Proof
import Untyped.Unif
import Untyped.Variable
import qualified SystemF.Syntax as SF
import qualified Builtins.Builtins as SF
import Type.Environment as SF
import Type.Level as SF
import Type.Var as SF
import GlobalVar
import Globals

-------------------------------------------------------------------------------
-- Error messages

ordinal :: Int -> Doc
ordinal 0 = text "zeroth"
ordinal 1 = text "first"
ordinal 2 = text "second"
ordinal 3 = text "third"
ordinal 4 = text "fourth"
ordinal 5 = text "fifth"
ordinal 6 = text "sixth"
ordinal 7 = text "seventh"
ordinal 8 = text "eighth"
ordinal 9 = text "ninth"
ordinal n = text (show n ++ suffix)
  where
    suffix = case n `mod` 10
             of 1 -> "st"
                2 -> "nd"
                3 -> "rd"
                _ -> "th"

-- | A reason that unification is performed, used for error reporting
data Reason =
    -- | Comparing against an explicit type annotation
    ExplicitTypeAnn
    { reaonPos    :: SourcePos
    , reasonThing :: Doc
    }
  | -- | Checking number of function arguments
    CheckedFunArgs
    { reasonPos        :: SourcePos
    , reasonGivenCount :: Int
    }
    -- | Comparing inferred type against type signature
  | CheckedFunSignature
    { reaonPos   :: SourcePos
    , reasonName :: Variable
    }
    -- | Comparing inferred type of function call against inferred type of body
  | InferredFunReturn
    { reaonPos   :: SourcePos
    , reasonName :: Variable
    }

functionReturnTypeReason :: Maybe Variable -> SourcePos -> Reason
functionReturnTypeReason name pos =
  let name_doc = case name
                 of Just n -> pprVariable n
                    Nothing -> text "anonymous function"
  in ExplicitTypeAnn pos (text "return type of" <+> name_doc)

exportReturnTypeReason :: SourcePos -> Variable -> Reason
exportReturnTypeReason pos name =
  ExplicitTypeAnn pos (text "return type of exported function" <+> pprVariable name)

exportParamTypeReason :: SourcePos -> Variable -> Int -> Reason
exportParamTypeReason pos name index =
  let thing = ordinal index <+> text "parameter of exported function" <+> pprVariable name
  in ExplicitTypeAnn pos thing

typeAssertReason :: SourcePos -> Variable -> Reason
typeAssertReason pos name =
  ExplicitTypeAnn pos (text "type assertion" <+> pprVariable name)

listItemReason :: SourcePos -> Reason
listItemReason pos =
  ExplicitTypeAnn pos (text "list element")

functionArgumentReason :: Int -> SourcePos -> Reason
functionArgumentReason index pos =
  ExplicitTypeAnn pos (ordinal index <+> text "argument of function call")

conditionReason :: SourcePos -> Reason
conditionReason pos =
  ExplicitTypeAnn pos (text "boolean condition")

ifBranchReason :: SourcePos -> Reason
ifBranchReason pos =
  ExplicitTypeAnn pos (text "branch of conditional expression")

letBinderReason :: SourcePos -> Reason
letBinderReason pos =
  ExplicitTypeAnn pos (text "right-hand side of assignment")

checkedFunArgsReason :: Int -> SourcePos -> Reason
checkedFunArgsReason n pos = CheckedFunArgs pos n

functionTypeSignatureReason :: SourcePos -> Variable -> Reason
functionTypeSignatureReason pos v = CheckedFunSignature pos v

functionInferredReturnTypeReason :: Variable -> SourcePos -> Reason
functionInferredReturnTypeReason v pos = InferredFunReturn pos v

showTypeError :: Reason -> HMType -> HMType -> Ppr TI Doc
showTypeError reason expected actual = do
  expected_doc <- pprType expected
  actual_doc <- pprType actual
  case reason of
    ExplicitTypeAnn pos thing ->
      let err = text "Type error in" <+> thing <+>
                text "at" <+> text (show pos) <> colon
          e = text "Expected" <+> expected_doc
          g = text "Got" <+> actual_doc
      in return $ err $$ e $$ g
    CheckedFunArgs pos given_args -> do
      (param_tys, return_ty) <- lift $ deconstructFunctionType actual
      let accepted_args = length param_tys
      let err = text "Wrong number of function arguments at" <+>
                text (show pos) <> colon
          eg = int given_args <+>
               text "arguments given, but the function takes" <+>
               int accepted_args
      return $ err $$ eg
    CheckedFunSignature pos v ->
      let err = text "Type error at" <+> text (show pos) <> colon
          g = text "Inferred type" <+> actual_doc <+> text "for" <+>
              pprVariable v
          e = text "Does not match type" <+> expected_doc <+>
              text "required by type signature"
      in return $ err $$ g $$ e
    InferredFunReturn pos v ->
      let err = text "Type error at" <+> text (show pos) <> colon
          g = text "Inferred return type" <+> actual_doc <+> text "of" <+>
              pprVariable v
          e = text "Does not match type" <+> expected_doc <+>
              text "of function boy"
      in return $ err $$ g $$ e

-------------------------------------------------------------------------------

-- | A desugared pattern.
--
--   Consists of a simple variable binding, some code to deconstruct that
--   variable, and a list of all variables bound by the pattern.
--   The simple variable binding may appear in the list of all bound variables.
data DSPattern =
  DSPattern
  { -- | The System F variable bound by the pattern
    dsBoundVar       :: SF.Var
    -- | The type of the bound variable
  , dsType           :: HMType
  , -- | The untyped variables bound by the pattern
    dsBindings       :: [(Variable, HMType)] 
  , dsUnpackBoundVar :: TI (TIExp -> TIExp)
  }

dsTIPat :: DSPattern -> TIPat
dsTIPat p = TIVarP (dsBoundVar p) (mkType $ dsType p) 

-- | Desugar a pattern to a simple, typed variable pattern.
--
--   Return a variable, its type, and a function for unpacking
--   the variable into the original pattern variables.
desugarPattern :: (Supplies m VarID, UMonad HMType m) => Pattern -> m DSPattern
desugarPattern (WildP _) = do
  -- Create a new variable with an unknown type
  sf_v <- SF.newAnonymousVar SF.ObjectLevel
  t <- newType
  return $ DSPattern sf_v t [] (return id)

desugarPattern (VariableP _ v Nothing) = do
  let Just sf_v = varSystemFVariable v
  t <- newType
  return $ DSPattern sf_v t [(v, t)] (return id)
  
desugarPattern (VariableP _ v (Just t)) =
  let Just sf_v = varSystemFVariable v
  in return $ DSPattern sf_v t [(v, t)] (return id)

desugarPattern (TupleP _ ps) = do
  sub_patterns <- mapM desugarPattern ps

  -- Create a new variable with a tuple type
  sf_v <- SF.newAnonymousVar SF.ObjectLevel
  let ty = tupleTy $ map dsType sub_patterns
  let bindings = concatMap dsBindings sub_patterns
  return $ DSPattern sf_v ty bindings (mk_unpack_expr sf_v ty sub_patterns)
  where
    mk_unpack_expr v ty sub_patterns = do
      -- Create an expression from 'v'
      repr <- requireRepr ty
      let v_exp = mkVarE noSourcePos repr v

      -- Create code to unpack the fields
      unpack_fields <- mapM dsUnpackBoundVar sub_patterns

      -- Compute size parameters
      size_params <- mapM (requireRepr . dsType) sub_patterns 

      return $ \e ->
        -- Unpack the tuple, then unpack each field 
        let field_patterns = [mkVarP (dsBoundVar p) (mkType $ dsType p)
                             | p <- sub_patterns]
        in mkTupleCaseE noSourcePos v_exp size_params field_patterns $
           foldr ($) e unpack_fields

-- | Add all pattern-bound variables to the environment
assumePattern :: EnvMonad m => DSPattern -> m a -> m a
assumePattern p m = assumeMonotypes (dsBindings p) m

assumePatterns ps m = foldr assumePattern m ps

-- | Check that the variables @bound_vars@ are not mentioned in @x@.
--   Throw an error if the check fails.
requireFree :: (NormalizeContext HMType m, CTerm a) =>
               String -> [TyCon] -> a -> m ()
requireFree err_message bound_vars x = do
  fv <- freeC x
  when (any (`Set.member` fv) bound_vars) $ error err_message

-- | Get the set of unifiable type variables that are free in the environment
getVisibleTyVars :: (EnvMonad m, NormalizeContext HMType m) => m TyVarSet
getVisibleTyVars = do
  bindings <- getsEnvironment envValues
  liftM Set.unions $ mapM free_vars $ Map.elems bindings
  where
    free_vars (PolyVarAss scm) = tySchemeFreeVars scm
    free_vars (MonoVarAss ty)  = freeUVars ty
    free_vars (RecVarAss inf)  = freeUVars $ VarTy (recVarType inf)
    free_vars (DataConAss _)   = return $ Set.empty -- always defined globally
    free_vars (MethodAss _ _)  = return $ Set.empty -- always defined globally

-- | Given a set of type variables, scan and recompute
recomputeFreeTypeVariables :: (EnvMonad m, NormalizeContext HMType m) =>
                              TyVarSet -> m TyVarSet
recomputeFreeTypeVariables ftv1 = do
  let types = map VarTy $ Set.toList ftv1
  Set.unions `liftM` mapM freeUVars types

pprPlaceholder (DictPlaceholder p) = pprPredicate $ dictPPredicate p

-------------------------------------------------------------------------------
-- Generalization

debugGeneralization = True

failIfPlaceholdersExist location phs 
  | null phs = return ()
  | otherwise = do
      -- If debugging enabled, print error details
      when debugGeneralization $ do
        docs <- runPpr $ mapM pprPlaceholder phs
        liftIO $ print (hang (text "Unresolved placeholders:") 2 $ vcat docs)

      error $ "Unresolved placeholders in " ++ location

failIfNonemptyConstraint location cst 
  | null cst = return ()
  | otherwise = do
      -- If debugging enabled, print error details
      when debugGeneralization $ do
        doc <- runPpr $ pprConstraint cst
        liftIO $ print (hang (text "Unresolved constraint:") 2 doc)
        
      error $ "Unresolved constraint in " ++ location


-- | Generalize types in a subset of a definition group produced by dependence
--   analysis.
--
--   Return the generalized type schemes and the inferred types.
generalizeSubgroup :: Bool -> [FunctionDef] -> TI [(Variable, TyScheme, TIDef)]
-- Each subgroup is either a single explicitly typed definition
-- or any number of implicitly typed definitions  
generalizeSubgroup is_global [fdef]
  | explicitlyTyped fdef = do
      ti_def <- checkPolyTypeSignature is_global fdef
      return [ti_def]

generalizeSubgroup is_global fdefs
  | all (not . explicitlyTyped) fdefs = do
      generalizeImplicitSubgroup is_global fdefs

generalizeSubgroup _ _ =
  internalError "generalizeSubgroup"

-- | Perform type inference on some mutually recursive function definitions  
--   and generalize their types.
generalizeImplicitSubgroup :: Bool -> [FunctionDef]
                           -> TI [(Variable, TyScheme, TIDef)]
generalizeImplicitSubgroup is_global fdefs = do
  -- Will not generalize over type variables in the environment.
  -- Get these unifiable type variables.
  ftv_gamma <- getVisibleTyVars
  
  let defined_variables = [v | FunctionDef v _ _ <- fdefs]

  -- Create a placeholder for each function in the group
  assumeRecursiveVariables defined_variables $ \f_placeholders -> do

    -- Perform type inference in each function body
    (inferred_cst, monotypes, inferred_functions) <- infer_function_bodies

    -- Decide what type variables to generalize over
    ftv_gamma2 <- recomputeFreeTypeVariables ftv_gamma
    runPpr $ do tys <- mapM pprType monotypes
                fvs <- mapM pprUVar $ Set.toList ftv_gamma2
                liftIO $ print (text "fv" <+> fsep fvs $$ text "ty" <+> vcat tys)
    (qvars, retained, deferred) <-
      liftTE_TI $ chooseGeneralizedTypes ftv_gamma2 monotypes inferred_cst

    -- This error should be impossible.  Errors in the input should have
    -- been detected when splitting the context.
    when is_global $
      failIfNonemptyConstraint "global function" deferred

    -- Create bindings for constraints
    retained_bindings <- liftTE_TI $ mapM mkProofBinding retained
    when debugGeneralization $
      liftIO . print =<< runPpr (mapM pprProofBinding retained_bindings)

    -- Construct functions
    let set_up_constraint :: PE ([TIPat], Constraint)
        set_up_constraint = do
          mapM_ assumeProofBinding retained_bindings
          return (map snd retained_bindings, [])

        construct_def
          ( FunctionDef v ann f
          , (inferred_placeholders, body, params, body_ty)) = do

            ([], residual_placeholders, ti_fun) <-
              completePolyFunction (getSourcePos f) qvars
              params set_up_constraint body_ty body inferred_placeholders

            -- In global functions, all placeholders must be resolved
            when is_global $
              failIfPlaceholdersExist ("function " ++ showVariable v)
              residual_placeholders

            -- Construct function definition
            let ti_def = mkDef v ann ti_fun
            let function_type = map dsType params `functionTy` body_ty
            let ty_scheme = Qualified qvars retained function_type
            liftIO . print . (text "Type scheme:" <+>) =<< runPpr (pprTyScheme ty_scheme) -- DEBUG
            return (residual_placeholders, (v, ty_scheme, ti_def))

    constructed_function_results <-
      mapM construct_def $ zip fdefs inferred_functions
    let residual_placeholders = concatMap fst constructed_function_results 
        ti_defs = map snd constructed_function_results
    
    require deferred
    deferPlaceholders residual_placeholders

    -- Fill in recursive variable placeholders
    mapM_ (setRecVarPlaceholder qvars retained_bindings) f_placeholders

    return ti_defs
  where
    infer_function_bodies = do
      -- Do type inference on each function.  Unify with placeholder's type.
      results <- forM fdefs $ \(FunctionDef v _ f) -> do
        ty <- getRecVarType v
        tiFun' (Just v) (Just ty) f

      -- Combine constraints.  The constraint is shared by all
      -- functions in the group.
      let cst = concat [c | (c, _, _, _, _) <- results]
      let monotypes = [functionTy (map dsType params) result_ty
                      | (_, _, _, params, result_ty) <- results]
      let body_results = [(placeholders, body, params, result_ty)
                         | (_, placeholders, body, params, result_ty) <-
                             results]
      return (cst, monotypes, body_results)


-- | Decide which types to generalize over.
--   Generalization will be performed over all type variables that are 
--   in the given list of types, but not in the given free variable set.
--   The constraint is split into retained and deferred parts.
chooseGeneralizedTypes :: TyVarSet -> [HMType] -> Constraint
                       -> TE ([TyCon], Constraint, Constraint)
chooseGeneralizedTypes ftv_gamma monotypes inferred_cst = do
  -- Simplify constraint
  reduced_cst <- reduceContext inferred_cst

  -- Find the type variables that are mentioned in the types and not in
  -- the environment.  These will be generalized over.
  ftv_types <- Set.unions `liftM` mapM freeUVars monotypes

  -- Add type variables that are fixed by 'ftv_types' due to equality
  -- constraints.  For example, in the type @T a ~ b => a -> a@,
  -- type 'a' fixes the value of type 'b'.
  dtv_types <- dependentTypeVariables reduced_cst ftv_types

  let local_tyvars = dtv_types Set.\\ ftv_gamma
  runPpr $ do ts <- mapM pprType monotypes
              dtvs <- mapM pprUVar $ Set.toList dtv_types
              liftIO $ print $ text "splitConstraint on" <+> (fsep dtvs $$ vcat ts)

  (retained, deferred) <- splitConstraint reduced_cst ftv_gamma local_tyvars

  -- Fix the free variables as new type variables
  qvars <- mapM fixTyVar $ Set.elems local_tyvars

  when debugGeneralization $ print_generalization qvars retained deferred
  return (qvars, retained, deferred)
  where
    print_generalization qvars retained deferred = do
      message <- runPpr $ do
        original_doc <- pprConstraint inferred_cst
        scheme_doc <-
          pprQualified return (Qualified qvars retained (text "..."))
        deferred_doc <- pprConstraint deferred
        return $ text "Constraint" <+> original_doc $$
                 text "Generalized to" <+> scheme_doc $$
                 text "Deferred" <+> deferred_doc
      liftIO $ print message

setRecVarPlaceholder :: [TyCon] -> [ProofBinding] -> RecVarP -> TI ()
setRecVarPlaceholder qvars bindings ph@(RecVarP rec_var _) = do
  -- Apply the function to the inferred type parameters and
  -- dictionary parameters
  let Just v = varSystemFVariable rec_var
      v_exp = mkVarE noSourcePos TIBoxed v
      ty_args = map ConTy qvars
      dict_args = [mkVarE noSourcePos unknownRepr v
                  | (_, TIVarP v _) <- bindings]
      inst_exp =
        mkPolyCallE noSourcePos TIBoxed v_exp (map mkType ty_args) dict_args

  -- Assign the placeholder
  liftIO $ setRecVarP ph inst_exp

-- | Verify that the function's polymorphic type signature satisfies the
--   currently inferred type.  Generate code to satisfy the constraint.
checkPolyTypeSignature :: Bool -> FunctionDef
                       -> TI (Variable, TyScheme, TIDef)
checkPolyTypeSignature is_global
  fdef@(FunctionDef def_name def_ann def_function) =

  -- Add the function itself, and its type parameters, to the type environment
  assumePolytype def_name ty_scheme $
  withTyParams given_tyvars $ do

    -- Perform type inference in the function body.
    -- Get constraints and placeholders produced by type inference.
    (inferred_cst, placeholders, inferred_exp, params, inferred_ty) <-
      tiFun' (Just def_name) Nothing def_function

    -- Construct the polymorphic function
    let set_up_constraint :: PE ([TIPat], Constraint)
        set_up_constraint = do
          -- Add declared constraints to environment
          cst_bindings <- assumeConstraint given_cst

          -- Verify that inferred constraint follows from given constraint
          residual_cst <-
            liftTE_PE $
            checkDeclaredConstraint pos given_tyvars given_cst inferred_cst

          return (map snd cst_bindings, residual_cst)

    (residual_cst, residual_placeholders, ti_fun) <-
      completePolyFunction (getSourcePos def_function) given_tyvars params
      set_up_constraint inferred_ty inferred_exp placeholders

    -- In global functions, all placeholders and constraints must be satisfied
    when is_global $ do
      failIfNonemptyConstraint "global function" residual_cst
      failIfPlaceholdersExist "global function" residual_placeholders

    -- Propagate constraint and placeholders that weren't fixed
    require residual_cst
    deferPlaceholders residual_placeholders

    -- Construct the function definition
    let ti_def = mkDef def_name def_ann ti_fun

    return (def_name, ty_scheme, ti_def)
  where
    pos = getSourcePos fdef

    -- This should succeed; failure cases should have been caught by Parser
    !(Just given_polytype) = explicitFunctionType fdef
    ty_scheme = fmap (uncurry functionTy) given_polytype
    Qualified given_tyvars given_cst (given_param_tys, given_return_ty) =
      given_polytype

-- | Simplify @expected_cst@, given @given_cst@.
--
--   Returns the residual constraint, which is the part of
--   @expected_cst@ that isn't implied by @given_cst@.
--   It's an error if the residual constraint mentions @given_tyvars@.
checkDeclaredConstraint pos given_tyvars given_cst expected_cst = do
  -- Remove inferred constraints that follow from the declared ones
  residual_cst <- solveConstraintWithContext pos given_cst expected_cst

  -- Leftover constraints must be independent of type parameters.
  -- If this is a global function, leftover constraints must be empty.
  let error_message = "Constraint satisfaction failed"
  requireFree error_message given_tyvars residual_cst

  return residual_cst

-- | Construct a polymorphic function from the given information
completePolyFunction :: SourcePos     -- ^ Origin of function definition
                     -> [TyCon]       -- ^ Type parameters
                     -> [DSPattern]   -- ^ Function parameters
                     -> PE ([TIPat], Constraint)
                        -- ^ Constraint setup.  Creates bindings for predicate
                        --   parameters and returns a deferred constraint. 
                     -> HMType        -- ^ Return type
                     -> TIExp         -- ^ Inferred function body
                     -> Placeholders
                        -- ^ Dictionary placeholders from function body
                     -> TI (Constraint, Placeholders, TIFun)
completePolyFunction pos typarams params set_up_constraint rtype
                     body placeholders = placeholderFree $ do
  (fun_body, (cst_bindings, residual_cst, residual_placeholders)) <-
    generateProof $ do
      -- Set up dictionaries in the environment
      (cst_bindings, residual_cst) <-
        placeholderFree_PE "constraint setup" $
        set_up_constraint

      -- Fill in placeholder expressions.
      -- Ignore the constraints generated by placeholders;
      -- they're equivalent to 'residual_cst'.
      (_, residual_placeholders) <-
        getPlaceholders_PE $ satisfyPlaceholders placeholders

      return (unknownRepr, body, (cst_bindings, residual_cst, residual_placeholders))

  -- Build the typed function
  let ti_typarams = [ TITyPat (tyConSFVar tc) (mkKind $ tyConKind tc)
                    | tc <- typarams]
      ti_params = cst_bindings ++ map dsTIPat params
      ti_rtype = mkType rtype
      ti_body = fun_body
      ti_f = TIFun pos ti_typarams ti_params ti_rtype ti_body
  return (residual_cst, residual_placeholders, ti_f)

mkDef :: Variable -> FunctionAnn -> TIFun -> TIDef
mkDef v ann f = TIDef sf_var (mkAnnotation ann) f
  where
    !(Just sf_var) = varSystemFVariable v

-- | Convert a unifiable type variable to a new type constructor
fixTyVar :: TyVar -> TE TyCon
fixTyVar v = do
  free <- isFreeUVar v
  unless free $ internalError "fixTyVar: Not a free unifiable variable"

  -- Unify with a fresh type variable
  tycon <- newTyVar (uVarName v) (uVarKind v)
  unifyUVar v (ConTy tycon)
  return tycon

-------------------------------------------------------------------------------
-- Unification helper functions

-- | Create a new type variable
newType :: (Supplies m VarID, UMonad HMType m) => m HMType
newType = do
  tyvar <- newAnonymousUVar Star
  return $ VarTy tyvar

-- | Unify two types without generating any code.
--   Types must match exactly; coercible types are not accepted.
tiUnifyTypes :: Reason -> HMType -> HMType -> TI ()
tiUnifyTypes reason expected given = do
  m_cst <- unify expected given
  case m_cst of
    Just deferred_cst -> do
      require deferred_cst
      if any isEqualityPredicate deferred_cst
        then error "Unification failed"
        else return ()
    Nothing -> do
      message <- runPpr $ showTypeError reason expected given
      error (show message)

-- | Unify the expected and given types, where the given type is the type
--   of 'e'.  If coercion is necessary, 'e' will be coerced from given to
--   expected type.
--   An exception is raised if unification fails.
tiUnify :: Reason -> HMType -> HMType -> TIExp -> TI TIExp
tiUnify reason expected given e = do
  m_cst <- unify expected given
  case m_cst of
    Just deferred_cst -> do
      require deferred_cst

      -- If unification produced equality constraints, a coercion may
      -- be required
      if any isEqualityPredicate deferred_cst
        then return $
             mkCoerceE noSourcePos unknownRepr (mkType given) (mkType expected) e
        else return e

    Nothing -> do
      message <- runPpr $ showTypeError reason expected given
      error (show message)

-- | Unify a variable's type with the given type.  An exception is raised if
--   unification fails.
tiUnifyVariable :: Reason -> SourcePos -> HMType -> Variable -> TI ()
tiUnifyVariable reason pos ty v =
  -- Instantiate the variable and unify its type. 
  -- Ignore the generated code and ignore its placeholders, but
  -- keep its type class constraints.
  void $ getPlaceholders $ instantiateVarAtType reason pos v ty

-- | Instantiate a variable at a particular type
instantiateVarAtType :: Reason -> SourcePos -> Variable -> HMType -> TI TIExp
instantiateVarAtType reason pos v expected_ty = do
  (inferred_ty, e) <- instantiateVar pos v
  tiUnify reason expected_ty inferred_ty e

tiExpAtType :: (SourcePos -> Reason) -> HMType -> Expression -> TI TIExp
tiExpAtType reason expected e =
  do (e', _, inferred) <- tiExp e
     let pos = getSourcePos e
     tiUnify (reason pos) expected inferred e'

-------------------------------------------------------------------------------
-- Type inference on terms

tiExp' :: Expression -> TI (TIExp, HMType)
tiExp' es = do (e, _, t) <- tiExp es
               return (e, t)

-- | Infer the type and representation of an expression.
tiExp :: Expression -> TI (TIExp, TIRepr, HMType)
tiExp expression = 
  case expression
  of VariableE _ v           -> tiVariable pos v
     LiteralE _ l            -> tiLiteral pos l
     ListE _ es              -> tiList pos es
     UndefinedE _            -> tiUndefined pos
     TupleE _ fs             -> tiTuple pos fs
     CallE _ op args         -> tiCall pos op args
     IfE _ c t f             -> tiIf pos c t f 
     FunE _ f                -> do (f, ty) <- tiLambda f
                                   return (mkFunE pos f, TIBoxed, ty)
     LetE _ p rhs body       -> tiLet pos p rhs body
     LetrecE _ defs body     -> tiLetrec pos defs body
     TypeAssertE _ v ty body -> tiTypeAssert pos v ty body
  where
    pos = getSourcePos expression

tiVariable pos v = do
  (ty, e) <- instantiateVar pos v
  repr <- requireRepr ty
  return (e, repr, ty)
     
tiLiteral pos l = do
  repr <- requireRepr ty
  return (mkLitE pos l, repr, ty)
  where
    ty = case l
         of IntL _   -> ConTy $ builtinTyCon TheTC_int
            FloatL _ -> ConTy $ builtinTyCon TheTC_float
            BoolL _  -> ConTy $ builtinTyCon TheTC_bool
            NoneL    -> ConTy $ builtinTyCon TheTC_NoneType

tiList pos elements = do
  -- Create a type variable to stand for the empty list's contents
  elt_type <- newType
  let list_type = ConTy (builtinTyCon TheTC_list) @@ elt_type

  -- Infer type of each given element.  Unify element types with
  -- the 'elt_type' variable.
  ti_elements <- mapM (tiExpAtType listItemReason elt_type) elements

  list_repr <- requireRepr list_type
  let list = mkListE pos (mkType elt_type) list_repr []
  return (list, list_repr, list_type)

tiUndefined pos = do
  ty <- newType
  repr <- requireRepr ty
  return (mkUndefinedE pos repr (mkType ty), repr, ty)

tiTuple pos fs = do
  (ti_elements, ti_reprs, ti_types) <- liftM unzip3 $ mapM tiExp fs
  let ty = tupleTy ti_types
  repr <- requireRepr ty
  let tuple = mkTupleE pos repr (map mkType ti_types) ti_reprs ti_elements
  return (tuple, repr, ty)

tiCall pos op args = do
  -- Create function type
  let n_args = length args
  param_types <- replicateM n_args newType
  return_type <- newType
  let ty = param_types `functionTy` return_type

  -- Infer type of operator
  let op_reason pos = checkedFunArgsReason n_args pos
  op_exp <- tiExpAtType op_reason ty op

  -- Unify argument types with parameter types
  arg_exps <- sequence [tiExpAtType (functionArgumentReason i) t e
                       | (i, t, e) <- zip3 [1..] param_types args]

  repr <- requireRepr return_type
  let exp = mkAppE pos repr op_exp [] arg_exps
  return (exp, repr, return_type)

tiIf pos c t f = do
  c_exp <- tiExpAtType conditionReason (ConTy $ builtinTyCon TheTC_bool) c
  branch_type <- newType
  t_exp <- tiExpAtType ifBranchReason branch_type t
  f_exp <- tiExpAtType ifBranchReason branch_type f
  repr <- requireRepr branch_type
  let exp = mkIfE pos repr c_exp t_exp f_exp
  return (exp, repr, branch_type)

tiLet pos pat rhs body = do
  ds_pat <- desugarPattern pat
  ti_rhs <- tiExpAtType letBinderReason (dsType ds_pat) rhs
  assumePattern ds_pat $ do
    unpack <- dsUnpackBoundVar ds_pat
    (ti_body, repr, ty) <- tiExp body
    let exp = mkLetE pos repr (dsTIPat ds_pat) ti_rhs $ unpack ti_body
    return (exp, repr, ty)

tiLetrec pos defs body = tiDefGroup False defs $ \defs' -> do
  (ti_body, repr, ty) <- tiExp body
  let exp = mkLetrecE pos repr defs' ti_body
  return (exp, repr, ty)

tiTypeAssert pos v ty body = do
  -- Unify the type of 'v' with 'ty'
  tiUnifyVariable (typeAssertReason pos v) pos ty v
  tiExp body

-- | Infer the type of a function's body.  Also get the constraints
--   and placeholders produced by type inference.
tiFun' :: Maybe Variable        -- ^ Function name, used in error messages.
                                --   If there is no name, it's called an
                                --   anonymous function.
       -> Maybe HMType          -- ^ The function's type, if this is a
                                --   recursive function whose type is being
                                --   inferred.  The type will be unified
                                --   with the declared parameter and return
                                --   types.  If given, name must be given.
       -> Function              -- ^ The function to examine
       -> TI (Constraint, Placeholders, TIExp, [DSPattern], HMType)
tiFun' name given_type f = do
  (((params, ty, e), cst), phs) <-
    getPlaceholders $ getConstraint $ tiFun name given_type f
  return (cst, phs, e, params, ty)

-- | Infer the type of a function's body.
--   Desugar and unpack the function parameters.
--   Get the typed function body.
--   The function name, if given, is used for reporting errors.
tiFun :: Maybe Variable -> Maybe HMType -> Function
      -> TI ([DSPattern], HMType, TIExp)
tiFun name placeholder_type f = do
  -- Desugar the function parameters
  ds_params <- mapM desugarPattern $ funParameters f

  -- Get a return type
  return_ty <- case funReturnType f
               of Nothing -> newType
                  Just t  -> return t

  -- Unify placeholder type with declared type
  let signature_type = map dsType ds_params `functionTy` return_ty
  check_placeholder_type signature_type

  -- Add function parameters to the environment and compute the function body
  assumePatterns ds_params $ do
    body <- infer_body_type (funBody f) return_ty

    -- Generate code to unpack the function parameters 
    unpack_params <- mapM dsUnpackBoundVar ds_params
    let body'' = foldr ($) body unpack_params
    return (ds_params, return_ty, body'')
  where
    -- If a placeholder type was given, unify it with the function signature. 
    -- Mismatch means that the function was called in a manner incompatible
    -- with its signature.
    check_placeholder_type signature_type =
      case (name, placeholder_type)
      of (_, Nothing) -> return ()   -- No placeholder type
         (Just v, Just t) -> do
           let reason = functionTypeSignatureReason (getSourcePos f) v
           tiUnifyVariable reason (getSourcePos f) signature_type v

         -- Cannot unify variable's type if variable is not given
         (Nothing, Just t) -> internalError "tiFun"

    -- Check that the function body's type is correct
    infer_body_type body return_ty =
      let reason =
            if isJust $ funReturnType f -- Return type was declared explicitly?
            then functionReturnTypeReason name
            else let !(Just n) = name
                 in functionInferredReturnTypeReason n
      in tiExpAtType reason return_ty $ funBody f


-- | Infer the type of a lambda function.  The result is always a monotype.
tiLambda :: Function -> TI (TIFun, HMType)
tiLambda f = do 
  (params, rtype, body) <- tiFun Nothing Nothing f
  let pos = getSourcePos f
      ti_f = TIFun pos [] (map dsTIPat params) (mkType rtype) body
      ty = map dsType params `functionTy` rtype
  return (ti_f, ty)

-- | Infer the type of an export statement.  Verify that it's monomorphic.
--   Since the exported object may be polymorphic, generate a wrapper
--   function that calls the exported object.
tiExport :: Export -> TI TIExport
tiExport (Export ann spec v ty) = do
  -- Get parameter and return types
  (param_tys, return_ty) <- deconstructFunctionType ty

  -- Create parameter variables
  param_vars <- mapM (const newAnonymousVariable) param_tys
  let param_bindings = [ VariableP ann v (Just t)
                       | (v, t) <- zip param_vars param_tys]
  ds_params <- mapM desugarPattern param_bindings

  -- Create a call of the exported variable
  ((e, cst), phs) <-
    getPlaceholders $ getConstraint $
    instantiateExportedVariable pos ds_params param_bindings return_ty v

  -- Create a function
  let check_cst = do
        -- Reduce the constraint, so that type variables get unified
        -- as a result of equality predicates.  Afterward, discard
        -- the constraints.  There are no constraints after reduction
        -- is complete because the type is monomorphic.
        reduced <- liftTE_PE $ reduceContext cst

        -- Reduced constraint should always be empty, since the function
        -- is global and monomorphic
        failIfNonemptyConstraint location_string reduced

        return ([], [])

  (residual_cst, residual_phs, ti_fun) <-
    completePolyFunction pos [] ds_params check_cst return_ty e phs

  failIfNonemptyConstraint location_string residual_cst
  failIfPlaceholdersExist location_string residual_phs

  return $ TIExport pos spec ti_fun
  where
    location_string = "exported function at " ++ show pos
    pos = case ann of Ann pos -> pos

-- | Create a call of an exported variable.
instantiateExportedVariable :: SourcePos -> [DSPattern] -> [Pattern]
                            -> HMType -> Variable -> TI TIExp
instantiateExportedVariable pos ds_params params return_type v =
  assumePatterns ds_params $ do
    -- Generate paramter-unpacking code
    unpack_params <- mapM dsUnpackBoundVar ds_params

    -- Create variable
    (inst_type, inst_exp) <- instantiateVar pos v
    (inst_param_tys, inst_return_ty) <- deconstructFunctionType inst_type

    -- Check that number of parameters matches
    when (length inst_param_tys /= length params) $
      error "Wrong number of parameters in exported function type"

    -- DEBUG
    {-liftIO . print =<< runPpr (do { xs <- mapM pprType inst_param_tys
                                  ; y <- pprType inst_return_ty
                                  ; z <- pprType inst_type
                                  ; return (parens (vcat (xs ++ [y])) $$ z)})-}

    -- Create arguments at the types expected by the function
    args <-
      forM (zip3 [1..] params inst_param_tys) $ \(n, VariableP _ v _, t) ->
      instantiateVarAtType (exportParamTypeReason pos v n) pos v t
    repr <- requireRepr inst_return_ty

    -- Create call
    let call = mkPolyCallE pos repr inst_exp [] args
        reason = exportReturnTypeReason pos v
    call' <- tiUnify reason return_type inst_return_ty call

    return call'

-- | Perform type inference on a definition group.  Definitions are
--   generalized to type schemes.
--   Definitions are added to the environment over the scope of the
--   continuation.
tiDefGroup :: Bool -> DefGroup -> (SF.DefGroup TIDef -> TI a) -> TI a
tiDefGroup is_global defs k = infer_subgroups subgroups (k . SF.Rec)
  where
    subgroups = depAnalysis defs

    -- Generalize one subgroup at a time.
    -- Add the generalized group to the type environment and continue.
    infer_subgroups (g:gs) k = do
      results <- generalizeSubgroup is_global g
      let polytypes = [(v, t) | (v, t, _) <- results]
          ti_defs = [d | (_, _, d) <- results]
      assumePolytypes polytypes $ infer_subgroups gs (k . (ti_defs ++))

    infer_subgroups [] k = k []

tiGlobalDefGroups (defs:defss) exports =
  tiDefGroup True defs $ \defs' -> do
    (defss', exports') <- tiGlobalDefGroups defss exports
    return (defs':defss', exports')

tiGlobalDefGroups [] exports = do 
  exports' <- mapM tiExport exports
  return ([], exports')

tiModule :: Module -> TI (ModuleName, [SF.DefGroup TIDef], [TIExport])
tiModule (Module module_name defss exports) = do
  (defss', exports') <- tiGlobalDefGroups defss exports
  return (module_name, defss', exports')

-------------------------------------------------------------------------------

-- | Run the computation, then convert any unifiable variables it has created 
--   to 'Any' types.
eliminateUnificationVariables :: TI a -> TI a
eliminateUnificationVariables m = do
  (x, free_vars) <- getFreeVariables m

  -- Any unbound variables that haven't been unified shall now be converted
  -- to an Any type
  mapM_ defaultFreeVariable free_vars

  return x
  where
    -- Free variables default to 'any'.
    -- Defaulting does not produce constraints.
    defaultFreeVariable v = do
      b <- isFreeUVar v
      if b
        then unifyUVar v (AnyTy $ uVarKind v)
        else return ()

typeInferModule :: Module -> IO (SF.Module SF.SF)
typeInferModule m = do
  env <- readInitGlobalVarIO the_TITypes

  -- Run type inference
  ti_module <- runTI env $ check_placeholders $
               eliminateUnificationVariables $ tiModule m
  
  -- Force evaluation of all IO stuff
  runTE env $ evalTypeInferenceResult ti_module
  where
    check_placeholders m = do
      (x, ph) <- getPlaceholders m
      unless (null ph) $ runPpr $ do
        docs <- mapM ppr_placeholder ph
        let message = text "runTI: Unresolved placeholders after type inference" $$
                      nest 2 (vcat docs)
        internalError (show message)
      return x

    ppr_placeholder (DictPlaceholder p) = pprPredicate $ dictPPredicate p
