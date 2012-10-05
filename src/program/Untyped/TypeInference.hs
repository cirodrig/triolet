
{-# LANGUAGE TypeSynonymInstances #-}
module Untyped.TypeInference
       (typeInferModule)
where

import Control.Concurrent.MVar
import Control.Monad
import Control.Monad.Trans
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid
import qualified Data.Set as Set
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Label
import Common.SourcePos
import Common.Supply
import Globals
import qualified SystemF.Syntax as SystemF
import qualified Builtins.Builtins as SystemF
import Untyped.Builtins
import Untyped.Data
import Untyped.Syntax
import Untyped.HMType
import Untyped.Kind
import Untyped.GenSystemF
import Untyped.Unification
import Untyped.Classes
import Untyped.Print
import Untyped.TypeAssignment
import Untyped.TypeInferenceEval
import Type.Level
import Type.Var(Var, mkAnonymousVar)

zipWithM3 :: Monad m => (a -> b -> c -> m d) -> [a] -> [b] -> [c] -> m [d]
zipWithM3 f (x:xs) (y:ys) (z:zs) = do
  w <- f x y z
  ws <- zipWithM3 f xs ys zs
  return (w:ws)
  
zipWithM3 f _ _ _ = return []

mapAndUnzip3M :: Monad m => (a -> m (b, c, d)) -> [a] -> m ([b], [c], [d])
mapAndUnzip3M f xs = do
  ys <- mapM f xs
  return (unzip3 ys)


printUnresolvedPlaceholders ps = mapM print_placeholder ps
  where
    print_placeholder (DictPH {phExpPredicate = pred}) = do
      pred_name <- runPpr (pprPredicate pred)
      print (text "Unresolved dictionary placeholder" <+> pred_name)
        
    print_placeholder _ =
      putStrLn "Unknown non-dictionary placeholder"

-------------------------------------------------------------------------------
-- Coercions

-- | A type coercion.  Type coercions modify a value's data type without
--   changing its underlying representation.  Coercions are needed for some 
--   uses of type functions.
data Coercion =
    -- | The identity coercion, which does nothing.
    NoCoercion HMType
    -- | @Coercion t1 t2@ is a coercion from type t1 to type t2.
  | Coercion HMType HMType

-- | Apply a coercion to an expression
applyCoercion :: Coercion -> TIExp -> IO TIExp
applyCoercion (NoCoercion _) e =
  return e

applyCoercion (Coercion from_t to_t) e = do
  return $ mkCoerceE noSourcePos (convertHMType from_t) (convertHMType to_t) e

-------------------------------------------------------------------------------
-- The type inference monad

newtype Inf a =
  Inf {runInf :: Environment
              -> IO (Constraint, TyVarSet, Placeholders, a)}

infReturn :: a -> IO (Constraint, TyVarSet, Placeholders, a)
infReturn x = return ([], Set.empty, [], x)

instance Functor Inf where
  fmap f (Inf g) = Inf $ \env -> do (c, v, p, x) <- g env
                                    return (c, v, p, f x)

instance Monad Inf where
  return x = Inf $ \_ -> infReturn x
  fail msg = Inf $ \_ -> fail msg
  Inf f >>= k = Inf $ \env -> do
    (c1, s1, p1, x) <- f env
    (c2, s2, p2, y) <- runInf (k x) env
    return (c1 ++ c2, Set.union s1 s2, p1 ++ p2, y)

instance MonadIO Inf where
  liftIO m = Inf $ \_ -> infReturn =<< m

getEnvironment :: Inf Environment
getEnvironment = Inf $ \env -> infReturn env

withEnvironment :: (Environment -> IO a) -> Inf a
withEnvironment f = Inf $ \env -> infReturn =<< f env

assume :: Variable -> TypeAssignment -> Inf a -> Inf a
assume v assignment (Inf f) = Inf $ \env ->
  f (Map.insert v assignment env)

-- | Unify types in the Inf monad.  The first parameter is the expected type,
--   the second is the given type.
--
--   Generated constraints are added to the context.
--
--   A coercion from given type to expected type is returned.
--
--   FIXME: We should actually generate coercion placeholders instead of 
--   coercions.  Later steps of type inference may produce additional
--   unification of type variables, which may affect the form of coercions
--   that have already been generated.  Using placeholders to resolve
--   coercions after-the-fact would solve the problem.
unifyInf :: Bool -> SourcePos -> HMType -> HMType -> Inf Coercion
unifyInf reduce pos expect given = Inf $ \_ -> do
  c <- unify pos expect given

  -- In contexts where coercions are not permitted, we should reduce the
  -- constraint immediately
  c' <- if reduce
        then reduceContext c
        else return c

  -- If unification produced equality constraints, the type must be coerced
  let coercion = if any isEqualityPredicate c'
                 then Coercion given expect
                 else NoCoercion expect
  return (c', Set.empty, [], coercion)

unifyAndCoerceInf :: SourcePos
                  -> TIExp      -- ^ Expression with given type
                  -> HMType     -- ^ Expected type
                  -> HMType     -- ^ Given type
                  -> Inf TIExp  -- ^ Returns expression with expected type
unifyAndCoerceInf pos e expected given = do
  co <- unifyInf False pos expected given
  liftIO $ applyCoercion co e

-- | Add a predicate to the context
requirePredicate :: Predicate -> Inf ()
requirePredicate p = require [p]

-- | Require the given type to have a parameter-passing convention
requirePassable :: HMType -> Inf ()
requirePassable ty = do 
  require [ty `IsInst` tiBuiltin the_c_Repr]

-- | For debugging, print a constraint
printContext s c | null c = return ()
                 | otherwise = do doc <- runPpr $ pprContext c
                                  print (text s <+> doc)

-- | Add a constraint to the context
require :: Constraint -> Inf ()
require c = Inf $ \_ -> return (c, Set.empty, [], ())

-- | Fail if the given type contains type variables.  Unified variables will
-- not be expanded before checking.
failIfPolymorphic pos ty = go ty
  where
    go ty =
      case ty
      of ConTy c | isTyVar c -> fail "Type may not contain type variables"
                 | otherwise -> pass
         FunTy _ -> pass
         TupleTy _ -> pass
         AppTy t1 t2 -> go t1 >> go t2

    pass = return ()

-------------------------------------------------------------------------------
-- Environments

-- | An environment assigns types and System F translations to variables
type Environment = Map.Map Variable TypeAssignment

-- | Get all free, unifiable type variables from the environment
ftvEnvironment :: Environment -> IO TyVarSet
ftvEnvironment env =
  liftM Set.unions $ mapM assignedFreeVariables $ Map.elems env

-- | Instantiate a variable
instantiateVariable :: SourcePos -> Variable -> Inf (TIExp, HMType)
instantiateVariable pos v = Inf $ \env ->
  case Map.lookup v env
  of Nothing  -> internalError $
                 "No type for variable " ++ maybe "" showLabel (varName v)
     Just ass -> do
       (placeholders, vars, constraint, ty, val) <-
         instantiateTypeAssignment pos ass
         
       -- There must be a parameter passing convention for this type
       let cst = ty `IsInst` tiBuiltin the_c_Repr

       -- For debugging, show the instantiation that occurred
       -- printContext ("instantiate " ++ maybe "" showLabel (varName v)) (cst : constraint)
       return (cst:constraint, vars, placeholders, (val, ty))

-------------------------------------------------------------------------------

-- | Generalize a set of types to type schemes in a common type environment.
--
-- The returned type schemes will use the same type variables as the original 
-- environment.  This is relied on for translating code to System F after
-- generalization.
generalize :: Environment       -- ^ Environment to generalize in
           -> Constraint        -- ^ Class constraints to generalize over
           -> [(Maybe [TyCon], HMType)] -- ^ Inferred types
           -> IO (Constraint, TyVarSet, Constraint, [TyScheme])
generalize env constraint inferred_types = do
  let types = map snd inferred_types 
  
  -- Simplify the constraints
  reduced_constraint <- reduceContext constraint
  
  -- Find type variables that are free in the definition group's types or
  -- dependent on a free variable.
  -- Will generalize over type variables that are dependent on the type,
  -- but not free in the environment.
  ftv_gamma <- ftvEnvironment env
  ftv_types <- liftM Set.unions $ mapM freeTypeVariables types
  dtv_types <- dependentTypeVariables reduced_constraint ftv_types
  let local_tyvars = dtv_types Set.\\ ftv_gamma
  
  {-print =<< runPpr (do fv <- mapM pprTyCon $ Set.toList ftv_gamma
                       fvt <- mapM pprTyCon $ Set.toList ftv_types
                       bv <- mapM pprTyCon $ Set.toList local_tyvars
                       c <- pprContext reduced_constraint
                       ts <- mapM uShow types
                       return $
                         fsep fv $$ fsep fvt $$ fsep bv $$ c $$
                         text "Functions" <+> vcat ts)-}

  -- Determine which constraints to generalize over
  (retained, deferred) <-
    splitConstraint reduced_constraint ftv_gamma local_tyvars

  -- print_retained_constraints local_tyvars ftv_gamma retained -- DEBUG
  let ok_constraint (IsInst {}) = True
      ok_constraint (IsEqual {}) = True
      ok_constraint _ = False
  when (not $ all ok_constraint retained) $
    internalError "generalize: Unexpected constraints"
  
  -- Create type schemes
  schemes <- mapM (generalizeType local_tyvars retained) inferred_types
  
  return (deferred, local_tyvars, retained, schemes)
  where
    -- Generalize one type to a type scheme
    generalizeType local_tyvars retained (explicit_qvars, fot) = do
      -- Which type variables should be quantified over?  This will be a subset
      -- of 'local_tyvars'.
      ftv <- freeTypeVariables fot
      dtv1 <- dependentTypeVariables retained ftv

      -- Must not quantify over type variables bound in the surrounding
      -- environment
      let dtv = dtv1 `Set.intersection` local_tyvars

      -- Ensure that we respect user-specified 'forall' annotations
      case explicit_qvars of
        Nothing ->
          -- If no explicit type variables are given, then do not parameterize
          -- over any rigid type variables
          if any isRigidTyVar $ Set.toList dtv
          then fail "Type is less polymorphic than expected"
          else return ()
        Just x_dtv ->
          -- Parameterize over a subset of the explicit type variables
          if dtv `Set.isSubsetOf` Set.fromList x_dtv
          then return ()
          else fail "Type is more polymorphic than expected"

      -- Retained constraints must only mention these type variables
      r_ftv <- freeTypeVariables retained
      unless (r_ftv `Set.isSubsetOf` dtv) $
        fail "Ambiguous type variable in constraint"

      return $ TyScheme (Set.toList dtv) retained fot

    -- Print some debugging information
    print_retained_constraints local_tyvars ftv_gamma retained = do
      doc <- runPpr $ do
        dtvs <- mapM pprTyCon $ Set.toList local_tyvars
        gamma <- mapM pprTyCon $ Set.toList ftv_gamma
        ctx <- pprContext retained
        let rigids = fsep [parens $ dtv <+> if isRigidTyVar v
                                            then text "rigid"
                                            else text "flexible"
                          | (dtv, v) <- zip dtvs (Set.toList local_tyvars)]
        return $ text "F" <+> sep dtvs $$ rigids $$ text "G" <+> sep gamma $$ ctx
      putStrLn "Retained"
      print doc

-- | Add some recursively defined variables to the environment.  The variables
-- are assigned new type variables.  Each variable is associated with a 
-- placeholder.
--
-- The new type variables are recorded as part of the monad's output, as are
-- any placeholder expressions that are used.
addRecVarsToEnvironment :: [Variable] -> Inf a -> Inf (a, [TyCon])
addRecVarsToEnvironment vars k = do
  (assignments, tyvars) <- liftIO $ mapAndUnzipM recursiveAssignment vars
  x <- foldr (uncurry assume) k $ zip vars assignments
  
  -- Add new type variables and placeholders to the output
  Inf $ \_ -> return ([], Set.fromList tyvars, [], (x, tyvars))

-- | An assignment of named proof objects to predicates
type ProofBinding = [(Predicate, TIPat)]

lookupProofParam :: Predicate -> ProofBinding -> IO (Maybe TIPat)
lookupProofParam p ((p', pat):bs) = uEqual p p' >>= continue
  where
    continue False = lookupProofParam p bs
    continue True  = return (Just pat)
    
lookupProofParam _ [] = return Nothing

generalizeDefGroup :: Bool
                   -> SourcePos
                   -> [Variable]
                   -> Inf [(SourcePos, Maybe [TyCon], TIFun, HMType)]
                   -> ([TIFun] -> Inf a) -> Inf a
generalizeDefGroup is_top_level
                   source_pos
                   defgroup_vars 
                   scan_defgroup 
                   use_defgroup = Inf $ \env -> do
  -- Run the computation to get first-order types
  (constraint, unbound_vars, placeholders, (inferred_functions, new_tyvars)) <-
    runInf (addRecVarsToEnvironment defgroup_vars scan_defgroup) env

  -- Unify the assumed type of each function with its inferred type
  let inferred_fotypes = [ty | (_, _, _, ty) <- inferred_functions]
  constraint_1 <- unify_inferred_types inferred_fotypes new_tyvars

  -- Generalize these types
  let inferred_types = [(qvars, ty) | (_, qvars, _, ty) <- inferred_functions]
  (deferred, bound_vars, retained, schemes) <- 
    generalize env (constraint_1 ++ constraint) inferred_types

  -- DEBUG: Print generalized types
  when debug_generalize $ do
    schemes_doc <- runPpr $ mapM pprTyScheme schemes
    putStrLn "Generalized type schemes:"
    print $ nest 2 $ vcat schemes_doc

  -- If this is a top-level definition group,
  -- deferred constraints aren't allowed
  when (is_top_level && not (null deferred)) $ do
    pred_text <- runPpr $ pprContext deferred
    fail $ "Unresolved constraints in top-level binding:\n" ++ show pred_text

  -- Create proof objects
  (proof_env, proof_params) <- constraintToProofEnvironment retained
  
  -- Create generalized functions
  let fo_functions = [f | (_, _, f, _) <- inferred_functions]
      positions = [p | (p, _, _, _) <- inferred_functions]
  functions <-
    zipWithM3 (makePolymorphicFunction proof_params) positions schemes fo_functions
  
  -- Add generalized functions to environment
  let system_f_vars = map get_system_f_var defgroup_vars
        where
          get_system_f_var v =
            case varSystemFVariable v
            of Just sfvar -> sfvar
               Nothing    -> internalError "Variable has no System F translation"
      -- Create an expression for a use of a function name
      system_f_exprs = map (\v pos -> mkVarE pos v)  system_f_vars
      
      body_env = foldr (uncurry Map.insert) env $
                 zip defgroup_vars $
                 zipWith polymorphicAssignment schemes system_f_exprs

  -- Resolve placeholders
  unresolved_placeholders <-
    resolvePlaceholders proof_env body_env placeholders

  -- If this is a top-level definition group,
  -- all placeholders must be resolved
  when (is_top_level && not (null unresolved_placeholders)) $ do
    printUnresolvedPlaceholders unresolved_placeholders
    fail "Unresolved placeholders in top-level binding"
  
  -- Run body of computation in the extended environment
  (body_cst, body_unbound_vars, body_placeholders, x) <-
    runInf (use_defgroup functions) body_env

  -- Return
  let ret_placeholders = unresolved_placeholders ++ body_placeholders
      ret_cst = deferred ++ body_cst
      ret_unbound_vars = Set.union body_unbound_vars 
                                   (unbound_vars Set.\\ bound_vars)

  return (ret_cst, ret_unbound_vars, ret_placeholders, x)
  where
    debug_generalize = False
    unify_inferred_types inferred_types assumed_vars =
      liftM concat $
      zipWithM (unify source_pos) inferred_types (map ConTy assumed_vars)
      
resolvePlaceholders :: ProofEnvironment -- ^ Proof values
                    -> Environment
                       -- ^ Type assignments for recursive variables
                    -> Placeholders    -- ^ Placeholders to resolve
                    -> IO Placeholders -- ^ Unresolved placeholders
resolvePlaceholders proof_env rec_env placeholders =
  resolve [] placeholders
  where
    -- Resolve one placeholder at a time
    resolve :: Placeholders -> Placeholders -> IO Placeholders
    resolve deferred (ph:phs) = do
      b <- isResolved ph
      if b then resolve deferred phs else
        case ph
        of RecVarPH {phExpVariable = variable, phExpTyVar = tyvar} ->
             resolveRecVar variable tyvar
           DictPH {phExpPredicate = prd} ->
             resolveDict prd
           _ -> internalError "resolvePlaceholder"
      where
        -- The position of the source code that generated this placeholder
        source_pos = getSourcePos $ phExpInfo ph
        
        -- Actions to perform at the end of resolving a placeholder
        continue = resolve deferred phs
        continue_subgoals new_phs = resolve deferred (new_phs ++ phs)
        defer = resolve (ph:deferred) phs
        defer_subgoals new_phs = resolve (new_phs ++ deferred) phs
        
        -- Replace a recursive variable reference with an expression.  Create
        -- the expression in the same way we would instantiate a variable.
        resolveRecVar variable tyvar =
          case Map.lookup variable rec_env
          of Nothing  -> defer
             Just (RecursiveAssignment {}) ->
               -- Recursive variable has not been resolved yet
               defer

             Just ass -> do
               -- Instantiate the assignment.
               --
               -- Ignore the constraint that is created; because generalization
               -- restricts functions to be monomorphic and to have the same 
               -- contexts, all these constraints will be redundant.
               -- Also ignore new type variables, since they will immediately 
               -- be unified with another type.
               (new_placeholders, _, _, fot, new_exp) <-
                 instantiateTypeAssignment source_pos ass
               
               -- Unify with actual type
               unify source_pos fot (ConTy tyvar)
               
               -- Save the new expression as the placeholder's elaborated value
               setPlaceholderElaboration ph new_exp
               
               -- Add newly created placeholders to the list 
               continue_subgoals new_placeholders
        
        resolveDict prd = do
          -- Get a proof of this predicate
          (progress, new_placeholders, proof) <- prove source_pos proof_env prd
          
          -- If no progress was made, then defer the placeholder until it can
          -- be resolved
          if not progress then defer else do
            -- Record the new code
            setPlaceholderElaboration ph proof
            
            -- Defer the new placeholders (they were not found in
            -- the environment)
            defer_subgoals new_placeholders

    resolve deferred [] = return deferred

makePolymorphicFunction :: ProofBinding -- ^ Names of proof objects
                        -> SourcePos    -- ^ Function definition location
                        -> TyScheme     -- ^ Function's type scheme
                        -> TIFun    -- ^ First-order part of function
                        -> IO TIFun -- ^ Polymorphic function
makePolymorphicFunction
  proofs pos (TyScheme qvars cst fot)
  fo_function@(TIFun fun_info [] fo_params ret_type body) = do
      -- Convert type parameters
      ty_params <- mapM convertTyParam qvars
      -- Convert dictionary parameters
      prd_params <- mapM getProofParam cst
      
      let params = prd_params ++ fo_params
      return $ TIFun fun_info ty_params params ret_type body
      {- This is the old code, which produced nested functions.
      -- Instead, we add parameters to the first-order function.
  | null cst = 
      -- If there are only type parameters, add them to the function 
      addTypeParameters fo_function
  | otherwise = do
      -- Convert type parameters
      ty_params <- mapM convertTyParam qvars
      -- Convert dictionary parameters
      prd_params <- mapM getProofParam cst
      -- Create a new function with these parameters.  The new function 
      -- returns the original function
      let fun_body = mkFunE pos (TIFun fo_function)
          return_type = convertHMType fot
          info = SystemF.funInfo fo_function
      return $ TIFun $ SystemF.Fun info ty_params prd_params return_type fun_body-}
  where
    convertTyParam ty_param = do
      v <- tyVarToSystemF ty_param
      let k = convertKind $ tyConKind ty_param
      return $ TITyPat v k

    getProofParam prd = do
      mpat <- lookupProofParam prd proofs
      case mpat of
        Nothing -> do
          internalError "Cannot find proof variable"
        Just p  -> return p

makePolymorphicFunction _ _ _ _ =
  -- The argument function must not have type parameters
  internalError "makePolymorphicFunction"

-- | Construct the proof environment corresponding to a constraint.

constraintToProofEnvironment :: Constraint 
                             -> IO (ProofEnvironment, ProofBinding)
constraintToProofEnvironment cst = do
  (proofs, bindings) <- mapAndUnzipM convert cst
  return (ProofEnvironment $ concat proofs, bindings)
  where
    -- Create a dictionary expression for each predicate in the context
    -- and its superclasses.
    -- Create a binding for each predicate in the context. 
    -- The superclasses do not need bindings; they're derived from their 
    -- subclass.
    convert prd = do
      -- Create a variable to hold the proof object
      v_id <- withTheNewVarIdentSupply supplyValue
      let v = mkAnonymousVar v_id ObjectLevel

      -- Create a variable binding to pass it as a parameter
      let binding = (prd, mkVarP v (convertPredicate prd))

      -- The proof object is just the variable
      let proof_value = mkVarE noSourcePos v
      let proof_assoc = (prd, proof_value)

      -- Get superclass proof objects
      ProofEnvironment superclasses <-
        superclassDictionaries noSourcePos prd proof_value
      
      return (proof_assoc : superclasses, binding)

-- | Given a class dictionary, get expressions for class dictionaries 
--   of all its superclasses
superclassDictionaries :: SourcePos -> Predicate -> TIExp
                       -> IO ProofEnvironment
superclassDictionaries pos (IsInst ty cls) dict = do
  -- Get the actual class constraint for this type
  constraint <- instantiateClassConstraint (clsSignature cls) ty

  -- Construct a case expression to get the class's fields
  make_case_statement <- mkCaseOfDict pos cls ty dict

  -- Construct a dictionary expression for each immediate superclass.
  -- Each constraint is a member of the class.
  superclass_env <- forM (zip [0..] constraint) $ \(i, prd) -> do
    (expression, ()) <-
      make_case_statement $ \sc_vars _ ->
      return (mkVarE pos (sc_vars !! i), ())

    return (prd, expression)

  -- Transitively get all superclasses of each superclass in the constraint
  transitive_superclasses <-
    liftM mconcat $
    forM superclass_env $ \(sc_prd, sc_dict) ->
      superclassDictionaries pos sc_prd sc_dict

  return (ProofEnvironment superclass_env `mappend` transitive_superclasses)

-- Equality constraints have no superclasses
superclassDictionaries pos (IsEqual t1 t2) dict = return mempty

inferDefGroup :: Bool -> [FunctionDef] -> ([TIDef] -> Inf a) -> Inf a
inferDefGroup is_top_level defs k =
  let (first_def:_) = defs
      source_pos = getSourcePos first_def
      defgroup_vars = [v | FunctionDef v _ <- defs]
  in generalizeDefGroup is_top_level source_pos defgroup_vars
     infer_defgroup infer_body
  where
    infer_defgroup = mapM infer_function defs
    
    infer_function (FunctionDef _ f@(Function { funQVars = qvars
                                              , funParameters = params
                                              , funBody = body
                                              , funReturnType = rt})) = do
      (fun, ty) <-
        inferFunctionFirstOrderType (getSourcePos f) params body rt
      return (getSourcePos f, qvars, fun, ty)

    infer_body functions = do
      sfdefs <- zipWithM convert_def defs functions
      k sfdefs
    
    convert_def (FunctionDef v _) function = do
      sfvar <- case varSystemFVariable v
               of Just sfvar -> return sfvar 
                  Nothing -> internalError "Variable has no System F translation"
      return $ TIDef sfvar (SystemF.defaultDefAnn) function

-- | Infer an expression's type and parameter-passing convention
inferExpressionType :: Expression -> Inf (TIExp, HMType)
inferExpressionType expression 
  | not debug_inference = inferExpressionType' expression
  | otherwise = do
    ret@(e', t) <- inferExpressionType' expression
    t_doc <- liftIO $ runPpr $ uShow t
    let message = text "Expression has type" <+> t_doc $$
                  nest 4 (pprExpression expression)
    liftIO $ print message
    return ret
  where
    debug_inference = False

inferExpressionType' expression =
  case expression
  of VariableE {expVar = v} ->
       instantiateVariable pos v
     LiteralE {expLit = l} ->
       let ty = case l
                of IntL _ -> ConTy $ tiBuiltin the_con_int
                   FloatL _ -> ConTy $ tiBuiltin the_con_float
                   BoolL _ -> ConTy $ tiBuiltin the_con_bool
                   NoneL -> ConTy $ tiBuiltin the_con_NoneType
       in return (mkLitE pos l, ty)
     UndefinedE {} -> do
       tyvar <- liftIO $ newTyVar Star Nothing
       let ty = ConTy tyvar
       requirePassable ty
       return (mkUndefinedE pos (convertHMType ty), ty)
     TupleE {expFields = fs} -> do
       (f_exps, f_tys) <- inferExpressionTypes fs
       let -- Create the tuple expression
           tuple_con = SystemF.tupleCon $ length f_tys
           f_tys' = map convertHMType f_tys
           tuple_expr = mkConE pos tuple_con f_tys' [] f_exps
       return (tuple_expr, tupleType f_tys)
     ListE {expElements = []} -> do
       -- Empty list
       -- Create a type variable to stand for the list contents
       ltype <- liftIO $ newTyVar Star Nothing
       requirePassable (ConTy ltype)

       let list_type = ConTy (tiBuiltin the_con_list) `appTy` ConTy ltype
       return (mkListE pos (convertHMType $ ConTy ltype) [], list_type)
     ListE {expElements = fs} -> do
       -- Infer element types
       (first_exp : tail_exps, first_ty : tail_tys) <- inferExpressionTypes fs

       -- All elements must have the same type.  Coerce list elements.
       tail_exps' <- zipWithM (\e t -> unifyAndCoerceInf pos e first_ty t) tail_exps tail_tys

       let -- Create the list expression
           list_type = ConTy (tiBuiltin the_con_list) `appTy` first_ty
           list_exp = mkListE pos (convertHMType first_ty) (first_exp : tail_exps')
       return (list_exp, list_type)
     CallE {expOperator = op, expOperands = args} -> do
       (op_exp, op_ty) <- inferExpressionType op
       (arg_exps, arg_tys) <- inferExpressionTypes args
       
       -- Create the expected function type based on the inferred argument 
       -- types
       result_var <- liftIO $ newTyVar Star Nothing
       let result_type = ConTy result_var
           function_type = functionType arg_tys result_type
       requirePassable result_type
       
       -- Unify expected function type with actual function type
       co_op_exp <- unifyAndCoerceInf pos op_exp function_type op_ty
       
       return (mkPolyCallE pos co_op_exp [] arg_exps, result_type)
     IfE {expCondition = cond, expIfTrue = tr, expIfFalse = fa} -> do
       (cond_exp, cond_ty) <- inferExpressionType cond
       
       -- Check that condition has type 'bool'
       co_cond_exp <-
         unifyAndCoerceInf pos cond_exp (ConTy $ tiBuiltin the_con_bool) cond_ty
              
       (tr_exp, tr_ty) <- inferExpressionType tr
       (fa_exp, fa_ty) <- inferExpressionType fa
       
       -- True and false paths must have same type and passing convention
       co <- unifyInf False pos tr_ty fa_ty
       co_fa_exp <- liftIO $ applyCoercion co fa_exp
       return (mkIfE pos co_cond_exp tr_exp co_fa_exp, tr_ty)
     FunE {expFunction = f} -> do
       (fun_exp, fun_ty) <- inferLambdaType f
       return (mkFunE pos fun_exp, fun_ty)
     LetE {expPattern = p, expArgument = rhs, expBody = body} -> do
       (rhs_exp, rhs_ty) <- inferExpressionType rhs
       addParameterToEnvironment p $ \pat param_ty -> do
         -- Unify parameter type with RHS type
         co_rhs_exp <- unifyAndCoerceInf pos rhs_exp param_ty rhs_ty

         -- Scan body
         (body_exp, body_ty) <- inferExpressionType body
         return (mkLetE pos pat co_rhs_exp body_exp, body_ty)
     LetrecE {expDefinitions = defs, expBody = body} ->
       inferDefGroup False defs $ \defs' -> do
         (body_exp, body_ty) <- inferExpressionType body
         return (mkLetrecE pos defs' body_exp, body_ty)

     TypeAssertE {expVar = check_var, expType = t, expBody = body} -> do
       -- Unify check_var type with t
       (_, v_type) <- instantiateVariable pos check_var
       co <- unifyInf False pos t v_type

       -- Type assertion is removed from the appear in output
       inferExpressionType body
  where
    pos = getSourcePos expression

inferExpressionTypes :: [Expression] -> Inf ([TIExp], [HMType])
inferExpressionTypes = mapAndUnzipM inferExpressionType

-- | Infer the type of a lambda function.  The function has no type variables.
inferLambdaType :: Function -> Inf (TIFun, HMType)
inferLambdaType f@(Function { funQVars = qvars
                            , funParameters = params
                            , funReturnType = rt
                            , funBody = body}) = do
  unless (isNothing qvars) $ internalError "Lambda function has type parameters"
  inferFunctionFirstOrderType (getSourcePos f) params body rt

-- | Infer the type and calling convention of a first-order function
inferFunctionFirstOrderType :: SourcePos
                            -> [Pattern]
                            -> Expression
                            -> Maybe HMType
                            -> Inf (TIFun, HMType)
inferFunctionFirstOrderType pos params body annotated_return_type =
  addParametersToEnvironment params $ \sf_params param_types -> do
    
    (co_body, rtype) <- do
      (body, body_type) <- inferExpressionType body

      -- If a return type was annotated, coerce to the return type
      case annotated_return_type of
        Nothing -> return (body, body_type)
        Just t  -> do co_body <- unifyAndCoerceInf pos body t body_type
                      return (co_body, t)

    let f_type = functionType param_types rtype
    f <- liftIO $ mkFunction pos [] sf_params (convertHMType rtype) co_body
    return (f, f_type)

-- | Bind a list of parameters with first-order types over a local scope.
-- The System F parameters and their types are passed to the local scope.
addParametersToEnvironment
  :: [Pattern]
  -> ([TIPat] -> [HMType] -> Inf a)
  -> Inf a
addParametersToEnvironment (p:ps) k =
  addParameterToEnvironment p $ \pat ty ->
  addParametersToEnvironment ps $ \pats tys ->
  k (pat:pats) (ty:tys)

addParametersToEnvironment [] k = k [] []

addParameterToEnvironment :: Pattern 
                          -> (TIPat -> HMType -> Inf a) 
                          -> Inf a
addParameterToEnvironment pattern k =
  case pattern
  of WildP _ -> do
       -- Create a new type for this parameter
       ty <- liftIO $ liftM ConTy $ newTyVar Star Nothing
       requirePassable ty
       k (mkWildP (convertHMType ty)) ty
     VariableP _ v mty -> do
       -- Get or create this parameter's type
       ty <- case mty
             of Nothing -> liftIO $ liftM ConTy $ newTyVar Star Nothing
                Just ty -> return ty
       requirePassable ty
       sfvar <- case varSystemFVariable v
                of Just sfvar -> return sfvar
                   Nothing    -> internalError "Pattern variable has no translation"
       let ty_assignment = firstOrderAssignment ty (\pos -> mkVarE pos sfvar)
       assume v ty_assignment $
         k (mkVarP sfvar (convertHMType ty)) ty
     TupleP _ fields -> do
       -- Bind variables in each field
       addParametersToEnvironment fields $ \fields' field_types -> do
         -- Construct the tuple type
         let tuple_type = tupleType field_types
         k (mkTupleP fields') tuple_type

-- | Infer the type of an export statement.  Generate a function that wraps
-- the variable.
inferExportType :: Export -> Inf TIExport
inferExportType (Export { exportAnnotation = ann
                        , exportSpec = espec
                        , exportVariable = var
                        , exportType = ty}) = do
  -- Type must be a monomorphic function type
  failIfPolymorphic pos ty
  (dom, rng) <- do
    ty' <- liftIO $ uncurryTypeApplication ty
    case ty' of
      (FunTy _, args) -> return (init args, last args)
      _ -> fail "Exported variable is not a function"

  inst_exp <- instantiate_export_var pos var ty
  
  -- Create a variable for each parameter
  param_var_ids <- liftIO $ withTheNewVarIdentSupply $ \var_supply -> replicateM (length dom) (supplyValue var_supply)
  let param_vars = [mkAnonymousVar n ObjectLevel | n <- param_var_ids]

  -- Create a new function that calls the exported variable
  let call_args = map (mkVarE pos) param_vars
      call_exp = mkPolyCallE pos inst_exp [] call_args
      params = zipWith mkVarP param_vars (map convertHMType dom)
  wrapper_fun <- liftIO $ mkFunction pos [] params (convertHMType rng) call_exp
  
  return $ mkExport pos espec wrapper_fun
  where
    pos = case ann of Ann pos -> pos
                      
    -- Instantiate an exported variable
    instantiate_export_var pos var ty = Inf $ \env -> do
      (cst, tyvars, placeholders, x) <-
        runInf (instantiateExportedVariable pos var ty) env
      
      -- Reduce the constraints, so that type variables get unified as a result
      -- of equality constraints.
      -- Afterward, discard the constraints.  We don't have constraints 
      -- after reduction is complete because the type is monomorphic.
      _ <- reduceContext cst

      -- Resolve placeholders.  All placeholders should be resolved.
      unresolved_placeholders <- resolvePlaceholders mempty env placeholders
      unless (null unresolved_placeholders) $ do
        printUnresolvedPlaceholders unresolved_placeholders
        internalError "Unresolved placeholders in export expression"
      
      return ([], tyvars, [], x)

-- | Instantiate an exported function variable to a monotype.
--   Return the instantiated expression.
instantiateExportedVariable :: SourcePos -> Variable -> HMType -> Inf TIExp
instantiateExportedVariable pos var export_type = Inf $ \env -> do
  -- Instantiate at the given exported type
  (constraint, unbound_vars, placeholders, inst_exp) <- flip runInf env $ do
    (exp, var_type) <- instantiateVariable pos var
    unifyAndCoerceInf pos exp var_type export_type

  -- Generalize the type to a type scheme.  It will be a monomorphic type
  -- scheme.  Nevertheless, this step is required becasue it does context
  -- reduction and defaulting.
  (deferred, local_tyvars, retained, [inst_scheme]) <-
    generalize env constraint [(Nothing, export_type)]

  -- Debugging output
  {- doc <- runPpr $ pprTyScheme inst_scheme
  print "Exported function scheme"
  print doc -}

  -- Verify that generalized scheme is monomorphic
  unless (null retained) $
    fail "Exported function must not be polymorphic"

  -- These should be impossible because the exported type is monomorphic
  unless (Set.null local_tyvars) $
    internalError "Exported function has free type variables after type inference"
  unless (null deferred) $
    internalError "Exported function has deferred constraints"

  return ([], unbound_vars, placeholders, inst_exp)

inferModuleTypes :: Module -> Inf (ModuleName, [SystemF.DefGroup TIDef], [TIExport])
inferModuleTypes (Module module_name defss exports) = do
  (defss', exports') <- inferDefGroups defss
  return (module_name, defss', exports')
  where
    inferDefGroups (defs:defss) =
      inferDefGroup True defs $ \defs' -> do
        (defss', exports') <- inferDefGroups defss
        return (SystemF.Rec defs':defss', exports')
    inferDefGroups [] = do 
      exports' <- mapM inferExportType exports
      return ([], exports')

-- | The type environment for all global variables
buildGlobalEnvironment :: IO Environment
buildGlobalEnvironment = do
  assocs <- mapM getTypeAssignment allBuiltinGlobals
  return $ Map.fromList assocs
  where
    getTypeAssignment v = do
      is_empty <- isEmptyMVar $ varTranslation v
      when is_empty $ internalError "Built-in variable has no type"
      tr <- readMVar $ varTranslation v
      return (v, tr)

doTypeInference :: Inf a -> IO a
doTypeInference m = do
  env <- buildGlobalEnvironment
  (_, unbound_vars, _, x) <- runInf m env
  
  -- Any unbound variables that haven't been unified shall now be converted
  -- to an Any type
  mapM_ defaultFreeVariable $ Set.toList unbound_vars

  return x
  where
    -- Free variables default to 'any'.
    -- Defaulting does not produce constraints.
    defaultFreeVariable v = do
      b <- isCanonicalTyVar v
      if b
        then unify noSourcePos (ConTy v) (AnyTy $ tyConKind v)
        else return []

typeInferModule :: Module -> IO (SystemF.Module SystemF.SF)
typeInferModule m = do
  -- Run type inference
  ti_module <- doTypeInference $ inferModuleTypes m
  
  -- Force evaluation of all IO stuff
  evalTypeInferenceResult ti_module
