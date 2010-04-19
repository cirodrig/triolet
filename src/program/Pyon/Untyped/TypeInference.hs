
module Pyon.Untyped.TypeInference
       (typeInferModule)
where

import Control.Concurrent.MVar
import Control.Monad
import Control.Monad.Trans
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set
import Text.PrettyPrint.HughesPJ

import Gluon.Common.Error
import Gluon.Common.Label
import Gluon.Common.SourcePos
import qualified Gluon.Core
import Pyon.Globals
import qualified Pyon.SystemF.Syntax as SystemF
import qualified Pyon.SystemF.Builtins as SystemF
import Pyon.Untyped.Builtins
import Pyon.Untyped.Data
import Pyon.Untyped.Syntax
import Pyon.Untyped.HMType
import Pyon.Untyped.CallConv
import Pyon.Untyped.Kind
import Pyon.Untyped.GenSystemF
import Pyon.Untyped.Unification
import Pyon.Untyped.Classes
import Pyon.Untyped.TypeAssignment
import Pyon.Untyped.TypeInferenceEval

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

-------------------------------------------------------------------------------
-- The type inference monad

newtype Inf a =
  Inf {runInf :: Environment -> IO (Constraint, TyVarSet, Placeholders, a)}

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
withEnvironment f = Inf $ infReturn <=< f

assume :: Variable -> TypeAssignment -> Inf a -> Inf a
assume v assignment (Inf f) = Inf $ f . Map.insert v assignment

-- | Unify in the Inf monad.  Generated constraints are added to the context.
unifyInf :: Unifiable a => SourcePos -> a -> a -> Inf ()
unifyInf pos x y = Inf $ \_ -> do
  c <- unify pos x y
  return (c, Set.empty, [], ())

-- | Add a predicate to the context
requirePredicate :: Predicate -> Inf ()
requirePredicate p = require [p]

-- | Require the given type to have a parameter-passing convention
requirePassable :: HMType -> Inf ()
requirePassable ty = do 
  require [ty `HasPassConv` TypePassConv ty]

-- | Add a constraint to the context
require :: Constraint -> Inf ()
require c = Inf $ \_ -> return (c, Set.empty, [], ())

-------------------------------------------------------------------------------
-- Environments

-- | An environment assigns types and System F translations to variables
type Environment = Map.Map Variable TypeAssignment

-- | Get all free, unifiable type variables from the environment
ftvEnvironment :: Environment -> IO TyVarSet
ftvEnvironment env =
  liftM Set.unions $ mapM assignedFreeVariables $ Map.elems env

-- | Instantiate a variable
instantiateVariable :: SourcePos -> Variable -> Inf (TIExp, HMType, PassConv)
instantiateVariable pos v = Inf $ \env ->
  case Map.lookup v env
  of Nothing  -> internalError $
                 "No type for variable " ++ maybe "" showLabel (varName v)
     Just ass -> do
       (placeholders, vars, constraint, ty, val) <-
         instantiateTypeAssignment pos ass
         
       -- There must be a parameter passing convention for this type
       let cst = ty `HasPassConv` TypePassConv ty

       return (cst:constraint, vars, placeholders, (val, ty, TypePassConv ty))

lookupTyScheme :: Variable -> Inf TyScheme
lookupTyScheme v = withEnvironment $ \env ->
  case Map.lookup v env
  of Nothing  -> internalError $
                 "No type for variable " ++ maybe "" showLabel (varName v)
     Just ass -> return $ assignedTyScheme ass

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
  
  -- Find free type variables.  Will generalize over type variables that are
  -- free in the inferred types, but not in the environment.
  ftv_types <- liftM Set.unions $ mapM freeTypeVariables types
  ftv_gamma <- ftvEnvironment env
  let local_tyvars = ftv_types Set.\\ ftv_gamma
  
  -- Determine which constraints to generalize over
  (retained, deferred, defaulted) <-
    splitConstraint constraint ftv_gamma local_tyvars
    
  -- Defaulting
  mapM_ defaultConstraint defaulted
  
  -- Create type schemes
  schemes <- mapM (generalizeType local_tyvars retained) inferred_types
  
  return (deferred, local_tyvars, retained, schemes)
  where
    -- Generalize one type to a type scheme
    generalizeType local_tyvars retained (explicit_qvars, fot) = do
      -- Which type variables should be quantified over?  This will be a subset
      -- of 'local_tyvars'.
      ftv <- freeTypeVariables fot

      -- Ensure that we respect user-specified 'forall' annotations
      case explicit_qvars of
        Nothing ->
          -- If no explicit type variables are given, then do not parameterize
          -- over any rigid type variables
          if any isRigidTyVar $ Set.toList ftv
          then fail "Type is less polymorphic than expected"
          else return ()
        Just x_ftv ->
          -- Parameterize over a subset of the explicit type variables
          if ftv `Set.isSubsetOf` Set.fromList x_ftv
          then return ()
          else fail "Type is more polymorphic than expected"
          
      -- Retained constraints must only mention these type variables
      r_ftv <- freeTypeVariables retained
      unless (r_ftv `Set.isSubsetOf` ftv) $
        fail "Ambiguous type variable in constraint"
      
      return $ TyScheme (Set.toList ftv) retained fot
  
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
type ProofBinding = [(Predicate, SystemF.Pat TI)]

lookupProofParam :: Predicate -> ProofBinding -> IO (Maybe (SystemF.Pat TI))
lookupProofParam p ((p', pat):bs) = uEqual p p' >>= continue
  where
    continue False = lookupProofParam p bs
    continue True  = return (Just pat)
    
lookupProofParam _ [] = return Nothing

generalizeDefGroup :: Bool
                   -> SourcePos
                   -> [Variable]
                   -> Inf [(SourcePos, Maybe [TyCon], SystemF.Fun TI, HMType, CallConv)]
                   -> ([SystemF.Fun TI] -> Inf a) -> Inf a
generalizeDefGroup is_top_level
                   source_pos
                   defgroup_vars 
                   scan_defgroup 
                   use_defgroup = Inf $ \env -> do
  -- Run the computation to get first-order types
  (constraint, unbound_vars, placeholders, (inferred_functions, new_tyvars)) <-
    runInf (addRecVarsToEnvironment defgroup_vars scan_defgroup) env

  -- Unify the assumed type of each function with its inferred type
  let inferred_fotypes = [ty | (_, _, _, ty, _) <- inferred_functions]
  constraint_1 <- unify_inferred_types inferred_fotypes new_tyvars
  
  -- Generalize these types
  let inferred_types = [(qvars, ty) | (_, qvars, _, ty, _) <- inferred_functions]
  (deferred, bound_vars, retained, schemes) <- 
    generalize env (constraint_1 ++ constraint) inferred_types

  -- If this is a top-level definition group,
  -- deferred constraints aren't allowed
  when (is_top_level && not (null deferred)) $
    fail "Unresolved constraints in top-level binding"

  -- Create proof objects
  (proof_env, proof_params) <- constraintToProofEnvironment retained
  
  -- Create generalized functions
  let fo_functions = [f | (_, _, f, _, _) <- inferred_functions]
      positions = [p | (p, _, _, _, _) <- inferred_functions]
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
  when (is_top_level && not (null unresolved_placeholders)) $
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
                        -> SystemF.Fun TI -- ^ First-order part of function
                        -> IO (SystemF.Fun TI) -- ^ Polymorphic function
makePolymorphicFunction proofs pos (TyScheme qvars cst fot) (TIFun fo_function)
  | not $ null $ SystemF.funTyParams fo_function =
      internalError "makePolymorphicFunction"
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
      return $ TIFun $ SystemF.Fun ty_params prd_params return_type fun_body
  where
    addTypeParameters f = do
      ty_params <- mapM convertTyParam qvars
      return $ TIFun $ fo_function {SystemF.funTyParams = ty_params}
      
    convertTyParam ty_param = do
      v <- tyVarToSystemF ty_param
      let k = convertKind $ tyConKind ty_param
      return $ SystemF.TyPat v k

    getProofParam prd = do
      mpat <- lookupProofParam prd proofs
      case mpat of
        Nothing -> do
          internalError "Cannot find proof variable"
        Just p  -> return p

constraintToProofEnvironment :: Constraint 
                             -> IO (ProofEnvironment, ProofBinding)
constraintToProofEnvironment cst = mapAndUnzipM convert cst
  where
    convert prd = do
      -- Create a variable to hold the proof object
      v_id <- getNextVarIdent
      let v = Gluon.Core.mkAnonymousVariable v_id Gluon.Core.ObjectLevel
      
      let exp = mkVarE noSourcePos v
          pat = mkVarP v (convertPredicate prd) 
      return ((prd, exp), (prd, pat))

inferDefGroup :: Bool -> [FunctionDef] -> ([SystemF.Def TI] -> Inf a) -> Inf a
inferDefGroup is_top_level defs k =
  let source_pos = getSourcePos $ head defs
      defgroup_vars = [v | FunctionDef v _ <- defs]
  in generalizeDefGroup is_top_level source_pos defgroup_vars
     infer_defgroup infer_body
  where
    infer_defgroup = mapM infer_function defs
    
    infer_function (FunctionDef _ f@(Function { funQVars = qvars
                                              , funParameters = params
                                              , funBody = body
                                              , funReturnType = rt})) = do
      (fun, ty, cc) <-
        inferFunctionFirstOrderType (getSourcePos f) params body rt
      return (getSourcePos f, qvars, fun, ty, cc)

    infer_body functions = do
      sfdefs <- zipWithM convert_def defs functions
      k sfdefs
    
    convert_def (FunctionDef v _) function = do
      sfvar <- case varSystemFVariable v
               of Just sfvar -> return sfvar 
                  Nothing -> internalError "Variable has no System F translation"
      return $ SystemF.Def sfvar function

-- | Infer an expression's type and parameter-passing convention
inferExpressionType :: Expression -> Inf (TIExp, HMType, PassConv)
inferExpressionType expression =
  case expression
  of VariableE {expVar = v} ->
       instantiateVariable pos v
     LiteralE {expLit = l} ->
       let ty = case l
                of SystemF.IntL _ -> ConTy $ tiBuiltin the_con_int
                   SystemF.FloatL _ -> ConTy $ tiBuiltin the_con_float
                   SystemF.BoolL _ -> ConTy $ tiBuiltin the_con_bool
                   SystemF.NoneL -> ConTy $ tiBuiltin the_con_NoneType
           -- All these literals are pass-by-value
           pc = ByVal
       in return (mkLitE pos l (convertHMType ty), ty, pc)
     UndefinedE {} -> do
       tyvar <- liftIO $ newTyVar Star Nothing
       let ty = ConTy tyvar
       requirePassable ty
       return (mkUndefinedE pos (convertHMType ty), ty, TypePassConv ty)
     TupleE {expFields = fs} -> do
       (f_exps, f_tys, f_pcs) <- inferExpressionTypes fs
       let pc = TuplePassConv f_pcs
       return (mkTupleE pos f_exps, tupleType f_tys, pc)
     CallE {expOperator = op, expOperands = args} -> do
       (op_exp, op_ty, op_conv) <- inferExpressionType op
       (arg_exps, arg_tys, arg_convs) <- inferExpressionTypes args
       
       -- Create the expected function type based on the inferred argument 
       -- types
       result_var <- liftIO $ newTyVar Star Nothing
       let result_type = ConTy result_var
           function_type = functionType arg_tys result_type
       requirePassable result_type
       
       -- Unify expected function type with actual function type
       unifyInf pos function_type op_ty
       
       -- Unify the parameter-passing conventions
       let result_pc = TypePassConv result_type
       let fun_return_conv = Return (PickExecMode result_type) result_pc
           fun_conv = ByClosure $ foldr (:+>) fun_return_conv arg_convs

       unifyInf pos op_conv fun_conv

       return (mkCallE pos op_exp arg_exps, result_type, result_pc)
     IfE {expCondition = cond, expIfTrue = tr, expIfFalse = fa} -> do
       (cond_exp, cond_ty, cond_pc) <- inferExpressionType cond
       
       -- Check that condition has type 'bool'       
       -- Once this is checked, we know that cond_pc will be ByVal
       unifyInf pos (ConTy $ tiBuiltin the_con_bool) cond_ty
              
       (tr_exp, tr_ty, tr_pc) <- inferExpressionType tr
       (fa_exp, fa_ty, fa_pc) <- inferExpressionType fa
       
       -- True and false paths must have same type and passing convention
       unifyInf pos tr_ty fa_ty
       unifyInf pos tr_pc fa_pc
       return (mkIfE pos cond_exp tr_exp fa_exp, tr_ty, tr_pc)
     FunE {expFunction = f} -> do
       (fun_exp, fun_ty, fun_cc) <- inferLambdaType f
       return (mkFunE pos fun_exp, fun_ty, ByClosure fun_cc)
     LetE {expPattern = p, expArgument = rhs, expBody = body} -> do
       (rhs_exp, rhs_ty, rhs_pc) <- inferExpressionType rhs
       addParameterToEnvironment p $ \pat param_ty param_pc -> do
         -- Unify parameter type with RHS type
         unifyInf pos param_ty rhs_ty
         unifyInf pos param_pc rhs_pc
         -- Scan body
         (body_exp, body_ty, body_pc) <- inferExpressionType body
         return (mkLetE pos pat rhs_exp body_exp, body_ty, body_pc)
     LetrecE {expDefinitions = defs, expBody = body} ->
       inferDefGroup False defs $ \defs' -> do
         (body_exp, body_ty, body_pc) <- inferExpressionType body
         return (mkLetrecE pos defs' body_exp, body_ty, body_pc)
  where
    pos = getSourcePos expression

inferExpressionTypes :: [Expression] -> Inf ([TIExp], [HMType], [PassConv])
inferExpressionTypes = mapAndUnzip3M inferExpressionType

-- | Infer the type of a lambda function.  The function has no type variables.
inferLambdaType :: Function -> Inf (SystemF.Fun TI, HMType, CallConv)
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
                            -> Inf (SystemF.Fun TI, HMType, CallConv)
inferFunctionFirstOrderType pos params body annotated_return_type =
  addParametersToEnvironment params $ \sf_params param_types param_pcs -> do
    (body, body_type, body_pc) <- inferExpressionType body
    
    -- If a return type was annotated, check against the return type
    case annotated_return_type of
      Nothing -> return ()
      Just t  -> unifyInf pos body_type t
      
    -- Compute the function's calling convention
    let return_cc = Return (PickExecMode body_type) body_pc
        f_cc = foldr (:+>) return_cc param_pcs

    let f_type = functionType param_types body_type
    f <- liftIO $ mkFunction [] sf_params (convertHMType body_type) body
    return (f, f_type, f_cc)

-- | Bind a list of parameters with first-order types over a local scope.
-- The System F parameters and their types are passed to the local scope.
addParametersToEnvironment
  :: [Pattern]
  -> ([SystemF.Pat TI] -> [HMType] -> [PassConv] -> Inf a)
  -> Inf a
addParametersToEnvironment (p:ps) k =
  addParameterToEnvironment p $ \pat ty pc ->
  addParametersToEnvironment ps $ \pats tys pcs ->
  k (pat:pats) (ty:tys) (pc:pcs)

addParametersToEnvironment [] k = k [] [] []

addParameterToEnvironment :: Pattern 
                          -> (SystemF.Pat TI -> HMType -> PassConv -> Inf a) 
                          -> Inf a
addParameterToEnvironment pattern k =
  case pattern
  of WildP _ -> do
       -- Create a new type for this parameter
       ty <- liftIO $ liftM ConTy $ newTyVar Star Nothing
       requirePassable ty
       k (mkWildP (convertHMType ty)) ty (TypePassConv ty)
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
         k (mkVarP sfvar (convertHMType ty)) ty (TypePassConv ty)
     TupleP _ fields -> do
       -- Bind variables in each field
       addParametersToEnvironment fields $ \fields' field_types field_pcs -> do
         -- Construct the tuple type
         let tuple_type = tupleType field_types
             tuple_pc = TuplePassConv field_pcs
         k (mkTupleP fields') tuple_type tuple_pc

inferExportType :: Export -> SystemF.Export
inferExportType (Export ann var) =
  case varSystemFVariable var
  of Nothing -> internalError "Cannot export variable"
     Just v  -> let pos = case ann
                          of Ann pos -> pos
                in SystemF.Export pos v

inferModuleTypes :: Module -> Inf (SystemF.Module TI)
inferModuleTypes (Module defss exports) = do
  defss' <- inferDefGroups defss
  let exports' = map inferExportType exports
  return $ SystemF.Module defss' exports'
  where
    inferDefGroups (defs:defss) =
      inferDefGroup True defs $ \defs' -> do
        defss' <- inferDefGroups defss
        return (defs':defss')
    inferDefGroups [] = return []

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
  -- to the special type 'Any'
  mapM_ defaultFreeVariable $ Set.toList unbound_vars

  return x
  where
    defaultFreeVariable v = do
      b <- isCanonicalTyVar v
      if b
        then unify noSourcePos (ConTy v) (ConTy $ tiBuiltin the_con_Any)
        else return []

typeInferModule :: Module -> IO SystemF.RModule
typeInferModule m = do
  -- Run type inference
  ti_module <- doTypeInference $ inferModuleTypes m
  
  -- Force evaluation of all IO stuff
  evalTypeInferenceResult ti_module