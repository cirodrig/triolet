{-| Demand analysis.

This is a backward analysis that annotates each variable binding with
how often and how it is used.

The analysis is a combination of inlining information described in
Simon Peyton Jones and Simon Marlow, \"Secrets of the Glasgow Haskell
Compiler inliner\", and use information described in Simon Peyton Jones and
Will Partain, \"Measuring the Effectiveness of a Simple Strictness Analyzer.\"
We do not use strictness information as in the latter paper, but we do use
information about how a value is deconstructed.
-}

{-# LANGUAGE TypeSynonymInstances, ViewPatterns, Rank2Types #-}
module SystemF.DemandAnalysis
       (altSpecificity,
        altListSpecificity,
        demandAnalysis,
        localDemandAnalysis)
where

import Prelude hiding(mapM, sequence)
  
import Control.Monad hiding(mapM, sequence)
import Control.Monad.Trans
import Control.Applicative
import Control.Monad.Reader.Class
import Control.Monad.Writer.Class
import qualified Data.Graph as Graph
import qualified Data.IntMap as IntMap
import qualified Data.Set as Set
import Data.List
import Data.Maybe
import Data.Traversable
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import Common.MonadLogic
import Common.Supply
import Builtins.Builtins
import SystemF.Demand
import SystemF.Syntax
import SystemF.MemoryIR
import SystemF.PrintMemoryIR
import Type.Environment
import Type.Eval
import qualified Type.Rename as Rename
import Type.Type
import GlobalVar
import Globals

-------------------------------------------------------------------------------
-- Demand analysis functions

-- | Demand analysis takes a reduced type environment as a parameter.
--   The type environment is only used to look up type and data constructors,
--   and compute kinds.  Value variables are never looked up in the environment.
--
--   For this reason, demand analysis only updates the type environment with 
--   type variables, not value variables.
--   
--   The analysis generates demand information on variables.
newtype Df a = Df {runDf :: TypeEvalM UnboxedMode (a, Dmds)}

returnDf :: a -> TypeEvalM UnboxedMode (a, Dmds)
returnDf x = return (x, bottom)

evalDf :: Df a -> IdentSupply Var -> ITypeEnvBase UnboxedMode -> IO a
evalDf m supply env = do
  env' <- thawTypeEnv env
  (x, _) <- runTypeEvalM (runDf m) supply env'
  return x

instance Functor Df where
  fmap = liftM

instance Applicative Df where
  pure = return
  (<*>) = ap

instance Monad Df where
  return x = Df (returnDf x)
  m >>= k = Df (do (x, dmd1) <- runDf m
                   (y, dmd2) <- runDf (k x)
                   return (y, joinSeq dmd1 dmd2))

instance MonadWriter Df where
  type WriterType Df = Dmds
  tell w = Df (return ((), w))
  listen m = Df (do (x, w) <- runDf m
                    return ((x, w), w))
  pass m = Df (do ((x, f), w) <- runDf m 
                  return (x, f w))

instance MonadIO Df where
  liftIO m = Df (liftIO m >>= returnDf)

instance TypeEnvMonad Df where
  type EvalBoxingMode Df = UnboxedMode
  getTypeEnv = Df (getTypeEnv >>= returnDf)
  liftTypeEnvM m = Df (liftTypeEnvM m >>= returnDf)

instance Supplies Df (Ident Var) where
  fresh = Df (fresh >>= returnDf)

instance EvalMonad Df where
  liftTypeEvalM m = Df (m >>= returnDf)

-- | Run multiple dataflow analyses on mutually exclusive execution paths.
--   This kind of execution occurs in case alternatives.
parallel :: [Df a] -> Df [a]
parallel dfs = Df $ do
  (xs, dmds) <- liftM unzip $ sequence $ map runDf dfs
  return (xs, joinPars dmds)

underLambda :: Multiplicity -> Bool -> Df a -> Df a
underLambda call_multiplicity is_called m =
  censor (lambdaAbstracted call_multiplicity is_called) m

-- | Demand analysis only deals with variables that can be removed from the 
--   program.  Global type variables (type functions and constructors) and
--   data constructor definitions cannot be removed, so they are ignored.
--   To decide whether a variable is ignored, look it up in the type
--   environment.
isDeletable :: Var -> Df Bool
isDeletable v = Df $ do
  deletable <-
    liftM isNothing (lookupDataType v) >&&>
    liftM isNothing (lookupDataCon v) >&&>
    liftM isNothing (lookupTypeFunction v)
  returnDf deletable

-- | A helper function for 'mention'.  If the variable is a global type or 
--   data constructor, then ignore it.
mentionHelper v dmd =
  ifM (isDeletable v)
  (tell $ useVariable v dmd)
  (return ())

mentionHelperList vs dmd = do
  used_variables <- filterM isDeletable vs
  tell $ useVariables used_variables dmd

-- | A variable was used somehow.  This is the most general case.
mention :: Var -> Df ()
mention v = mentionHelper v (Dmd OnceSafe Used, nonCallDmd)

-- | Mention a list of variables, behaving the same as 'mention'.
mentionList :: [Var] -> Df ()
mentionList vs = mentionHelperList vs (Dmd OnceSafe Used, nonCallDmd)

-- | A variable was used multiple times.  This prevents inlining.
--
--   We put 'Unused' as the specificity here to avoid contaminating the 
--   specificity information that we compute.
mentionMany :: Var -> Df ()
mentionMany v = mentionHelper v (Dmd ManySafe Unused, nonCallDmd)

-- | A variable was used with the given demand.
mentionVarDmd :: Var -> VarDmd -> Df ()
mentionVarDmd v d = mentionHelper v d

-- | A variable was used in a multiple-alternative case statement or \'copy\'
--   function.
mentionMultiCase :: Var -> Df ()
mentionMultiCase v = mentionHelper v (Dmd OnceSafe Inspected, nonCallDmd)

-- | A global variable is visible to external code.
mentionExtern :: Var -> Df ()
mentionExtern v = mentionHelper v (unknownDmd, nonCallDmd)

-- | Get the demand on variable @v@ produced by the given code; also, remove
--   @v@ from the demanded set
getDemand :: Var -> Df a -> Df (a, VarDmd)
getDemand v m = Df $ do
  (x, dmds) <- runDf m
  let dmd = lookupDmd v dmds
  let dmds' = IntMap.delete (fromIdent $ varID v) dmds
  dmd `seq` dmds' `seq` return ((x, dmd), dmds')

maskDemand :: Var -> Df a -> Df a
maskDemand v m = fmap fst $ getDemand v m

maskDemands :: [Var] -> Df a -> Df a
maskDemands vs m = Df $ do
  (x, dmds) <- runDf m
  let dmds' = foldr (\v m -> IntMap.delete (fromIdent $ varID v) m) dmds vs
  dmds' `seq` return (x, dmds')

-------------------------------------------------------------------------------
-- Demand analysis on Mem IR

-- | A computation that performs demand analysis, eliminates dead code,
--   minimizes recursive definition groups, and
--   annotates variable bindings with their demands in a piece of code.
type DmdAnl a = a -> Df a

-- | Get variables mentioned in a type.
--   The type is not changed by demand analysis.
dfType :: Type -> Df ()
dfType ty = mentionList $ Set.toList $ Rename.freeVariables ty

withManyBinders :: (forall b. a -> Df b -> Df (a, b))
                -> [a] -> Df c -> Df ([a], c)
withManyBinders one xs m = go xs
  where
    go (x:xs) = do
      (y, (ys, z)) <- one x $ go xs
      return (y : ys, z)
    
    go [] = fmap ((,) []) m

withTyBinder :: Binder -> Df a -> Df (Binder, a)
withTyBinder pat@(v ::: ty) m = do
  dfType ty
  x <- maskDemand v $ assume v ty m
  return (pat, x)

withTyBinders = withManyBinders withTyBinder

withTyPat :: TyPat -> Df a -> Df (TyPat, a)
withTyPat pat@(TyPat (v ::: ty)) m = do
  dfType ty
  x <- maskDemand v $ assume v ty m
  return (pat, x)

withTyPats = withManyBinders withTyPat

withMaybeParam :: Maybe PatM -> Df a -> Df (Maybe PatM, a)
withMaybeParam Nothing m = do
  x <- m
  return (Nothing, x)

withMaybeParam (Just p) m = do
  (new_p, x) <- withParam p m
  return (Just new_p, x)

withParam :: PatM -> Df a -> Df (PatM, a)
withParam pat m = do
  dfType $ patMType pat
  (x, (dmd, _)) <- getDemand (patMVar pat) m
  let new_pat = setPatMDmd dmd pat
  return (new_pat, x)

withParams :: [PatM] -> Df a -> Df ([PatM], a)
withParams = withManyBinders withParam

-- | Do demand analysis on an expression.
--   Given the demand on the expression's result, propagate demand information
--   through the expression.
dmdExp :: VarDmd -> DmdAnl ExpM
dmdExp dmd exp@(ExpM expression) =
  case expression
  of VarE _ v -> mentionVarDmd v dmd >> return exp
     LitE _ _ -> return exp
     ConE inf con sps ty_obj args -> dmdConE exp dmd inf con sps ty_obj args
     AppE inf op ts args -> dmdAppE inf dmd op ts args
     LamE inf f -> dmdLamE dmd inf f
     LetE inf pat rhs body -> dmdLetE dmd inf pat rhs body
     LetfunE inf dg body -> do
       -- Partition into minimal definition groups
       let fun_arity f = length $ funParams $ fromFunM f
       (dg', body') <- dmdGroup fun_arity dmdDef dg (dmdExp dmd body)
       let mk_let defgroup e = ExpM (LetfunE inf defgroup e)
       return $ foldr mk_let body' dg'
     CaseE inf scr sps alts -> dmdCaseE dmd inf scr sps alts
     ExceptE _ ty -> dfType ty >> return exp
     CoerceE inf t1 t2 e -> do
       dfType t1
       dfType t2
       e' <- dmdExp (coerced dmd) e
       return $ ExpM $ CoerceE inf t1 t2 e'
     ArrayE inf ty es -> do
       dfType ty
       es' <- mapM (dmdExp unknownVarDmd) es
       return $ ExpM $ ArrayE inf ty es'

{-
-- | Do demand analysis on an initializer function appearing in a data
--   constructor application, given how the expression's result is used.

dmdInitializer = dmdExpWorker True

dmdExpWorker :: Bool -> Specificity -> DmdAnl ExpM
dmdExpWorker is_initializer spc expressionM@(ExpM expression) =
  case expression
  of VarE _ v -> mentionSpecificity v spc >> return expressionM
     LitE _ _ -> return expressionM
     ConE inf con sps ty_obj args -> dmdConE inf con sps ty_obj args
     AppE inf op ts args -> dmdAppE inf op ts args
     LamE inf f -> do
       f' <- dmdFun is_initializer f
       return $ ExpM $ LamE inf f'
     LetE inf pat rhs body -> dmdLetE spc inf pat rhs body
     LetfunE inf dg body -> do
       (dg', body') <- dmdGroup dmdDef dg (dmdExp spc body)
       let mk_let defgroup e = ExpM (LetfunE inf defgroup e)
       return $ foldr mk_let body' dg'
     CaseE inf scr sps alts -> dmdCaseE spc inf scr sps alts
     ExceptE _ ty -> dfType ty >> return expressionM
     CoerceE inf t1 t2 e -> do
       dfType t1
       dfType t2
       e' <- dmdExp spc e
       return $ ExpM $ CoerceE inf t1 t2 e'
     ArrayE inf ty es -> do
       dfType ty
       es' <- mapM (dmdExp Used) es
       return $ ExpM $ ArrayE inf ty es'
  where
    {- -- Debugging output, show what was demanded in this expression
    trace_dmd m = do
      (x, dmd) <- listen m
      trace ("dmdExp\n" ++ show (pprExp expressionM) ++ "\n" ++
             intercalate "\n" [show v ++ " |-> " ++ showDmd d
                              | (v,d) <- IntMap.toList dmd])  $ return x
    -}
-}

dmdConE exp (dmd, _) inf con sps ty_obj args = do
  sps' <- mapM (dmdExp unknownVarDmd) sps
  ty_obj' <- mapM (dmdExp unknownVarDmd) ty_obj

  -- Propagate demand info to each field
  initializer_dmds <- deconstructSpecificity con (length args) dmd
  let dmd_doc (x, y) = pprDmd x <+> pprCallDmd y
  args' <- zipWithM dmdExp initializer_dmds args

  return $ ExpM $ ConE inf con sps' ty_obj' args'

-- | Dead code elimination for function application.
--
--   Perform dead code elimination on subexpressions as usual.
--   However, parameters that should be floated are marked as having
--   multiple uses so that they don't get inlined.
dmdAppE inf dmd op ty_args args = do
  let op_dmd = calleeDmd (length args) dmd
  op' <- dmdExp op_dmd op
  args' <- sequence [ dmdExp use_mode arg
                    | (use_mode, arg) <- zip use_modes args]
  --args' <- sequence $ zipWith3 dmdExpWorker call_modes use_modes args
  return $ ExpM $ AppE inf op' ty_args args'
  where
    -- This is a hack to ensure that arguments of 'blockcopy' are hoisted
    -- into a separate definition.  This hack should be fixed by hoisting 
    -- /all/ function arguments, but this requires further optimizer
    -- adjustments.
    use_modes =
      case op
      of ExpM (VarE _ op_var)
           | op_var == blockcopyV && n_args == 2 -> [u, c]
           | op_var == blockcopyV && n_args == 3 -> [u, c, u]
         _ -> repeat u
      where
        n_args = length args
        u = (Dmd ManyUnsafe Used, nonCallDmd)
        c = (Dmd ManyUnsafe Copied, nonCallDmd)

{-    -- This is a hack to allow inlining beneath the function argument
    -- of 'append_build_list'.  This is important to inline stream 
    -- expressions and enable stream rewriting.
    -- We really should generalize this to all 'called-at-most-once'
    -- functions.
    call_modes =
      case op
      of ExpM (VarE _ op_var)
           | op_var `isCoreBuiltin` The_append_build_list && length args >= 2 ->
               [False, True, False]
         _ -> repeat False -}

dmdLamE dmd inf f = do
  f' <- dmdFun dmd f
  return $ ExpM $ LamE inf f'

dmdLetE dmd inf binder rhs body = do
  (body', local_dmd) <- getDemand (patMVar binder) $ dmdExp dmd body
  case multiplicity (fst local_dmd) of
    Dead -> return body'        -- RHS is eliminated
    _ -> do
      rhs' <- dmdExp local_dmd rhs
      dfType (patMType binder)
      return $ ExpM $ LetE inf (setPatMDmd (fst local_dmd) binder) rhs' body'

dmdCaseE dmd inf scrutinee sps alts = do
  -- Get demanded values in each alternative
  alt_results <- parallel $ map (dmdAlt dmd) alts
  let alts' = map fst alt_results
      alts_spc = joinPars $ map snd alt_results

  -- If there's only one alternative and none of its fields are used, then
  -- eliminate the entire case statement
  case alts' of
    [AltM alt'] | null (deConExTypes $ altCon alt') &&
                  maybe True isDeadPattern (altTyObject alt') &&
                  all isDeadPattern (altParams alt') ->
      return $ altBody alt'
    _ -> do
      -- Process the scrutinee
      scrutinee' <- dmdExp (Dmd OnceSafe alts_spc, nonCallDmd) scrutinee
      sps' <- mapM (dmdExp unknownVarDmd) sps
      return $ ExpM $ CaseE inf scrutinee' sps' alts'

-- | Construct the specificity for a case scrutinee, based on how its value
--   is bound by a case alternative
altSpecificity :: AltM -> Specificity
altSpecificity (AltM alt) = Decond (altCon alt) fields
  where
    fields = map patMDmd $ altParams alt

-- | Construct the specificity for a case scrutinee, based on how its value
--   is bound by a list of alternatives.  If there's more than one alternative,
--   the specificity will be 'Inspected'.
altListSpecificity :: [AltM] -> Specificity
altListSpecificity []  = internalError "altListSpecificity: Empty list"
altListSpecificity [a] = altSpecificity a
altListSpecificity _   = Inspected

-- | Do demand analysis on a case alternative.  Return the demand on the
--   scrutinee.
dmdAlt :: VarDmd -> AltM -> Df (AltM, Specificity)
dmdAlt dmd (AltM (Alt (VarDeCon con ty_args ex_types) ty_ob_param params body)) = do
  mapM_ dfType ty_args
  (typats', (ty_ob_param', (pats', body'))) <-
    withTyBinders ex_types $
    withMaybeParam ty_ob_param $
    withParams params $
    dmdExp dmd body

  let new_alt = AltM $ Alt (VarDeCon con ty_args typats') ty_ob_param' pats' body'
  return (new_alt, altSpecificity new_alt)

dmdAlt dmd (AltM (Alt decon@(TupleDeCon _) Nothing params body)) = do
  (pats', body') <- withParams params $ dmdExp dmd body

  let new_alt = AltM (Alt decon Nothing pats' body')
  return (new_alt, altSpecificity new_alt)  

dmdFun :: VarDmd -> DmdAnl FunM
dmdFun dmd (FunM f) = do
  output_param_var <- liftTypeEvalM $ getOutputParameter (FunM f)

  -- Extract the demand on the function body
  let body_dmd = returnTypeDmd (length $ funParams f) output_param_var dmd

  -- Decide whether the function is work-safe.
  -- If this is an initializer and all uses are safe calls,
  -- then the function is work-safe.
  -- Otherwise, approximate as not work-safe.
  let old_is_safe =             -- No longer used
        case fst dmd 
        of Dmd m (Called 1 _ _)
             | isJust output_param_var && m == OnceSafe -> True
           _ -> False

  -- Is this function definitely called?
  let is_called = snd dmd `isCalledWithArity` length (funParams f)

  -- Eliminate dead code and convert patterns to wildcard patterns
  (tps', (ps', b')) <-
    underLambda (multiplicity $ fst dmd) is_called $
    withTyPats (funTyParams f) $
    withParams (funParams f) $ do
      dfType $ funReturn f
      dmdExp body_dmd (funBody f)
  return $ FunM $ f {funTyParams = tps', funParams = ps', funBody = b'}

-- | Decide whether this function takes an output parameter.
--   If a function's last parameter is an 'OutPtr' and its return type
--   is 'Store', return the output parameter.  Otherwise return Nothing.
getOutputParameter (FunM f)
  | null (funParams f) = internalError "getOutputParameter: No parameters"
  | otherwise =
    let p = last $ funParams f
    in cond ()
       [ do -- Parameter has type 'OutPtr t'?
            Just (op, _) <- lift $ deconVarAppType $ patMType p
            aguard $ op == outPtrV
        
            -- Return type has type 'Store'?
            VarT rtype_var <- lift $ reduceToWhnf $ funReturn f
            aguard $ rtype_var == storeV

            return (Just $ patMVar p)
       , return Nothing
       ]

dmdData (Constant inf ty e) = do
  e' <- dmdExp unknownVarDmd e
  dfType ty
  return $ Constant inf ty e'

dmdDef' :: DmdAnl (t Mem) -> DmdAnl (Def t Mem)
dmdDef' analyze_t def
  -- Wrapper functions may be inlined many times.
  -- Conservatively treat any use of a variable inside a wrapper as if it were many uses.
  | defIsWrapper def = censor replicatedCode analyze_def
  | otherwise        = analyze_def
  where
    analyze_def = mapMDefiniens analyze_t def

dmdDef :: VarDmd -> DmdAnl (FDef Mem)
dmdDef dmd def = dmdDef' (dmdFun dmd) def

dmdGlobalDef :: VarDmd -> DmdAnl (GDef Mem)
dmdGlobalDef dmd def = dmdDef' (dmdEnt dmd) def

dmdEnt dmd (FunEnt f) = FunEnt `liftM` dmdFun dmd f
dmdEnt _ (DataEnt d) = DataEnt `liftM` dmdData d

-- | Act like each exported function definition is used in an unknown way.
--   Doing so prevents the function from being inlined/deleted.
useExportedDefs :: [Def t Mem] -> Df ()
useExportedDefs defs = mapM_ demand_if_exported defs
  where
    demand_if_exported def =
      when (defAnnExported $ defAnnotation def) $
      mentionExtern (definiendum def)
  
dmdGroup :: forall a t.
            (t Mem -> Int)
         -> (VarDmd -> DmdAnl (Def t Mem))
         -> DefGroup (Def t Mem)
         -> Df a
         -> Df ([DefGroup (Def t Mem)], a)
dmdGroup arity do_def defgroup do_body =
  case defgroup
  of NonRec def -> do
       -- Eliminate dead code.  Decide whether the definition is dead.
       (body, dmd) <- getDemand (definiendum def) do_body_and_exports
       case multiplicity (fst dmd) of
         Dead ->
           return ([], body)
         _ -> do
           def' <- do_def dmd def
           let def'' = set_def_uses dmd def'
           return ([NonRec def''], body)

     Rec defs ->
       let local_vars = map definiendum defs
       in maskDemands local_vars $ rec_dmd defs
  where
    -- Process demands in the body.  Also account for exported variables.
    do_body_and_exports = do
      useExportedDefs $ defGroupMembers defgroup
      do_body

    rec_dmd defs = Df $ do
      -- Scan each definition and the body code
      defs_and_uses <- mapM (runDf . do_def unknownVarDmd) defs
      (body, body_uses) <- runDf do_body_and_exports

      -- Partition into strongly connected components
      let members = [((new_def, uses),
                      varID $ definiendum new_def,
                      uses)
                    | (new_def, uses) <- defs_and_uses]

          new_defs_and_uses :: forall. [DefGroup (Def t Mem, Dmds)]
          new_defs_and_uses = partitionDefGroup members body_uses

          new_uses =
            let local_function_uses =
                  map snd $ concatMap defGroupMembers new_defs_and_uses
            in joinSeqs (body_uses : local_function_uses)

          new_defs = map (fmap (set_uses . fst)) new_defs_and_uses
            where
              -- Save the local function's demand information
              set_uses def =
                let dmd = lookupDmd (definiendum def) new_uses
                in set_def_uses dmd def
      return ((new_defs, body), new_uses)
    
    set_def_uses dmd def =
      let definiens_arity = arity (definiens def)
          set_annotation a =
            a { defAnnUses = fst dmd
              , defAnnCalled = snd dmd `isCalledWithArity` definiens_arity}
      in modifyDefAnnotation set_annotation def

-- | Given the members of a definition group, the variables mentioned by them, 
--   and the set of members that are referenced by the rest of the program,
--   partition the group into a list of minimal definition groups.  Dead 
--   members are removed, and each group is only referenced by subsequent
--   members of the list.
partitionDefGroup :: [(a, VarID, Dmds)]
                     -- ^ The members of the definition group, their IDs, and
                     --   the IDs of the variables they reference
                  -> Dmds -- ^ References to members of definition group
                  -> [DefGroup a] -- ^ The partitioned definition group
partitionDefGroup members external_refs =
  let member_id_set =
        IntMap.fromList [(fromIdent n, nodemand) | (_, n, _) <- members]
      
      -- Restrict set 's' to the members of the definition group
      restrict s = IntMap.intersection s member_id_set

      -- Create a dummy variable ID for the graph node that represents 
      -- external references to the definition group
      dummy_id = toIdent $ 1 + fst (IntMap.findMax member_id_set)

      graph = (Nothing, dummy_id, nodes $ restrict external_refs) :
              [(Just x, n, nodes $ restrict ys) | (x, n, ys) <- members]
      
      sccs = Graph.stronglyConnComp graph
  in to_defgroups sccs
  where
    nodes :: Dmds -> [VarID]
    nodes = map toIdent . IntMap.keys

    to_defgroups sccs =
      -- Only save the definitions that precede the dummy node,
      -- meaning that they're referenced by something external
      map to_defgroup $ fst $ break is_dummy_node sccs

    to_defgroup (Graph.AcyclicSCC (Just x)) =
      NonRec x
    to_defgroup (Graph.AcyclicSCC _) =
      internalError "partitionDefGroup"
    to_defgroup (Graph.CyclicSCC xs) =
      case sequence xs
      of Just xs' -> Rec xs'
         _ -> internalError "partitionDefGroup"
    
    is_dummy_node (Graph.AcyclicSCC Nothing) = True
    is_dummy_node _ = False
    
    -- This value should never be used
    nodemand = internalError "partitionDefGroup: Invalid demand value"

-- | Eliminate dead code and get demands for an export declaration
dmdExport :: DmdAnl (Export Mem)
dmdExport export = do
  fun <- dmdFun unknownVarDmd $ exportFunction export
  return $ export {exportFunction = fun}

dmdTopLevelGroup (dg:dgs) exports = do
  let ent_arity (DataEnt _) = 0
      ent_arity (FunEnt f) = length $ funParams $ fromFunM f
  (dg', (dgs', exports')) <-
    dmdGroup ent_arity dmdGlobalDef dg $ dmdTopLevelGroup dgs exports
  return (dg' ++ dgs', exports')

dmdTopLevelGroup [] exports = do
  exports' <- mapM dmdExport exports
  return ([], exports')

-- | Perform local demand analysis and dead code elimination.
--   Top-level definitions are not removed or regrouped.
localDemandAnalysis :: Module Mem -> IO (Module Mem)
localDemandAnalysis mod =
  -- Same as full demand analysis
  demandAnalysis mod
{-  withTheNewVarIdentSupply $ \supply -> do
    tenv <- readInitGlobalVarIO the_memTypes
    defss' <- mapM (traverse evalDf 
  let defss' = map (fmap (\d -> evalDf (dmdGlobalDef d) tenv)) defss
      exports' = map (\e -> evalDf (dmdExport e) tenv) exports
  return $ Module modname imports defss' exports'
-}

-- | Perform demand analysis and dead code elimination.
demandAnalysis :: Module Mem -> IO (Module Mem)
demandAnalysis mod@(Module modname imports defss exports) =
  withTheNewVarIdentSupply $ \supply -> do
    tenv <- readInitGlobalVarIO the_memTypes
    (defss', exports') <- evalDf (dmdTopLevelGroup defss exports) supply tenv
    return $ Module modname imports defss' exports'
