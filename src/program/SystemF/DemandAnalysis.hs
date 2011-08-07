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

{-# LANGUAGE TypeSynonymInstances, ViewPatterns #-}
module SystemF.DemandAnalysis
       (altSpecificity,
        altListSpecificity,
        demandAnalysis,
        localDemandAnalysis)
where

import Control.Monad
import Control.Monad.Reader.Class
import Control.Monad.Writer.Class
import qualified Data.Graph as Graph
import qualified Data.IntMap as IntMap
import qualified Data.Set as Set
import Data.List
import Data.Maybe
import Debug.Trace

import Common.Error
import Common.Identifier
import Builtins.Builtins
import SystemF.Floating
import SystemF.Demand
import SystemF.Syntax
import SystemF.MemoryIR
import SystemF.PrintMemoryIR
import Type.Environment
import Type.Rename
import Type.Type
import GlobalVar
import Globals

-------------------------------------------------------------------------------
-- Demand analysis functions

-- | Demand analysis takes the global type environment as a parameter.
--   The global type environment is used to look up type and data constructors
--   only.  The analysis generates information how variables are used.
newtype Df a = Df {runDf :: TypeEnv -> (a, Dmds)}

evalDf :: Df a -> TypeEnv -> a
evalDf m env = fst (runDf m env)

instance Functor Df where
  fmap = liftM

instance Monad Df where
  return x = Df (\_ -> (x, IntMap.empty))
  m >>= k = Df (\env -> case runDf m env
                        of (x, dmd1) -> case runDf (k x) env
                                        of (y, dmd2) -> (y, joinSeq dmd1 dmd2))

instance MonadReader TypeEnv Df where
  ask = Df (\tenv -> (tenv, IntMap.empty))
  local f m = Df (\tenv -> runDf m (f tenv))

instance MonadWriter Dmds Df where
  tell w = Df (\_ -> ((), w))
  listen m = Df (\tenv -> let (x, w) = runDf m tenv in ((x, w), w))
  pass m = Df (\tenv -> let ((x, f), w) = runDf m tenv in (x, f w))

-- | Run multiple dataflow analyses on mutually exclusive execution paths.
--   This kind of execution occurs in case alternatives.
parallel :: [Df a] -> Df [a]
parallel dfs = Df $ \tenv ->
  case unzip [runDf df tenv | df <- dfs]
  of (xs, dmds) -> (xs, joinPars dmds)

underLambda :: Df a -> Df a
underLambda m = censor lambdaAbstracted m

-- | Demand analysis only deals with variables that can be removed from the 
--   program.  Global type variables (type functions and constructors) and
--   data constructor definitions cannot be removed, so they are ignored.
--   To decide whether a variable is ignored, look it up in the type
--   environment.
isDeletable :: TypeEnv -> Var -> Bool
isDeletable tenv v =
  isNothing (lookupDataType v tenv) &&
  isNothing (lookupDataCon v tenv) &&
  isNothing (lookupTypeFunction v tenv)

-- | A helper function for 'mention'.  If the variable is a global type or 
--   data constructor, then ignore it.
mentionHelper v dmd = do
  tenv <- ask
  if isDeletable tenv v
    then tell $ useVariable v dmd
    else return ()

mentionHelperList vs dmd = do
  tenv <- ask
  let used_variables = [v | v <- vs, isDeletable tenv v]
  tell $ useVariables used_variables dmd

-- | A variable was used somehow.  This is the most general case.
mention :: Var -> Df ()
mention v = mentionHelper v $ Dmd OnceSafe Used

-- | Mention a list of variables, behaving the same as 'mention'.
mentionList :: [Var] -> Df ()
mentionList vs = mentionHelperList vs $ Dmd OnceSafe Used

-- | A variable was used multiple times.  This prevents inlining.
--
--   We put 'Unused' as the specificity here to avoid contaminating the 
--   specificity information that we compute.
mentionMany :: Var -> Df ()
mentionMany v = mentionHelper v $ Dmd ManySafe Unused

-- | A variable was used with the given specificity.
mentionSpecificity :: Var -> Specificity -> Df ()
mentionSpecificity v spc = mentionHelper v $ Dmd OnceSafe spc

-- | A variable was used in a multiple-alternative case statement or \'copy\'
--   function.
mentionMultiCase :: Var -> Df ()
mentionMultiCase v = mentionHelper v $ Dmd OnceSafe Inspected

-- | Get the demand on variable @v@ produced by the given code; also, remove
--   @v@ from the demanded set
getDemand :: Var -> Df a -> Df (a, Dmd)
getDemand v m = Df $ \tenv ->
  let (x, dmds) = runDf m tenv
      dmd = lookupDmd v dmds
      dmds' = IntMap.delete (fromIdent $ varID v) dmds
  in ((x, dmd), dmds')

maskDemand :: Var -> Df a -> Df a
maskDemand v m = fmap fst $ getDemand v m

maskDemands :: [Var] -> Df a -> Df a
maskDemands vs m = Df $ \tenv ->
  let (x, dmds) = runDf m tenv
      dmds' = foldr (\v m -> IntMap.delete (fromIdent $ varID v) m) dmds vs
  in (x, dmds')

-------------------------------------------------------------------------------
-- Demand analysis on Mem IR

-- | A computation that performs demand analysis, eliminates dead code,
--   minimizes recursive definition groups, and
--   annotates variable bindings with their demands in a piece of code.
type DmdAnl a = a -> Df a

-- | Get variables mentioned in a type.
--   The type is not changed by demand analysis.
dfType :: Type -> Df ()
dfType ty = mentionList $ Set.toList $ freeVariables ty

withTyPat :: TyPatM -> Df a -> Df (TyPatM, a)
withTyPat pat@(TyPatM (v ::: ty)) m = do
  dfType ty
  x <- maskDemand v m
  return (pat, x)
  
withTyPats (pat:pats) m = do
  (p, (ps, x)) <- withTyPat pat $ withTyPats pats m
  return (p : ps, x)

withTyPats [] m = fmap ((,) []) m

withParam :: PatM -> Df a -> Df (PatM, a)
withParam pat m = do
  dfType $ patMType pat
  (x, dmd) <- getDemand (patMVar pat) m
  let new_pat = setPatMDmd dmd pat
  return (new_pat, x)

withParams :: [PatM] -> Df a -> Df ([PatM], a)
withParams (pat : pats) m = do
  (p, (ps, x)) <- withParam pat $ withParams pats m
  return (p : ps, x)

withParams [] m = fmap ((,) []) m

-- | Do demand analysis on an expression, given how the expression's result
--   is used.
dmdExp :: Specificity -> DmdAnl ExpM
dmdExp spc expressionM@(ExpM expression) =
  case expression
  of VarE _ v -> mentionSpecificity v spc >> return expressionM
     LitE _ _ -> return expressionM
     UTupleE inf args -> dmdUTupleE inf args
     AppE inf op ts args -> dmdAppE inf op ts args
     LamE inf f -> do
       f' <- dmdFun f
       return $ ExpM $ LamE inf f'
     LetE inf pat rhs body -> dmdLetE spc inf pat rhs body
     LetfunE inf dg body -> do
       (dg', body') <- dmdGroup dg (dmdExp spc body)
       let mk_let defgroup e = ExpM (LetfunE inf defgroup e)
       return $ foldr mk_let body' dg'
     CaseE inf scr alts -> dmdCaseE spc inf scr alts
     ExceptE _ ty -> dfType ty >> return expressionM
     CoerceE inf t1 t2 e -> do
       dfType $ fromTypM t1
       dfType $ fromTypM t2
       e' <- dmdExp spc e
       return $ ExpM $ CoerceE inf t1 t2 e'
  where
    {- -- Debugging output, show what was demanded in this expression
    trace_dmd m = do
      (x, dmd) <- listen m
      trace ("dmdExp\n" ++ show (pprExp expressionM) ++ "\n" ++
             intercalate "\n" [show v ++ " |-> " ++ showDmd d
                              | (v,d) <- IntMap.toList dmd])  $ return x
    -}
      
dmdUTupleE inf args = do
  args' <- mapM (dmdExp Used) args
  return $ ExpM $ UTupleE inf args'

-- | Dead code elimination for function application.
--
--   Perform dead code elimination on subexpressions as usual.
--   However, parameters that should be floated are marked as having
--   multiple uses so that they don't get inlined.
dmdAppE inf op ty_args args = do
  op' <- dmdExp Used op
  args' <- zipWithM dmdExp use_modes args
  tenv <- ask
  add_datacon_uses tenv op' args'
  return $ ExpM $ AppE inf op' ty_args args'
  where
    -- How the function arguments are used.
    -- We special-case the 'load' function.
    use_modes =
      case op
      of ExpM (VarE _ op_var)
           | op_var `isPyonBuiltin` the_copy && length args == 2 ->
               [Used, Inspected]
           | op_var `isPyonBuiltin` the_copy && length args == 3 ->
               [Used, Inspected, Used]
         _ -> repeat Used

    -- Determine which parameters should be floated.
    -- If a parameter should be floated, mark it as having multiple uses
    -- so it won't get inlined.
    floated_parameters tenv op' =
      case op'
      of ExpM (VarE _ op_var) -> Just $ floatedParameters' tenv op_var ty_args
         _ -> Nothing

    -- If an argument is a variable and should be floated,
    -- mark the argument as being used many times.
    add_datacon_uses tenv op' edc_args =
      case floated_parameters tenv op'
      of Nothing -> return ()
         Just floated_params ->
           mapM_ mentionMany $
           [v | (ExpM (VarE _ v), True) <- zip edc_args floated_params]

dmdLetE spc inf binder rhs body = do
  (body', demand) <- getDemand (patMVar binder) $ dmdExp spc body
  case multiplicity demand of
    Dead -> return body'        -- RHS is eliminated
    _ -> do
      -- Must also mask the RHS, since it could mention the local variable.
      -- Mentions in the RHS only define the variable; we don't count them 
      -- as uses.
      rhs' <- maskDemand (patMVar binder) $ dmdExp Used rhs
      dfType (patMType binder)
      return $ ExpM $ LetE inf (setPatMDmd demand binder) rhs' body'

dmdCaseE result_spc inf scrutinee alts = do
  -- Get demanded values in each alternative
  (unzip -> (alts', joinPars -> alts_spc)) <-
    parallel $ map (dmdAlt result_spc) alts

  -- If there's only one alternative and none of its fields are used, then
  -- eliminate the entire case statement
  case alts' of
    [AltM alt'] | null (getAltExTypes alt') &&
                  all isDeadPattern (altParams alt') ->
      return $ altBody alt'
    _ -> do
      -- Process the scrutinee
      scrutinee' <- dmdExp alts_spc scrutinee
      return $ ExpM $ CaseE inf scrutinee' alts'

-- | Construct the specificity for a case scrutinee, based on how its value
--   is bound by a case alternative
altSpecificity :: AltM -> Specificity
altSpecificity alt = Decond mono_con fields
  where
    (mono_con, params, _) = altToMonoCon alt
    fields = map (specificity . patMDmd) params

-- | Construct the specificity for a case scrutinee, based on how its value
--   is bound by a list of alternatives.  If there's more than one alternative,
--   the specificity will be 'Inspected'.
altListSpecificity :: [AltM] -> Specificity
altListSpecificity []  = internalError "altListSpecificity: Empty list"
altListSpecificity [a] = altSpecificity a
altListSpecificity _   = Inspected

-- | Do demand analysis on a case alternative.  Return the demand on the
--   scrutinee.
dmdAlt :: Specificity -> AltM -> Df (AltM, Specificity)
dmdAlt result_spc (AltM (DeCon con ty_args ex_types params body)) = do
  mapM_ (dfType . fromTypM) ty_args
  (typats', (pats', body')) <-
    withTyPats ex_types $ withParams params $ dmdExp result_spc body

  let new_alt = AltM $ DeCon { altConstructor = con
                             , altTyArgs = ty_args
                             , altExTypes = typats'
                             , altParams = pats'
                             , altBody = body'}
  return (new_alt, altSpecificity new_alt)

dmdAlt result_spc (AltM (DeTuple params body)) = do
  (pats', body') <-
    withParams params $ dmdExp result_spc body

  let new_alt = AltM $ DeTuple { altParams = pats'
                               , altBody = body'}
  return (new_alt, altSpecificity new_alt)  

dmdFun :: DmdAnl FunM
dmdFun (FunM f) = do
  -- Eliminate dead code and convert patterns to wildcard patterns.
  (tps', (ps', b')) <-
    underLambda $
    withTyPats (funTyParams f) $
    withParams (funParams f) $ do
      dfType $ fromTypM $ funReturn f
      dmdExp Used (funBody f)
  return $ FunM $ f {funTyParams = tps', funParams = ps', funBody = b'}

dmdDef :: DmdAnl (Def Mem)
dmdDef def = mapMDefiniens dmdFun def

dmdGroup :: DefGroup (Def Mem) -> Df b -> Df ([DefGroup (Def Mem)], b)
dmdGroup defgroup do_body =
  case defgroup
  of NonRec def -> do
       -- Eliminate dead code.  Decide whether the definition is dead.
       (body, dmd) <- getDemand (definiendum def) do_body
       case multiplicity dmd of
         Dead -> return ([], body)
         _ -> do
           def' <- dmdDef def
           return ([NonRec def'], body)

     Rec defs ->
       let local_vars = map definiendum defs
       in maskDemands local_vars $ rec_dmd defs
  where
    rec_dmd defs = Df $ \tenv ->
      let -- Scan each definition and the body code
          defs_and_uses = [runDf (dmdDef def) tenv | def <- defs]
          (body, body_uses) = runDf do_body tenv

          -- Partition into strongly connected components
          members = [((new_def, uses),
                      varID $ definiendum new_def,
                      uses)
                    | (new_def, uses) <- defs_and_uses]
          new_defs_and_uses = partitionDefGroup members body_uses
          new_defs = map (fmap fst) new_defs_and_uses
          new_uses = joinSeqs $ map snd $ concatMap defGroupMembers new_defs_and_uses
      in ((new_defs, body), new_uses `joinSeq` body_uses)

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
  fun <- dmdFun $ exportFunction export
  return $ export {exportFunction = fun}

dmdTopLevelGroup (dg:dgs) exports = do
  (dg', (dgs', exports')) <-  dmdGroup dg $ dmdTopLevelGroup dgs exports
  return (dg' ++ dgs', exports')

dmdTopLevelGroup [] exports = do
  exports' <- mapM dmdExport exports
  return ([], exports')

-- | Perform local demand analysis and dead code elimination.
--   Top-level definitions are not removed or regrouped.
localDemandAnalysis :: Module Mem -> IO (Module Mem)
localDemandAnalysis (Module modname imports defss exports) = do
  tenv <- readInitGlobalVarIO the_memTypes
  let defss' = map (fmap (\d -> evalDf (dmdDef d) tenv)) defss
      exports' = map (\e -> evalDf (dmdExport e) tenv) exports
  return $ Module modname imports defss' exports'

-- | Perform demand analysis and dead code elimination.
demandAnalysis :: Module Mem -> IO (Module Mem)
demandAnalysis (Module modname imports defss exports) = do
  tenv <- readInitGlobalVarIO the_memTypes
  let (defss', exports') = evalDf (dmdTopLevelGroup defss exports) tenv
  return $ Module modname imports defss' exports'
