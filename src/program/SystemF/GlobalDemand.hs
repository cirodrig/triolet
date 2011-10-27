{-| Global demand analysis.

The analysis still has some issues, but it is useful to see cases where it
refines the demand on functions'  return values.

This analysis improves the results of local demand analysis by
computing a more accurate demand on the return value of each function.
Local demand analysis computes the consequences of that demand on the
body of the function.

-}
{-# LANGUAGE GeneralizedNewtypeDeriving, TypeSynonymInstances, DoRec #-}
{-# OPTIONS_GHC -auto #-}
module SystemF.GlobalDemand (performGlobalDemandAnalysis)
where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.Writer
import qualified Data.HashTable as HashTable
import Data.IORef
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import Data.Maybe
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import SystemF.Syntax
import SystemF.MemoryIR
import SystemF.PrintMemoryIR
import SystemF.Demand
import SystemF.TypecheckMem
import Type.Type
import Type.Environment
import Type.Eval
import Globals
import GlobalVar

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

type Spcs = IntMap.IntMap Specificity

lookupSpc :: Var -> Spcs -> Specificity
{-# INLINE lookupSpc #-}
lookupSpc v m = fromMaybe bottom $ IntMap.lookup (fromIdent $ varID v) m

demandVariable :: Var -> Specificity -> Spcs
demandVariable v s = IntMap.singleton (fromIdent $ varID v) s

type DmdVar = IORef Specificity

-- | A function's demand analysis state.
--   Includes return demand, parameter demands, and a function to recompute
--   demand information.
data DmdFun =
  DmdFun 
  { -- | The function name.  This is only used for debugging.
    dmdFunName :: !(Maybe Var)
  , returnDemand :: !DmdVar
  , paramDemands :: ![DmdVar]
    -- | Number of parameters other than output parameters
  , inputArity :: {-#UNPACK#-}!Int
    -- | If the function takes an output parameter, this is the parameter
    -- variable
  , outputParam :: !(Maybe Var)
    -- | In the case of recursive definition groups, the evaluator may be
    --   assigned lazily
  , evaluator :: Run ()
  }

-- | The monad in which constraint solving runs.
--
--   Constraint solving has access to the global (not local) type environment.
newtype Run a = Run {run :: TypeEnv -> IO (a, Spcs)}

instance Functor Run where
  fmap f (Run m) = Run $ \tenv -> do
    (x, spcs) <- m tenv
    return (f x, spcs)

instance Monad Run where
  return x = Run $ \_ -> return (x, bottom)
  m >>= k = Run $ \tenv -> do
    (x, spcs1) <- run m tenv
    (y, spcs2) <- run (k x) tenv
    return (y, joinSeq spcs1 spcs2)

instance MonadIO Run where
  liftIO m = Run $ \_ -> do {x <- m; return (x, bottom)}

instance MonadReader TypeEnv Run where
  ask = Run $ \tenv -> return (tenv, bottom)
  local f (Run g) = Run (g . f)

instance MonadWriter Spcs Run where
  tell w = Run $ \_ -> return ((), w)
  listen m = Run $ \tenv -> do
    (x, w) <- run m tenv
    return ((x, w), w)                  
  pass m = Run $ \tenv -> do
    ((x, f), w) <- run m tenv
    return (x, f w)

parallel :: [Run a] -> Run [a]
parallel xs = Run $ \env -> do
  (ys, dmds) <- mapAndUnzipM (\x -> run x env) xs
  return (ys, joinPars dmds)

-- | A computation that evaluates demand information in some expression.
--
--   Its side effects are to update 'DmdVar's and to put functions on
--   the worklist.
type Evaluator = Specificity -> Run ()

-- | Skip the computation if the value it produces is dead.  A dead result 
--   means the computation is dead code and will be removed from the program.
ifLive :: Evaluator -> Evaluator
ifLive ev Unused = return ()
ifLive ev spc    = ev spc

-- | Read the value of a 'DmdVar'.
readDmdVar :: DmdVar -> Run Specificity
readDmdVar var = liftIO $ readIORef var

-- | Assign the value of a 'DmdVar'.
writeDmdVar :: DmdVar -> Specificity -> Run ()
writeDmdVar var spc = liftIO $ writeIORef var spc

-- | Update the return value of a 'DmdFun'.  Recurse into the function if its 
--   value changes.
--
--   To ensure that the algorithm terminates, values should
--   increase monotonically.  This is not checked.
updateDmdFun :: DmdFun -> Specificity -> Run [Specificity]
updateDmdFun dfun spc = do
  old_value <- readDmdVar $ returnDemand dfun
  if sameSpecificity old_value spc then return () else do
    writeDmdVar (returnDemand dfun) spc
    evaluator dfun
  mapM readDmdVar $ paramDemands dfun

mention :: Var -> Specificity -> Run ()
mention v spc = do
  tenv <- ask
  tell $! if isDeletable tenv v then demandVariable v spc else bottom

getDemandPats :: [PatM] -> Run a -> Run (a, [Specificity])
getDemandPats (pat : pats) m = do
  ((x, spcs), spc) <- getDemandPat pat $ getDemandPats pats m
  return (x, spc : spcs)

getDemandPats [] m = do
  x <- m
  return (x, [])

-- | Run some computation over which a variable is in scope.
--   The variable is removed from the resulting demand information.
getDemandPat :: PatM -> Run a -> Run (a, Specificity)
getDemandPat pat m = getDemand (patMVar pat) m

getDemand :: Var -> Run a -> Run (a, Specificity)
getDemand v m = Run $ \r -> do
  let vid = fromIdent $ varID v
  (x, w) <- vid `seq` run m r
  let spc = lookupSpc v w
  return ((x, spc), IntMap.delete vid w)

maskDemands :: [Var] -> Run a -> Run a
maskDemands vs m = Run $ \r -> do
  (x, w) <- run m r
  let vids = map (fromIdent . varID) vs
  return (x, foldr IntMap.delete w vids)

maskDemand :: Var -> Run a -> Run a
maskDemand v m = Run $ \r -> do
  (x, w) <- run m r
  let vid = fromIdent $ varID v
  return (x, IntMap.delete vid w)

-- | Process an exported function call.  Evaluate the function.
--   specificities.
callDmdFun :: DmdFun -> Run ()
callDmdFun f = do
  writeDmdVar (returnDemand f) Used
  evaluator f

-------------------------------------------------------------------------------

type FunTable = HashTable.HashTable Var DmdFun

data SetupEnv =
  SetupEnv 
  { setupFunTable :: !FunTable
  , setupTypeEnv :: TypeEnv
  }

newtype Setup a = Setup {unSetup :: ReaderT SetupEnv IO a}
                deriving(Functor, Monad, MonadFix, MonadIO)

runSetup :: Setup a -> SetupEnv -> IO a
runSetup (Setup f) env = runReaderT f env

instance TypeEnvMonad Setup where
  askTypeEnv f = Setup $ ReaderT $ \env -> return (f $ setupTypeEnv env)
  assumeWithProperties v t b m = Setup $ local insert_type $ unSetup m 
    where
      insert_type env =
        env {setupTypeEnv = insertTypeWithProperties v t b $ setupTypeEnv env}

putDmdFun :: Var -> DmdFun -> Setup ()
putDmdFun v f = Setup $ ReaderT $ \env ->
  HashTable.insert (setupFunTable env) v f

getDmdFun :: Var -> Setup (Maybe DmdFun)
getDmdFun v = Setup $ ReaderT $ \env ->
  HashTable.lookup (setupFunTable env) v

newDmdVar :: Specificity -> Setup DmdVar
newDmdVar s = liftIO $ newIORef s

-------------------------------------------------------------------------------

-- | Generate code to process a definition group.
--   Add the group to the environment.
setupDefGroup :: DefGroup (Def Mem) -> Setup a -> Setup a
setupDefGroup group m = do
  case group of
    NonRec fdef -> do
      dmd_fun <- setupFun (Just $ definiendum fdef) (definiens fdef)
      save_function fdef dmd_fun
    Rec fdefs -> assume_functions $ do
      let functions = map definiens fdefs
      rec dmd_funs <- forM (lazy_zip fdefs evaluators) $ \(def, ev) -> do
            makeDmdFun (Just $ definiendum def) (definiens def) ev
          zipWithM_ save_function fdefs dmd_funs
          evaluators <- zipWithM makeEvaluator functions dmd_funs
      return ()
  
  assume_functions m
  where
    save_function fdef x = putDmdFun (definiendum fdef) x
    
    lazy_zip (x:xs) ~(y:ys) = (x, y) : lazy_zip xs ys
    lazy_zip []     _       = []

    assume_functions :: forall b. Setup b -> Setup b
    assume_functions m = foldr assume_function m (defGroupMembers group)
      where
        assume_function fdef m =
          assume (definiendum fdef) (functionType $ definiens fdef) m

makeDmdFun :: Maybe Var -> FunM -> Run () -> Setup DmdFun
makeDmdFun m_name (FunM fun) evaluator =
  assumeTyPats (funTyParams fun) $ assumePatMs (funParams fun) $ do
    -- Create variables representing parameters and return values.
    -- Initialize with the demand analysis results that are annotated
    -- onto the function.
    param_vars <- forM (funParams fun) $ \param -> newDmdVar bottom
    ret_var <- newDmdVar bottom

    -- Determine the function's arity
    tenv <- getTypeEnv
    let (input_arity, output_param) =
          let (input_params, output_params) =
                partitionParameters tenv (funParams fun)
              output_param =
                case output_params
                of [] -> Nothing
                   [p] -> Just $ patMVar p
                   _ -> internalError "setupFun: Can't handle multiple output parameters"
          in (length input_params, output_param)
    
    return $ DmdFun m_name ret_var param_vars input_arity output_param evaluator
  where
    -- Separate the function parameters into input and output parameters.
    -- Output parameters must follow input parameters.
    partition_parameters tenv params = go id params 
      where
        go hd (p:ps) =
          case toBaseKind $ typeKind tenv (patMType p)
          of OutK -> (hd [], check_out_kinds (p:ps))
             _    -> go (hd . (p:)) ps

        go hd [] = (hd [], [])
        
        check_out_kinds ps
          | and [OutK == toBaseKind (typeKind tenv (patMType p)) | p <- ps] = ps
          | otherwise =
            internalError "planFunction: Cannot handle function parameters"

makeEvaluator :: FunM -> DmdFun -> Setup (Run ())
makeEvaluator (FunM fun) dmd_fun = do
  compute <- assumeTyPats (funTyParams fun) $
             assumePatMs (funParams fun) $
             setupExp (funBody fun)
  let recompute = do
        -- Read the return value, analyze the function body, 
        -- and determine the new parameter values
        ((), param_demands) <- getDemandPats (funParams fun) $ do
          compute =<< readDmdVar (returnDemand dmd_fun)

        -- Update parameter values
        zipWithM_ writeDmdVar (paramDemands dmd_fun) param_demands
  return recompute

setupFun :: Maybe Var -> FunM -> Setup DmdFun
setupFun m_name fun = do
  rec dfun <- makeDmdFun m_name fun evaluator
      evaluator <- makeEvaluator fun dfun
  return dfun

-- | Lambda functions aren't candidates for worker-wrapper transformation.
--   So, we analyze the function conservatively.
setupLambdaFun :: FunM -> Setup (Run ())
setupLambdaFun (FunM f) = 
  assumeTyPats (funTyParams f) $
  assumePatMs (funParams f) $ do
    eval_body <- setupExp (funBody f)
    return $ eval_body Used

setupExp :: ExpM -> Setup Evaluator
setupExp (ExpM expression) =
  case expression
  of VarE _ v -> setupVar v

     LitE _ _ -> return $ const $ return ()

     ConE _ con args -> setupConApp args

     AppE _ op@(ExpM (VarE _ op_var)) ty_args args -> do
       tenv <- getTypeEnv
       case lookupDataCon op_var tenv of
         Just dcon ->
           -- This is a data constructor application
           setupConApp args
         Nothing -> do
           function <- getDmdFun op_var
           case function of
             Just fun ->
               let out = outputParam fun
                   input_saturated = length args == inputArity fun
                   fully_saturated = isJust out && length args == inputArity fun + 1
               in case () of
                 _ | isJust out && input_saturated ->
                     -- This is a function application returning an initializer
                     let Just out_var = out
                     in setupDirectCall (evalInitializerCall fun out_var) fun op_var args
                   | isJust out && fully_saturated ->
                     -- This is a function application returning by side effect
                     setupDirectCall (evalEffectCall fun) fun op_var args
                   | isNothing out && input_saturated ->
                     -- This is a function application returning a value
                     setupDirectCall (evalValueCall fun) fun op_var args
                   | otherwise ->
                     -- Undersaturated or oversaturated function application
                     setupUnknownApp op args
             Nothing ->
               -- Not a function application.  Unknown demand on each argument.
               setupUnknownApp op args

     AppE _ op _ args ->
       setupUnknownApp op args

     LamE _ f -> do
       -- Function body has an unknown demand on its return value.
       -- Since lambda functions don't get argument-flattened, it's not worth
       -- analyzing them in more detail.
       ev <- setupLambdaFun f
       return $ ifLive $ const ev

     LetE _ pat rhs body -> setupLet pat rhs body

     LetfunE _ defs body -> setupLetfun defs body

     CaseE _ scr alts -> setupCase scr alts
   
     -- All variables are dead when execution is interrupted
     ExceptE _ _ -> return $ const $ return ()

     CoerceE _ _ _ body -> setupCoerce body

setupVar v = do
  dmd_fun <- getDmdFun v
  return $ \dmd -> do
    maybe (return ()) evalIndirectCall dmd_fun
    mention v dmd

setupConApp :: [ExpM] -> Setup Evaluator
setupConApp field_exps = do
  tenv <- getTypeEnv
  eval_fields <- mapM setupExp field_exps
  n_fields <- return $! length eval_fields
  return $ evalConApp tenv n_fields eval_fields

-- | Propagate demands through a constructor application.
--
--   Deconstruct the demand information and propagate it to the fields.
evalConApp :: TypeEnv -> Int -> [Evaluator] -> Evaluator
evalConApp tenv n_fields eval_fields dmd = do
  let field_demands = deconstructSpecificity tenv n_fields dmd
  zipWithM_ ($) eval_fields field_demands

setupDirectCall :: ([Evaluator] -> Evaluator)
                -> DmdFun -> Var -> [ExpM] -> Setup Evaluator
setupDirectCall evaluate dmd_fun op_var args = do
  eval_args <- mapM setupExp args
  return $ \dmd -> do
    ifLive (const $ mention op_var Used) dmd
    evaluate eval_args dmd

-- | If a function has an indirect call, its return annotation is unknown.
--   
evalIndirectCall :: DmdFun -> Run ()
evalIndirectCall f = void $ updateDmdFun f Used

-- | Evaluate a call of a function that returns an initializer.
evalInitializerCall :: DmdFun -> Var -> [Evaluator] -> Evaluator
evalInitializerCall dmd_fun out_var eval_args dmd = do
  -- If the call's return demand is an initializer demand,
  -- translate it into a side effect demand.
  let return_dmd =
        case dmd
        of Written d -> Read (HeapMap [(out_var, d)])
           Unused -> Unused
           _ -> Used
  arg_dmds <- updateDmdFun dmd_fun return_dmd
    
  -- Compute the demands on arguments.
  -- We have @length arg_dmds - 1 == length eval_args@.  The last arg_dmd
  -- is for the output pointer, which is certainly 'Used'.  
  zipWithM_ ($) eval_args arg_dmds

-- | Evaluate a call of a function that produces a side effect.
evalEffectCall :: DmdFun -> [Evaluator] -> Evaluator
evalEffectCall dmd_fun eval_args dmd = do
  arg_dmds <- updateDmdFun dmd_fun dmd
  zipWithM_ ($) eval_args arg_dmds

-- | Evaluate a call of a function that returns a value.
evalValueCall :: DmdFun -> [Evaluator] -> Evaluator
evalValueCall dmd_fun eval_args dmd = do
  arg_dmds <- updateDmdFun dmd_fun dmd
  zipWithM_ ($) eval_args arg_dmds

-- | Apply an unknown operator to arguments.
--
--   If argument values are live, then the operator and argument values are
--   all used in an unknown way.
setupUnknownApp :: ExpM -> [ExpM] -> Setup Evaluator
setupUnknownApp op args = do
  eval_op <- liftM ($ Used) $ setupExp op
  eval_args <- mapM (liftM ($ Used) . setupExp) args
  return $ ifLive $ \_ -> do 
    eval_op
    sequence_ eval_args

setupLet pat rhs body = do
  eval_body <- assumePatM pat $ setupExp body
  eval_rhs <- setupExp rhs
  return $ evalLet pat eval_rhs eval_body

-- | Evaluate a let expression.  Process the body to determine demand on the
--   let-bound variable.  If it's live, process the RHS.
evalLet pat rhs body dmd = do
  ((), x_dmd) <- getDemandPat pat $ body dmd
  ifLive rhs x_dmd

setupLetfun defs body = do
  eval_body <- setupDefGroup defs $ setupExp body
  return $ \dmd -> do
    maskDemands (map definiendum $ defGroupMembers defs) $ eval_body dmd

setupCase scr alts = do
  eval_alts <- mapM setupAlt alts
  eval_scr <- setupExp scr
  return $ evalCase eval_scr eval_alts 

evalCase scr alts dmd = do
  alt_dmds <- parallel $ map ($ dmd) alts
  scr $ joinPars alt_dmds

-- | Construct the demand computation for a case alternative.  The return
--   value is the demand imposed on the scrutinee.
setupAlt :: AltM -> Setup (Specificity -> Run Specificity)
setupAlt (AltM alt) =
  assumeBinders (deConExTypes $ altCon alt) $ assumePatMs (altParams alt) $ do
    eval_body <- setupExp $ altBody alt

    return $ evalAlt (altCon alt) (altParams alt) eval_body

evalAlt mono_con params eval_body dmd = do
  ((), param_demands) <- getDemandPats params $ eval_body dmd
  return $ Decond mono_con param_demands

setupCoerce body = do
  eval_body <- setupExp body
  return $ \dmd -> eval_body $ weaken dmd
  where
    -- Since the type is changed, and demand information is type-specific,
    -- we cannot preserve precise demand information.
    weaken (Decond {})  = Inspected
    weaken (Written {}) = Used
    weaken (Read {})    = Used
    weaken x            = x

setupExport export =
  setupFun Nothing $ exportFunction export

-- | Construct the demand computation for an entire module.  Return the list
--   of exported functions.
setupModule :: Module Mem -> Setup [DmdFun]
setupModule mod = do
  foldr setupDefGroup (mapM setupExport (modExports mod)) $ modDefs mod

setupAnalysis :: IdentSupply Var -> TypeEnv -> Module Mem
              -> IO (FunTable, [DmdFun])
setupAnalysis id_supply global_tenv mod = do
  -- Add imports to the type environment
  let imports_tenv = foldr (uncurry insertType) global_tenv
                     [(definiendum def, functionType $ definiens def)
                     | def <- modImports mod]

  -- Create function table
  fun_table <- HashTable.new (==) (HashTable.hashInt . fromIdent . varID)

  export_functions <-
    runSetup (setupModule mod) (SetupEnv fun_table imports_tenv)
  return (fun_table, export_functions)

-- | Run the analysis.  Demand variables are updated by the analysis. 
runAnalysis :: TypeEnv -> [DmdFun] -> IO ()
runAnalysis tenv export_functions = void $ run analyze tenv
  where
    analyze = mapM_ callDmdFun export_functions

-------------------------------------------------------------------------------
-- Annotating results back into the program.
-- Functions are annotated with the demands on their return values.

annotateExp :: FunTable -> ExpM -> IO ExpM
annotateExp ftable (ExpM expression) =
  case expression
  of VarE {} -> return (ExpM expression)
     LitE {} -> return (ExpM expression)

-------------------------------------------------------------------------------

-- | Print out the computed demands for each function
showResults :: FunTable -> IO ()
showResults ftable = do
  members <- HashTable.toList ftable
  mapM_ show_member members 
  where
    show_member (v, dmd_fun) = do
      param_demands <- mapM readIORef $ paramDemands dmd_fun
      return_demand <- readIORef $ returnDemand dmd_fun
      print $ hang (pprVar v <> text ":") 4
        (parens (vcat $ map pprSpecificity param_demands) $$ pprSpecificity return_demand)

performGlobalDemandAnalysis :: Module Mem -> IO (Module Mem)
performGlobalDemandAnalysis mod =
  withTheNewVarIdentSupply $ \id_supply -> do
    global_tenv <- readInitGlobalVarIO the_memTypes
    (htab, export_functions) <- setupAnalysis id_supply global_tenv mod
    runAnalysis global_tenv export_functions
    showResults htab
    return mod
