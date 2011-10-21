
{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleInstances, BangPatterns #-}
module LowLevel.Inlining2(inlineModule)
where

import Control.Applicative
import Control.Monad
import Control.Monad.RWS
import Control.Monad.Trans
import qualified Data.IntMap as IntMap
import Data.Maybe
import Data.Monoid
import Debug.Trace

import System.IO
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.MonadLogic
import Common.Supply
import Common.Identifier
import LowLevel.FreshVar
import LowLevel.CodeTypes
import qualified LowLevel.Rename
import LowLevel.Print
import LowLevel.Syntax
import Export
import Globals
import GlobalVar

type Renaming = IntMap.IntMap Var

closureInlineCutoff = 20
primInlineCutoff = 5

emptyRenaming = IntMap.empty

-- | The set of functions that can be inlined, and their numbers of endpoints.
type InlinedFunctions = IntMap.IntMap (Fun, NumReturns)

-- | The continuation of a function call.
--   Inlining may turn the continuation into a local function.
data ContinuationCode =
    HasContinuation [ParamVar] [ValueType] Stm
  | IsTailCall

data NumReturns = Zero | One | Many deriving(Show)

instance Monoid NumReturns where
  mempty = Zero
  mappend Zero x = x
  mappend x Zero = x
  mappend _ _ = Many

data InlEnv =
  InlEnv { varSupply :: !(IdentSupply Var)
         , functions :: InlinedFunctions
         , renaming :: Renaming
           -- | Return types of the current function.  'Nothing' when not
           --   processing a function body.
         , currentReturns :: !(Maybe [ValueType])
         }

-- | While inlining code in a function body,
--   compute the amount of code growth and count the number of endpoints the
--   function has
data InlState = InlState !NumReturns !CodeSize

instance Monoid InlState where
  mempty = InlState mempty mempty
  InlState r1 c1 `mappend` InlState r2 c2 =
    InlState (mappend r1 r2) (mappend c1 c2)

newtype Inl s a = Inl {unInl :: RWST InlEnv () s IO a}
                  deriving(Monad, Functor, Applicative, MonadIO)

instance MonadReader InlEnv (Inl s) where
  ask = Inl ask
  local f (Inl m) = Inl (local f m)

-- | Inlining within a function body keeps track of the function's code growth
--   and number of endpoints
type InlStm a = Inl InlState a

-- | Inlining elsewhere just accumulates code growth info
type InlFun a = Inl () a

runInl :: InlFun a -> InlEnv -> IO a
runInl m e = do
  (x, _, _) <- runRWST (unInl m) e ()
  return x

instance Supplies (Inl s) (Ident Var) where
  fresh = Inl $ do 
    env <- ask
    liftIO $ supplyValue (varSupply env)

tellReturns :: NumReturns -> InlStm ()
tellReturns n = Inl $ RWST $ \_ s ->
  let s' = s `mappend` InlState n mempty
  in s' `seq` return ((), s', mempty)

tellReturn :: InlStm ()
tellReturn = tellReturns One

-- | Capture the number of return values produced by the computation
censorReturns :: InlStm a -> InlStm (NumReturns, a)
censorReturns (Inl m) = Inl $ RWST $ \env s -> do
  let InlState n_returns size = s
  (x, InlState local_n_returns size', ()) <- runRWST m env (InlState Zero size)
  return ((local_n_returns, x), InlState n_returns size', ())

-- | Given a local function definition and the number of endpoints it has,
--   assign its endpoints to the caller.
--
--   If the function is not a join point, it contributes no endpoints to
--   the enclosing function.  That is, if a continuation is grafted onto the 
--   enclosing function, it doesn't affect the function.
--   If this function is a join point, its endpoints are endpoints of the
--   enclosing function.
propagateLetrecReturn :: Fun -> NumReturns -> InlStm ()
propagateLetrecReturn f n
  | funConvention f == JoinCall = tellReturns n
  | otherwise                   = return ()

tellCodeGrowth :: CodeSize -> InlStm ()
tellCodeGrowth size = Inl $ RWST $ \_ s ->
  let s' = s `mappend` InlState mempty size
  in s' `seq` return ((), s', mempty)

-- | Do inlining in a function body
doFunctionBody :: InlStm a -> InlFun (NumReturns, CodeSize, a)
doFunctionBody (Inl m) = Inl $ RWST $ \env () -> do
  -- To get statistics for the function body, start processing with
  -- 'mempty' as the state.
  (x, InlState num_returns code_size, _) <- runRWST m env mempty

  -- Write out the code size so it will be accumulated by the caller.
  return ((num_returns, code_size, x), (), ())

-- | Do inlining on functions that appear inside a function body
doFunction :: InlFun a -> InlStm a
doFunction (Inl m) = Inl $ RWST $ \env s -> do
  (x, _, _) <- runRWST m env ()
  return (x, s, ())

renameParameter :: Var -> (Var -> Inl s a) -> Inl s a
renameParameter v f = do
  v' <- newClonedVar v
  local (insert v v') (f v')
  where
    insert v v' env =
      env {renaming = IntMap.insert (fromIdent $ varID v) v' $ renaming env}

renameParameters :: [Var] -> ([Var] -> Inl s a) -> Inl s a
renameParameters = withMany renameParameter

setReturns :: [ValueType] -> Inl s a -> Inl s a
setReturns rtypes m = local set_returns m
  where set_returns env = env {currentReturns = Just rtypes}

getReturns :: Inl s [ValueType]
getReturns = asks (from_just . currentReturns)
  where
    from_just (Just x) = x
    from_just Nothing  = internalError "getReturns: No return types"

clearReturns :: Inl s a -> Inl s a
clearReturns m = local clear_returns m
  where clear_returns env = env {currentReturns = Nothing}

renameVar :: Var -> Inl s Var
renameVar v = Inl $ RWST $ \env s ->
  let v' = fromMaybe v $ IntMap.lookup (fromIdent $ varID v) (renaming env)
  in v' `seq` return (v', s, mempty)

renameVal (VarV v) = VarV <$> renameVar v
renameVal (RecV r vs) = RecV r <$> mapM renameVal vs
renameVal (LitV l) = return $ LitV l

renameStaticData (StaticData v) = StaticData <$> renameVal v

renameAtom :: Atom -> InlStm Atom
renameAtom (ValA vs) =
  ValA <$> mapM renameVal vs
renameAtom (CallA cc op args) =
  CallA cc <$> renameVal op <*> mapM renameVal args
renameAtom (PrimA prim args) =
  PrimA prim <$> mapM renameVal args
renameAtom (PackA r args) =
  PackA r <$> mapM renameVal args
renameAtom (UnpackA r v) =
  UnpackA r <$> renameVal v

renameExport :: (Var, ExportSig) -> InlFun (Var, ExportSig)
renameExport (v, sig) = do
  v' <- renameVar v
  return (v', sig)

lookupInlinedFunction :: Var -> Inl s (Maybe (Fun, NumReturns))
lookupInlinedFunction v =
  asks (IntMap.lookup (fromIdent $ varID v) . functions)

-- | Consider the function for inlining.  If it's small enough, then inline it.
considerForInlining :: Var -> Fun -> NumReturns -> Inl s a -> Inl s a
considerForInlining v f num_returns m
  | willInline f = local (insert v (f, num_returns)) m
  | otherwise = m
  where
    insert v x env =
      env {functions = IntMap.insert (fromIdent $ varID v) x $ functions env}

    report_inlining = traceShow message

    message =
      hang (text "Will inline" <+> pprVar v <+> parens (text $ show num_returns)) 4
      (pprFun f)

-- Make this function NOINLINE so it can be CSE'd.
{-# NOINLINE willInline #-}
willInline f = funIsInlinable f && worthInlining f

-- | Return True if the function is judged /profitable/ to inline.
worthInlining f
  | funInlineRequest f = True
  | funUses f == OneUse = True
  | funConvention f == ClosureCall,
    Just sz <- fromCodeSize (funSize f) = sz < closureInlineCutoff
  | funConvention f == PrimCall,
    Just sz <- fromCodeSize (funSize f) = sz < primInlineCutoff
  | funConvention f == JoinCall,
    isTinyJoinPoint f = True
  | otherwise = False

-- | Always inline join points if the body is one of the following:
--
--   * A 'ValA' term
--   * A tail call to a join point
isTinyJoinPoint :: Fun -> Bool
isTinyJoinPoint f =
  case funBody f
  of ReturnE (ValA _)             -> True
     ReturnE (CallA JoinCall _ _) -> True
     _                            -> False

-- | Return True if it's possible to inline the function.
funIsInlinable f =
  -- Function must not use stack data
  funFrameSize f == 0
  
  -- (TEMPORARY) cannot inline a join point
  --  funConvention f /= JoinCall

-------------------------------------------------------------------------------
-- The actual inlining stage

-- | Inline a function at a specific callsite.
--
--   The function and continuation should be renamed before they are passed 
--   to this function.
inlineCall :: (Fun, NumReturns) -- ^ Function to inline
           -> [Val]             -- ^ Function arguments
           -> ContinuationCode  -- ^ Continuation of function call
           -> InlStm Stm
inlineCall x args cont =
  {-# SCC "inlineCall" #-} inlineCall' x args cont

inlineCall' (!f, n_returns) args cont
  | n_args == n_params =
      inlineSaturatedCall f n_returns args cont

  | n_args > n_params = do
      -- Inline a saturated call.  The saturated call returns a function.
      -- Apply the remaining arguments to that function.
      ret_var <- newAnonymousVar (PrimType OwnedType)
      let ret_call = closureCallA (VarV ret_var) (drop n_params args)
      app_cont <-
        case cont
        of IsTailCall -> do
             rtypes <- getReturns
             tellReturn         -- This continuation is an endpoint
             return $ HasContinuation [ret_var] rtypes (ReturnE ret_call)
           HasContinuation cont_vars cont_rtypes cont_stm ->
             let app_cont_stm = LetE cont_vars ret_call cont_stm
             in return $ HasContinuation [ret_var] cont_rtypes app_cont_stm
      inlineSaturatedCall f n_returns (take n_params args) app_cont

  | otherwise = do
      -- Undersaturated call.
      -- Create a local function and pass it to the continuation
      let fun_body = bindArguments args (take n_args $ funParams f) (funBody f)
          partial_app =
            mkFun (funConvention f) (funInlineRequest f) (funFrameSize f)
            (drop n_args $ funParams f) (funReturnTypes f) fun_body
      case cont of
        IsTailCall -> do
          partial_app_var <- newAnonymousVar (PrimType OwnedType)
          tellReturn            -- This is an endpoint
          return $
            LetrecE (NonRec (Def partial_app_var partial_app)) $
            ReturnE (ValA [VarV partial_app_var])
        HasContinuation [cont_var] cont_rtypes cont_stm 
          | PrimType OwnedType <- varType cont_var -> do
            -- This is not an endpoint.  If there are endpoints, they are 
            -- part of the continuation, 'cont_stm', and they have already
            -- been marked.
            return $
              LetrecE (NonRec (Def cont_var partial_app)) cont_stm
        HasContinuation {} ->
          -- Wrong number of return values
          internalError "inlineCall: Type error detected"
  where
    n_args = length args
    n_params = length $ funParams f

-- | Inline a function that is called with exactly the right number of 
--   arguments.
--
inlineSaturatedCall (!f) (!n_returns) args IsTailCall = do
  -- This many endpoints are inserted
  tellReturns n_returns
  return $ bindArguments args (funParams f) (funBody f)

--   If the function has one endpoint,
--   graft the continuation onto the endpoint.
--   Otherwise, turn the continuation into a join point.

inlineSaturatedCall (!f) (!n_returns) args (HasContinuation params rtypes stm) =
  case n_returns
  of Zero -> 
       -- The function has no endpoints; the continuation is unreachable
       -- and can be discarded.
       return $ bindArguments args (funParams f) (funBody f)
     One ->
       -- The function has one endpoint.  Graft the continuation onto the
       -- endpoint.
       return $ insertContinuation params stm $
         bindArguments args (funParams f) (funBody f)
     Many -> do
       -- Create a continuation function
       cont_name <- newAnonymousVar (PrimType OwnedType)
       let cont_function = closureFun params rtypes stm

       f_return_vars <- mapM newAnonymousVar (funReturnTypes f)
       let cont_call =
             ReturnE $ closureCallA (VarV cont_name) (map VarV f_return_vars)
       let inlined_body =
             -- Bind the function's parameters
             bindArguments args (funParams f) $
             -- Define the continuation function
             LetrecE (NonRec (Def cont_name cont_function)) $
             -- Insert a call to the continuation at the end of the
             -- inlined function body
             insertContinuation f_return_vars cont_call $ funBody f

       return inlined_body

-- | Bind inlined function parameters to argument values
bindArguments (arg:args) (param:params) e =
  LetE [param] (ValA [arg]) $ bindArguments args params e
bindArguments [] [] e = e
bindArguments _ _ _ = internalError "bindArguments: Wrong number of arguments"

-- | Insert 'call' at every return point in expression 'e', which is a
--   function body that has been inlined.
insertContinuation return_vars cont_code e = go e
  where
    go (LetE params rhs body) = LetE params rhs (go body)
    go (LetrecE defs body) = LetrecE (fmap go_local_function defs) (go body)
    go (SwitchE scr alts) = SwitchE scr [(tag, go s) | (tag, s) <- alts]

    -- Do not insert code after a call to a join point
    go join_call@(ReturnE (CallA JoinCall _ _)) = join_call
    go (ReturnE atom) = LetE return_vars atom cont_code
    go (ThrowE val) = ThrowE val

    -- If the local function is a join point,
    -- continuations will be inserted in the function body instead of
    -- after a call to the function.
    -- Other local functions are not modified.
    go_local_function def
      | funConvention (definiens def) == JoinCall =
          let Def v f = def
              f' = changeFunBody go f
          in Def v f'
      | otherwise = def

-------------------------------------------------------------------------------

-- | Count the number of endpoints a function has.
--
--   This function is only used for imported functions. 
--   For other functions, the number of endpoints is computed 
--   when the function's body is processed by 'inlineFun'.
--   Since 'inlineFun' is not called on imported functions, we use
--   'countReturns' to count the endpoints.
countReturns :: Fun -> NumReturns
countReturns f = count $ funBody f
  where
    count (LetE _ _ body) = count body
    count (LetrecE defs body) = count_defs defs `mappend` count body
    count (SwitchE _ alts) = mconcat [count s | (_, s) <- alts]
    count (ReturnE (CallA JoinCall _ _)) = Zero
    count (ReturnE _) = One
    count (ThrowE _) = Zero

    count_defs group = mconcat $ map count_def $ groupMembers group

    count_def (Def v f)
      | funConvention f == JoinCall = count $ funBody f
      | otherwise = Zero

-- | Perform inlining on a function body.
--   Returns the new function, the amount of code growth that occurred due
--   to inlining, and the number of endpoints in the function.
inlineFun :: Fun -> InlFun (Fun, NumReturns, CodeSize)
inlineFun f =
  setReturns (funReturnTypes f) $
  renameParameters (funParams f) $ \params -> do
    (n_returns, code_growth, body) <- doFunctionBody $ inline $ funBody f
    let f' = f { funSize = addCodeSize code_growth $ funSize f
               , funParams = params
               , funBody = body}
    return (f', n_returns, code_growth)

-- | Consider an atom for inlining.
--   If it shall be inlined, replace it with an inlined function.
--
--   If it won't be inlined, determine whether inlining may insert code at 
--   this point later.  If code is inserted, it will be inserted by
--   'insertContinuation'.
--
--   The arguments should be renamed before they are passed to this function.
inlineAtom :: Atom -> ContinuationCode -> InlStm Stm
inlineAtom atom cont =
  case atom
  of CallA cc (VarV op) args -> do
       inlined_function <- lookupInlinedFunction op
       case inlined_function of
          Nothing -> don't_inline
          Just x  -> inlineCall x args cont
     _ -> don't_inline
  where
    don't_inline =
      case cont
      of HasContinuation params _ k -> do
           return $ LetE params atom k
         IsTailCall -> do
           -- Is this a tail call to a join point?
           case atom of
             CallA JoinCall _ _ -> return ()
             _ -> tellReturn    -- Inlining may insert a tail call here
           return $ ReturnE atom

-- | Inlining performs the following steps at each statement:
--
-- 1. Rename variables.
--
-- 2. At function definitions, perform inlining inside the functions.  
--
-- 3. At function definitions, decide whether to inline the function.
--
-- 4. Perform inlining in subexpressions of 'let' and 'switch' statements.
--
-- 5. Inline function calls at 'let' statements.  The tail of the statement
--    becomes a local function.
inline :: Stm -> InlStm Stm
inline statement =
  case statement
  of LetE params rhs body   -> inlineLet params rhs body
     LetrecE defs body      -> inlineLetrec defs body
     SwitchE scrutinee alts -> inlineSwitch scrutinee alts
     ReturnE atom           -> inlineReturn atom
     ThrowE value           -> inlineThrow value

inlineLet params rhs body = do
  rhs' <- renameAtom rhs
  renameParameters params $ \params' -> do
    body' <- inline body
    rtypes <- getReturns
    inlineAtom rhs' $ HasContinuation params' rtypes body'
      
inlineLetrec defs body = inlineGroup defs (inline body)

inlineSwitch scrutinee alts = do
  scrutinee' <- renameVal scrutinee
  alts' <- mapM renameAlt alts
  return $ SwitchE scrutinee' alts'
  where
    renameAlt (l, s) = do
      s' <- inline s
      return (l, s')

inlineReturn atom = do
  atom' <- renameAtom atom
  inlineAtom atom' IsTailCall

inlineThrow value = do
  val' <- renameVal value
  return $ ThrowE val'

inlineGroup (NonRec (Def v f)) do_body = do
  -- Perform inlining inside the function
  (f', n_returns, code_growth) <- doFunction $ inlineFun f
  propagateLetrecReturn f' n_returns
  tellCodeGrowth code_growth

  -- If the function is a join point and will be inlined,
  -- then delete the function definition.  It will not be referenced
  -- after inlining.
  let delete_definition = willInline f' && funConvention f' == JoinCall

  -- Rename the bound variable and perform inlining in the body 
  renameParameter v $ \v' -> do
    body' <- considerForInlining v' f' n_returns do_body

    return $! if delete_definition
              then body'
              else LetrecE (NonRec (Def v' f')) body'

inlineGroup (Rec defs) do_body = do
  -- Rename bound variables
  renameParameters (map definiendum defs) $ \vs' -> do

    -- Perform renaming inside each function
    results <- doFunction $ mapM (inlineFun . definiens) defs
    let fs' = [f | (f, _, _) <- results]
        code_growth = mconcat [g | (_, _, g) <- results]
    sequence [propagateLetrecReturn f n | (f, n, _) <- results]
    tellCodeGrowth code_growth

    -- Recursive functions may not be inlined
    body' <- do_body
    return $ LetrecE (Rec (zipWith Def vs' fs')) body'

-- Globals are not renamed during inlining, because the global variable
-- may be mentioned in the import list (which isn't renamed).
-- This deviation in behavior is kind of a hack that should be fixed.
inlineGlobalGroup (NonRec (GlobalFunDef (Def v f))) do_body = do
  -- Perform inlining inside the function
  (f', n_returns, _) <- inlineFun f
  body' <- considerForInlining v f' n_returns do_body
  return (NonRec (GlobalFunDef (Def v f')), body')

inlineGlobalGroup (NonRec (GlobalDataDef (Def v dat))) do_body = do
  dat' <- renameStaticData dat
  body' <- do_body
  return (NonRec (GlobalDataDef (Def v dat')), body')

inlineGlobalGroup (Rec defs) do_body = do
  -- Perform renaming inside each function or global datum
  fs' <- mapM inline_global defs

  -- Recursive functions may not be inlined
  body' <- do_body
  let vs = map globalDefiniendum defs
  let new_defs = zipWith mk_global_def vs fs'
  return (Rec new_defs, body')
  where
    inline_global (GlobalFunDef (Def _ f)) = do
      (f', _, _) <- inlineFun f
      return $ Left f'

    inline_global (GlobalDataDef (Def _ d)) = Right `liftM` renameStaticData d
    mk_global_def v (Left f) = GlobalFunDef (Def v f)
    mk_global_def v (Right d) = GlobalDataDef (Def v d)

inlineGlobals :: [Group GlobalDef] -> [(Var, ExportSig)]
              -> InlFun ([Group GlobalDef], [(Var, ExportSig)])
inlineGlobals defss exports =
  {-# SCC "inlineGlobals" #-} do_defs defss
  where
    do_defs (defs : defss) = do
      (defs', (defss', exports')) <-
        inlineGlobalGroup defs $ do_defs defss
      return (defs' : defss', exports')
    
    do_defs [] = do
      exs <- mapM renameExport exports
      return ([], exs)

-- | Make all imported functions that have function bodies inlinable
makeImportsInlinable :: [Import] -> InlinedFunctions
makeImportsInlinable imports =
  IntMap.fromList $ mapMaybe get_imported_function imports
  where
    get_imported_function impent =
      case impent
      of ImportClosureFun _ (Just f) | willInline f ->
           Just (fromIdent $ varID $ importVar impent, (f, countReturns f))
         ImportPrimFun _ _ (Just f) | willInline f ->
           Just (fromIdent $ varID $ importVar impent, (f, countReturns f))
         _ -> Nothing

inlineModule :: Module -> IO Module
inlineModule mod =
  withTheLLVarIdentSupply $ \var_ids -> do
    -- Allow imported functions to be inlined
    let import_map = makeImportsInlinable (moduleImports mod)

    -- Do inlining
    let env = InlEnv var_ids import_map emptyRenaming Nothing
    -- putStrLn "Before inlineModule"
    -- print $ pprModule mod
    (globals, exports) <-
      runInl (inlineGlobals (moduleGlobals mod) (moduleExports mod)) env
    let new_mod = mod {moduleGlobals = globals, moduleExports = exports}
    --putStrLn "After inlineModule"
    --print $ pprModule new_mod
        
    -- Rename so that all inlined variables are unique
    runFreshVarM var_ids $
      LowLevel.Rename.renameModule LowLevel.Rename.RenameLocals
      LowLevel.Rename.emptyRenaming new_mod
