{-| Normalize tail calls.

This compiler pass finds functions that can be converted to tail-call form
by merging their continuations.  The continuations have to be syntactically
identical and consist of a single function call.

For example, the following code has two calls to 'f'.  Each call is followed
by a call to 'g'.  Since the calls to 'g' are identical, we can merge them
both into a single call that goes in the body of 'f'.

> letfun nonrec
>   f x =
>     x + 1
> in case y of
>   0. u <- f 1
>      g u z
>   1. v <- f 2
>      g v z

After transformation:

> letfun nonrec
>   f x = 
>     w <- x + 1 
>     g w z
> in case y of
>   0. f 1
>   1. f 2

-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
module LowLevel.NormalizeTail(normalizeTailCalls)
where

import Control.Monad.Reader
import qualified Data.IntMap as IntMap
import qualified Data.List as List
import Data.IORef
import Text.PrettyPrint.HughesPJ

import Common.Error
import Common.Identifier
import Common.Supply
import LowLevel.CodeTypes
import LowLevel.FreshVar
import LowLevel.Print
import LowLevel.Rename
import LowLevel.Syntax
import Globals

-- | Test whether two values are equal
sameVal :: Val -> Val -> Bool
sameVal (VarV v1)    (VarV v2)    = v1 == v2
sameVal (RecV _ vs1) (RecV _ vs2) = length vs1 == length vs2 &&
                                    and (zipWith sameVal vs1 vs2)
sameVal (LitV l1)    (LitV l2)    = l1 == l2
sameVal _ _                       = False

-- | A specific tail-call pattern, occurring in a function whose
--   return type is RETURNS
--
-- > let PARAMS = ... in
-- > call CONV TARGET ARGS
--
--   Some parts of the code require a /renamed/ tail-call, which is one
--   where the @PARAMS@ have been renamed to fresh variables.
data TailCall =
  TailCall
  { tcParams :: [ParamVar]
  , tcReturns :: [ValueType]
  , tcConv :: !CallConvention
  , tcTarget :: Val
  , tcArgs :: [Val]
  }

pprTailCall (TailCall params returns cc target args) =
  let binder = sep $ punctuate (text ",") $ map pprVarLong params
      body = pprAtom (CallA cc target args)
  in text "let" <+> binder <+> text "<- _" $$ body

-- | Get the set of free variables in a tail call
freeVars :: TailCall -> [Var]
freeVars (TailCall params _ _ tgt args) =
  List.nub (concatMap fvVal (tgt : args)) List.\\ params
  where
    fvVal :: Val -> [Var]
    fvVal (VarV v)    = [v]
    fvVal (RecV _ vs) = concatMap fvVal vs
    fvVal (LitV _)    = []

-- | Rename bound variables in a tail call
freshenTailCall :: Supplies m (Ident Var) => TailCall -> m TailCall
freshenTailCall (TailCall params returns conv target args) = do
  params' <- mapM newClonedVar params
  let rn = mkRenaming $ zip params params'
      target' = renameVal RenameEverything rn target
      args' = map (renameVal RenameEverything rn) args
  return $ TailCall params' returns conv target' args'

-- | Rename free variables in a tail call.
--   The given renaming should not mention bound variables.
renameTailCall :: Renaming -> TailCall -> TailCall
renameTailCall rn tc =
  tc { tcTarget = renameVal RenameEverything rn $ tcTarget tc
     , tcArgs = map (renameVal RenameEverything rn) $ tcArgs tc}

-- | Continuations of a function.
--   Continuations form a lattice.
data Cont = Top | TC {-# UNPACK #-} !TailCall | Bot

pprCont Top     = text "Top"
pprCont (TC tc) = pprTailCall tc
pprCont Bot     = text "Bot"

-- | Join two tail call patterns.  Rename the second one if
--   it becomes the joined value.
joinCont :: Supplies m (Ident Var) => Cont -> Cont -> m Cont
joinCont x@(TC tc1) (TC tc2) | sameTC tc1 tc2 = return x
joinCont Bot        Top                       = return Top
joinCont Bot        (TC tc)                   = liftM TC $ freshenTailCall tc
joinCont x          Bot                       = return x
joinCont _          _                         = return Top

-- | Check whether two tail-call patterns are equal.
--   The first tail-call pattern must have been renamed so that bound
--   variables don't shadow free variables. 
--   We can assume that the return types are equal.
sameTC :: TailCall -> TailCall -> Bool
sameTC (TailCall pvs1 _ c1 target1 args1)
       (TailCall pvs2 _ c2 target2 args2) =
  c1 == c2 &&
  length pvs1 == length pvs2 &&
  sameVal target1 target' &&
  length args1 == length args' &&
  and (zipWith sameVal args1 args')
  where
    -- Rename the second pattern to match the first
    rn      = mkRenaming $ zip pvs2 pvs1
    target' = renameVal RenameEverything rn target2
    args'   = map (renameVal RenameEverything rn) args2

-- | An environment associates each local closure-call function
--   with an arity and a continuation set.
type Conts = IntMap.IntMap (Int, IORef Cont)

data Env =
  Env
  { envVarSupply :: !(IdentSupply Var)
    -- | Return types of the current function
  , envReturns :: [ValueType]
    -- | Known continuations of local 'ClosureCall' functions.
    --   All in-scope local functions are in the map.  Each function is
    --   initialized to Bot.
  , envConts :: !Conts
    -- | The set of in-scope variables.  Variables are appended to the
    --   head of the list.
  , envInScope :: [Var]
  }

initialEnv :: IdentSupply Var
           -> [Var]           -- ^ Imported variables
           -> Env
initialEnv var_ids global_vars =
  Env { envVarSupply = var_ids
      , envReturns = internalError "envReturns: Not in a function"
      , envConts = IntMap.empty
      , envInScope = global_vars
      }

newtype NT a = NT {unNT :: ReaderT Env IO a}

instance Monad NT where
  return x = NT (return x)
  NT m >>= k = NT (m >>= unNT . k)

instance Supplies NT (Ident Var) where
  fresh = NT $ ReaderT $ \env -> supplyValue $ envVarSupply env

liftFreshVarM :: FreshVarM a -> NT a
liftFreshVarM m = NT $ ReaderT $ \env -> runFreshVarM (envVarSupply env) m

addLocals :: [Var] -> NT a -> NT a
addLocals params (NT m) = NT $ local insert_params m
  where
    insert_params env = env {envInScope = params ++ envInScope env}

getInScope :: NT [Var]
getInScope = NT $ asks envInScope

setReturnTypes rts (NT f) = NT $ local insert_params f
  where
    insert_params env = env {envReturns = rts}

addCont :: Var -> Int -> NT a -> NT (Cont, a)
addCont v arity (NT m) = NT $ ReaderT $ \env -> do
  -- Initialize to _|_
  ref <- newIORef Bot
  let key = fromIdent $ varID v
      local_env = env {envConts = IntMap.insert key (arity, ref) $
                                  envConts env}
  x <- runReaderT m local_env

  -- Read final value
  final_cont <- readIORef ref
  return (final_cont, x)

updateContTop :: Var -> NT ()
updateContTop target = NT $ ReaderT $ \env ->
  -- Look up the continuations in the environment
  case IntMap.lookup (fromIdent $ varID target) $ envConts env
  of Nothing  -> return ()        -- Not being tracked
     Just (_, ref) -> writeIORef ref Top

updateCont :: Var -> Int -> [ParamVar] -> CallConvention -> Val -> [Val] -> NT ()
updateCont target n_args params cc k k_args = NT $ ReaderT $ \env ->
  -- Look up the continuations in the environment
  case IntMap.lookup (fromIdent $ varID target) $ envConts env
  of Nothing  -> return ()        -- Not being tracked
     Just (arity, ref)
       | n_args == arity -> do
         -- Join with old value
         old_val <- readIORef ref
         let upd_val = TC $ TailCall params (envReturns env) cc k k_args
         new_val <- runFreshVarM (envVarSupply env) $ joinCont old_val upd_val
         writeIORef ref new_val
       | otherwise ->
         -- Over- or under-saturated; set continuation to Top
         writeIORef ref Top

scanVal :: Val -> NT ()
scanVal (VarV v)    = updateContTop v
scanVal (RecV _ vs) = scanVals vs
scanVal (LitV _)    = return ()

scanVals vs = mapM_ scanVal vs

scanAtom :: Atom -> NT ()
scanAtom (ValA vs)      = scanVals vs
scanAtom (CallA _ v vs) = scanVal v >> scanVals vs
scanAtom (PrimA _ vs)   = scanVals vs
scanAtom (PackA _ vs)   = scanVals vs
scanAtom (UnpackA _ v)  = scanVal v

-- | Perform a pass over a program.  The pass detects whether any
--   local functions are called, and if so, normalizes them.
scan :: Stm -> NT Stm
scan stm =
  case stm
  of LetE params atom@(CallA ClosureCall (VarV tgt) call_args) stm'@(ReturnE (CallA cc k k_args))
       | cc == PrimCall || cc == ClosureCall -> do
           scanVals call_args
           updateCont tgt (length call_args) params cc k k_args
           k' <- addLocals params $ scan stm'
           return $ LetE params atom k'

     LetE params atom stm' -> do
       scanAtom atom
       LetE params atom `liftM` addLocals params (scan stm')

     LetrecE grp stm -> scanGroup grp stm
     SwitchE scr alts -> scanVal scr >> SwitchE scr `liftM` mapM scan_alt alts
     ReturnE atom -> scanAtom atom >> return stm
     ThrowE v -> scanVal v >> return stm
  where
    scan_alt (tag, stm) = do
      stm' <- scan stm
      return (tag, stm')

scanGroup (NonRec (Def v f)) body = do
  -- Do the body of the letrec
  let arity = length $ funParams f
  (k, body') <- addCont v arity $ addLocals [v] $ scan body

  -- If f can be normalized, then normalize.
  (f', body'') <-
    case k
    of TC tail_call -> do
         unless (funConvention f == ClosureCall) $
            internalError "Attempted to normalize non-closure function"

         (f', captured) <- normalizeReturn tail_call f
         let body'' = normalizeCalls v captured body'
         return (f', body'')
       _ -> return (f, body')

  -- Do the body of f
  f'' <- scanFun f'
  return $ LetrecE (NonRec (Def v f'')) body''

scanGroup (Rec defs) body = do
  let definienda = map definiendum defs
  addLocals definienda $ do
    -- Scan the functions and the body
    definientia <- mapM (scanFun . definiens) defs
    body' <- scan body
    let defs' = zipWith Def definienda definientia
    return $ LetrecE (Rec defs') body'

-- | Scan and update the body of a function
scanFun f =
  addLocals (funParams f) $ setReturnTypes (funReturnTypes f) $ do
    body' <- scan $ funBody f
    return $ f {funBody = body'}

scanGlobalDef (GlobalFunDef def) = do
  -- Rename local variables in the function. 
  -- We do this to avoid name ambiguity when comparing 'TailCall' values
  -- taken from different paths.
  Def v f <- liftFreshVarM $ renameInFunDef RenameLocals def
  
  -- Normalize tail calls inside this function
  f' <- scanFun f
  return $ GlobalFunDef (Def v f')

scanGlobalDef d@(GlobalDataDef _) = return d

scanGlobalGroup grp k =
  case grp
  of NonRec def -> do
       def' <- scanGlobalDef def
       addLocals [globalDefiniendum def] $ k (NonRec def')
     Rec defs -> addLocals (map globalDefiniendum defs) $ do
       defs' <- mapM scanGlobalDef defs
       k (Rec defs')

scanGlobalGroups (g:gs) =
  scanGlobalGroup g $ \g' -> do
    gs' <- scanGlobalGroups gs
    return (g' : gs')

scanGlobalGroups [] = return []

normalizeTailCalls :: Module -> IO Module
normalizeTailCalls mod =
  withTheLLVarIdentSupply $ \var_ids -> do
    let env = initialEnv var_ids (map importVar $ moduleImports mod)
    globals' <- runReaderT (unNT (scanGlobalGroups (moduleGlobals mod))) env
    return $ mod {moduleGlobals = globals'}

-- | Normalize function calls by converting them to tail calls.
--
--   Any expression of the form @let ... = F ARGS@
--   will be replaced by @F (CAPTURED ++ ARGS)@.
normalizeCalls :: Var           -- ^ Callee to normalize
               -> [Var]         -- ^ Captured variables
               -> Stm           -- ^ Statement to transform
               -> Stm           -- ^ Statement with normalized calls
normalizeCalls f_name captured e = go e
  where
    captured_values = map VarV captured
    go (LetE params (CallA conv (VarV target) args) body)
      | target == f_name =
          ReturnE $ CallA conv (VarV target) (captured_values ++ args)
    go (LetE params rhs body) = LetE params rhs $ go body
    go (LetrecE defs body) = LetrecE (fmap go_local_function defs) (go body)
    go (SwitchE scr alts) = SwitchE scr [(tag, go s) | (tag, s) <- alts]
    go e@(ReturnE _) = e
    go e@(ThrowE _) = e

    go_local_function def =
      let Def v f = def in Def v (changeFunBody go f)

-- | Normalize return points of a function by inserting the tail call.
--   Compute and return the set of captured variables.
normalizeReturn :: TailCall -> Fun -> NT (Fun, [Var])
normalizeReturn tail_call f = do
  -- Free variables that are not in scope here are renamed, and they
  -- become new function parameters
  in_scope <- getInScope
  let tc_fv = freeVars tail_call
      captured_fv = filter (`List.notElem` in_scope) tc_fv
  captured_params <- mapM newClonedVar captured_fv
  let TailCall tc_params tc_returns tc_cc tc_target tc_args =
        renameTailCall (mkRenaming $ zip captured_fv captured_params) tail_call

  -- Insert a tail call into all callees
  let tail_call = ReturnE $ CallA tc_cc tc_target tc_args
      new_body = insertContinuation tc_params tail_call $ funBody f

  -- Create new function
  let new_params = captured_params ++ funParams f
      new_returns = tc_returns
      new_f = f {funParams = new_params
                , funReturnTypes = tc_returns
                , funBody = new_body}
  return (new_f, captured_params)

-- | Insert 'call' at every return point in expression 'e'
insertContinuation :: [ParamVar] -> Stm -> Stm -> Stm
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
