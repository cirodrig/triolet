
{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleInstances #-}
module LowLevel.Inlining2 where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import qualified Data.IntMap as IntMap
import Data.Maybe

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

-- | The set of functions that can be inlined
type InlinedFunctions = IntMap.IntMap Fun

-- | The continuation of a function call.
--   Inlining may turn the continuation into a local function.
data ContinuationCode =
    HasContinuation [ParamVar] [ValueType] Stm
  | IsTailCall

data NumReturns = Zero | One | Many

addOne Zero = One
addOne _    = Many

data InlEnv =
  InlEnv { varSupply :: !(IdentSupply Var)
         , functions :: InlinedFunctions
         , renaming :: Renaming
           -- | Return types of the current function.  'Nothing' when not
           --   processing a function body.
         , currentReturns :: !(Maybe [ValueType])
         -- , continuation :: !(Maybe ([Var], Stm))
         }

newtype Inl a = Inl {unInl :: InlEnv -> NumReturns -> IO (a, NumReturns)}

instance Functor Inl where
  fmap = liftM

instance Monad Inl where
  return x = Inl $ \_ r -> return (x, r)
  m >>= k = Inl $ \env r -> do
    (x, r') <- unInl m env r
    unInl (k x) env r'

instance Applicative Inl where
  pure = return
  (<*>) = ap

instance MonadIO Inl where
  liftIO m = Inl $ \_ r -> do
    x <- m
    return (x, r)

runInl m e = unInl m e Zero

instance Supplies Inl (Ident Var) where
  fresh = Inl $ \env r -> do
    x <- supplyValue (varSupply env)
    return (x, r)

local :: (InlEnv -> InlEnv) -> Inl a -> Inl a
local f (Inl m) = Inl $ \env r -> m (f env) r

asks :: (InlEnv -> a) -> Inl a
asks f = Inl $ \env r -> return (f env, r)

tellReturn :: Inl ()
tellReturn = Inl $ \_ r -> return ((), addOne r)

getNumReturns :: Inl a -> Inl (NumReturns, a)
getNumReturns (Inl f) = Inl $ \env r -> do
  (x, local_r) <- f env Zero
  return ((local_r, x), r)

renameParameter :: Var -> (Var -> Inl a) -> Inl a
renameParameter v f = do
  v' <- newClonedVar v
  local (insert v v') (f v')
  where
    insert v v' env =
      env {renaming = IntMap.insert (fromIdent $ varID v) v' $ renaming env}

renameParameters = withMany renameParameter

setReturns :: [ValueType] -> Inl a -> Inl a
setReturns rtypes m = local set_returns m
  where set_returns env = env {currentReturns = Just rtypes}

getReturns :: Inl [ValueType]
getReturns = asks (from_just . currentReturns)
  where
    from_just (Just x) = x
    from_just Nothing  = internalError "getReturns: No return types"

clearReturns :: Inl a -> Inl a
clearReturns m = local clear_returns m
  where clear_returns env = env {currentReturns = Nothing}

renameVar :: Var -> Inl Var
renameVar v = Inl $ \env r ->
  let v' = fromMaybe v $ IntMap.lookup (fromIdent $ varID v) (renaming env)
  in v' `seq` return (v', r)

renameVal (VarV v) = VarV <$> renameVar v
renameVal (RecV r vs) = RecV r <$> mapM renameVal vs
renameVal (LitV l) = return $ LitV l

renameStaticData (StaticData v) = StaticData <$> renameVal v

renameAtom :: Atom -> Inl Atom
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

renameExport (v, sig) = do
  v' <- renameVar v
  return (v', sig)

lookupInlinedFunction :: Var -> Inl (Maybe Fun)
lookupInlinedFunction v =
  asks (IntMap.lookup (fromIdent $ varID v) . functions)

-- | Consider the function for inlining.  If it's small enough, then inline it.
considerForInlining :: Var -> Fun -> Inl a -> Inl a
considerForInlining v f m
  | willInline f = local (insert v f) m
  | otherwise = m
  where
    insert v f env =
      env {functions = IntMap.insert (fromIdent $ varID v) f $ functions env}

willInline f = funIsInlinable f && worthInlining f

-- | Return True if the function is judged /profitable/ to inline.
worthInlining f
  | funInlineRequest f = True
  | funUses f == OneUse = True
  | funConvention f == ClosureCall,
    Just sz <- fromCodeSize (funSize f) = sz < closureInlineCutoff
  | funConvention f == PrimCall,
    Just sz <- fromCodeSize (funSize f) = sz < primInlineCutoff
  | otherwise = False

-- | Return True if it's possible to inline the function.
funIsInlinable f = False &&
  -- Function must not use stack data
  funFrameSize f == 0 &&
  
  -- (TEMPORARY) cannot inline a join point
  funConvention f /= JoinCall

-------------------------------------------------------------------------------
-- The actual inlining stage

-- | Inline a function at a specific callsite.
--
--   The function and continuation should be renamed before they are passed 
--   to this function.
inlineCall :: Fun              -- ^ Function to inline
           -> [Val]            -- ^ Function arguments
           -> ContinuationCode -- ^ Continuation of function call
           -> Inl Stm
inlineCall f args cont
  | n_args == n_params =
      inlineSaturatedCall f args cont
  | n_args > n_params = do
      -- Inline a saturated call.  The saturated call returns a function.
      -- Apply the remaining arguments to that function.
      ret_var <- newAnonymousVar (PrimType OwnedType)
      let ret_call = closureCallA (VarV ret_var) (drop n_params args)
      app_cont <-
        case cont
        of IsTailCall -> do
             rtypes <- getReturns
             return $ HasContinuation [ret_var] rtypes (ReturnE ret_call)
           HasContinuation cont_vars cont_rtypes cont_stm ->
             let app_cont_stm = LetE cont_vars ret_call cont_stm
             in return $ HasContinuation [ret_var] cont_rtypes app_cont_stm
      inlineSaturatedCall f (take n_params args) app_cont
  | n_args < n_params = do
      -- Create a local function and pass it to the continuation
      let fun_body = bindArguments args (take n_args $ funParams f) (funBody f)
          partial_app =
            mkFun (funConvention f) (funInlineRequest f) (funFrameSize f)
            (drop n_args $ funParams f) (funReturnTypes f) fun_body
      case cont of
        IsTailCall -> do
          partial_app_var <- newAnonymousVar (PrimType OwnedType)
          return $
            LetrecE (NonRec (Def partial_app_var partial_app)) $
            ReturnE (ValA [VarV partial_app_var])
        HasContinuation [cont_var] cont_rtypes cont_stm 
          | PrimType OwnedType <- varType cont_var -> do
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
inlineSaturatedCall f args IsTailCall =
  return $ bindArguments args (funParams f) (funBody f)

inlineSaturatedCall f args (HasContinuation params rtypes stm) = do
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

-- | Perform inlining on a function body
inlineFun :: Fun -> Inl Fun
inlineFun f =
  setReturns (funReturnTypes f) $
  renameParameters (funParams f) $ \params -> do
    body <- inline $ funBody f
    return $ f {funParams = params, funBody = body}

-- | Consider an atom for inlining.
--   If it shall be inlined, replace it with an inlined function.
--
--   The arguments should be renamed before they are passed to this function.
inlineAtom :: Atom -> ContinuationCode -> Inl Stm
inlineAtom atom cont =
  case atom
  of CallA cc (VarV op) args -> do
       inlined_function <- lookupInlinedFunction op
       case inlined_function of
          Nothing -> don't_inline
          Just f  -> inlineCall f args cont
     _ -> don't_inline
  where
    don't_inline =
      case cont
      of HasContinuation params _ k -> do
           return $ LetE params atom k
         IsTailCall -> do                 
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
inline :: Stm -> Inl Stm
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
      
inlineLetrec (NonRec (Def v f)) body = do
  -- Perform inlining inside the function
  f' <- inlineFun f
  renameParameter v $ \v' -> do
    body' <- considerForInlining v' f' $ inline body
    return $ LetrecE (NonRec (Def v' f')) body'

inlineLetrec defs body = do
  (defs', body') <- inlineGroup defs (inline body)
  return $ LetrecE defs' body'

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
  f' <- inlineFun f
  renameParameter v $ \v' -> do
    body' <- considerForInlining v' f' do_body
    return (NonRec (Def v' f'), body')

inlineGroup (Rec defs) do_body = do
  -- Rename bound variables
  renameParameters (map definiendum defs) $ \vs' -> do
    -- Perform renaming inside each function
    fs' <- mapM (inlineFun . definiens) defs

    -- Recursive functions may not be inlined
    body' <- do_body
    return (Rec (zipWith Def vs' fs'), body')

-- Globals are not renamed during inlining, because the global variable
-- may be mentioned in the import list (which isn't renamed).
-- This deviation in behavior is kind of a hack that should be fixed.
inlineGlobalGroup (NonRec (GlobalFunDef (Def v f))) do_body = do
  -- Perform inlining inside the function
  f' <- inlineFun f
  body' <- considerForInlining v f' do_body
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
    inline_global (GlobalFunDef (Def _ f)) = Left `liftM` inlineFun f
    inline_global (GlobalDataDef (Def _ d)) = Right `liftM` renameStaticData d
    mk_global_def v (Left f) = GlobalFunDef (Def v f)
    mk_global_def v (Right d) = GlobalDataDef (Def v d)

inlineGlobals :: [Group GlobalDef] -> [(Var, ExportSig)]
              -> Inl ([Group GlobalDef], [(Var, ExportSig)])
inlineGlobals defss exports = do_defs defss
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
           Just (fromIdent $ varID $ importVar impent, f)
         ImportPrimFun _ _ (Just f) | willInline f ->
           Just (fromIdent $ varID $ importVar impent, f)
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
    ((globals, exports), _) <-
      runInl (inlineGlobals (moduleGlobals mod) (moduleExports mod)) env
    let new_mod = mod {moduleGlobals = globals, moduleExports = exports}
    --putStrLn "After inlineModule"
    --print $ pprModule new_mod
        
    -- Rename so that all inlined variables are unique
    runFreshVarM var_ids $
      LowLevel.Rename.renameModule LowLevel.Rename.RenameLocals
      LowLevel.Rename.emptyRenaming new_mod
