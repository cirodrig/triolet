{-| Expression flattening turns nested expressions into non-nested ones,
    increasing opportunities for subsequent optimizations.

Rafts are extracted from:

1. Size parameters
2. Arguments of data constructors
3. Callees and arguments of function calls
4. Right-hand-sides of let expressions
5. Bodies of letfun-bound initializer functions
6. The scrutinee of case expressions

* Variable name hygiene

Because this module moves variable bindings around, it also takes measures
to prevent variable name shadowing.

As an example of shadowing, consider the following expression that
contains two non-nested bindings of 'x'.

> f (case x of C z. z) (case y of C z. z)

Flattening will rebuild this expression, pushing code under bindings, 
as shown below.  The \"HOLE\" stands for the location where code is pushed.
Since @f@ is a simple variable, flattening cannot simplify it further.
The first parameter of the call to @f@ is flattened by turning the case
expression into a 'Raft'.

> case x of C z. HOLE

Then the next parameter is flattened, extending the 'Raft'.  Because @z@
is in scope here, it gets renamed.

> case x of C z. case y of C z'. HOLE

Finally, the simplified application is put into the hole.

> case x of C z. case y of C z'. f z z'

As this example shows, variables are renamed in a single pass that's
combined with the other steps of flattening.  Flattening carries around
a renaming that it applies to expressions as needed.  The principle is that,
when we're ready to flatten an expression, all the in-scope variables are
visible in the renaming and the type environment, so we need to rename a 
bound variable only if it's found in these two data structures.

There is an additional rule for function bindings.
In some cases, a function binding may be pushed into a 'Raft' depending
on what variables the 'Raft' mentions.
That is, we choose between producing
@\x. let y = FOO in BAR@ and producing @let y = FOO in \x. BAR@,
depeding on whether expression @FOO@ mentions the bound variable @x@.
To keep the process simple, we unconditionally rename @x@ in this case
before deciding whether to push it inside the binding.
-}

{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving, RankNTypes #-}
module SystemF.Flatten(flattenModule)
where

import Prelude hiding(mapM)
import Control.Applicative
import Control.Monad hiding(mapM)
import Control.Monad.Reader hiding(mapM)
import Control.Monad.Writer hiding(mapM)
import Data.List
import qualified Data.Set as Set
import Data.Maybe
import Data.Monoid
import Data.Traversable
import Debug.Trace
import Text.PrettyPrint.HughesPJ hiding(float)

import Common.Error
import Common.Identifier
import Common.MonadLogic
import Common.Supply
import SystemF.Rename
import SystemF.Syntax
import SystemF.Raft
import SystemF.TypecheckMem
import SystemF.MemoryIR
import SystemF.PrintMemoryIR
import Type.Environment
import Type.Type
import qualified Type.Rename as Rename
import Type.Rename(rename, Renaming)
import Globals
import GlobalVar

-- | Debugging messages
context s m = do liftIO $ putStrLn ("Begin " ++ s)
                 x <- m
                 liftIO $ putStrLn ("End   " ++ s)
                 return x

-- | Return True if the expression is a trivial expression. 
--   A trivial expression is a variable or literal.
isTrivialExp :: ExpM -> Bool
isTrivialExp (ExpM e) = 
  case e
  of VarE {} -> True
     LitE {} -> True
     _       -> False

-- | Give a new name to a variable if the current name is already in scope.
freshenIfInEnvironment :: Renaming -> Var -> UnboxedTypeEvalM (Renaming, Var)
freshenIfInEnvironment rn v
  -- Is it in the renaming's domain?
  | isJust $ Rename.lookup v rn = rename_binder

  -- Is it in the type environment?
  | otherwise = do mt <- lookupType v
                   if isJust mt then rename_binder else no_change
  where
    no_change = return (rn, v)
    rename_binder = do v' <- newClonedVar v
                       return (Rename.extend v v' rn, v')

-------------------------------------------------------------------------------
-- Variable renaming and type environment maintenance

-- | Flattening involves renaming and type inference
newtype F a = F {unF :: ReaderT Renaming UnboxedTypeEvalM a}
             deriving(Functor, Applicative, Monad, MonadIO)

runF m = runReaderT (unF m) Rename.empty

instance Supplies F (Ident Var) where
  fresh = F $ lift fresh

instance TypeEnvMonad F where
  type EvalBoxingMode F = UnboxedMode
  getTypeEnv = F $ lift getTypeEnv
  liftTypeEnvM m = F $ lift $ liftTypeEnvM m

instance EvalMonad F where
  liftTypeEvalM m = F $ lift $ liftTypeEvalM m

class (EvalMonad m, EvalBoxingMode m ~ UnboxedMode) => FlattenMonad m where
  -- | Get the current renaming
  getRenaming :: m Renaming

  -- | Set the current renaming
  setRenaming :: Renaming -> m a -> m a

  -- | Rename a value using the current renaming
  renameF :: Rename.Renameable a => a -> m a

instance FlattenMonad F where
  getRenaming = F ask
  setRenaming rn (F m) = F (local (const rn) m)
  renameF x = F (asks (flip rename x))

-- | Rename a binder and add the bound variable to the environment.
withBinder :: FlattenMonad m => Binder -> (Binder -> m a) -> m a
withBinder (v ::: t) f = do
  rn <- getRenaming
  (rn', v') <- liftTypeEvalM $ freshenIfInEnvironment rn v
  let b' = v' ::: rename rn t
  setRenaming rn' $ assumeBinder b' $ f b'

withBinders = withMany withBinder

withDeConInst :: FlattenMonad m => DeConInst -> (DeConInst -> m a) -> m a
withDeConInst dc f =
  case dc
  of VarDeCon op ty_args ex_types -> do
       ty_args' <- renameF ty_args
       withBinders ex_types $ \ex_types' ->
          f (VarDeCon op ty_args' ex_types')
     TupleDeCon ty_args -> do
       ty_args' <- renameF ty_args
       f (TupleDeCon ty_args')

withTyParam :: FlattenMonad m => TyPat -> (TyPat -> m a) -> m a
withTyParam (TyPat b) m = withBinder b (m . TyPat)

withTyParams :: FlattenMonad m => [TyPat] -> ([TyPat] -> m a) -> m a
withTyParams = withMany withTyParam

withPatM :: FlattenMonad m => PatM -> (PatM -> m a) -> m a
withPatM (PatM b u) m = withBinder b $ \b' -> m (PatM b' u)

withMaybePatM Nothing  f = f Nothing
withMaybePatM (Just p) f = withPatM p (f . Just)

withPatMs :: FlattenMonad m => [PatM] -> ([PatM] -> m a) -> m a
withPatMs = withMany withPatM

-------------------------------------------------------------------------------
-- Generating and moving code rafts

-- | A flattening computation that extracts some code into a raft.
--   The result of flattening is normally a simplified piece of code 
--   that goes inside the raft.
--
--   The functions 'anchor' and 'anchorAll' run an 'FRaft' computation
--   and put its result inside the raft that is produced.
newtype FRaft a = FRaft (WriterT Raft F a)
              deriving(Functor, Applicative, Monad, MonadIO)

instance Supplies FRaft (Ident Var) where
  fresh = liftF fresh

instance TypeEnvMonad FRaft where
  type EvalBoxingMode FRaft = UnboxedMode
  getTypeEnv = liftF getTypeEnv
  liftTypeEnvM m = liftF $ liftTypeEnvM m

instance EvalMonad FRaft where
  liftTypeEvalM m = liftF $ liftTypeEvalM m

instance FlattenMonad FRaft where
  getRenaming = liftF getRenaming
  setRenaming rn (FRaft (WriterT m)) = FRaft $ WriterT $ setRenaming rn m
  renameF x = liftF $ renameF x

runFRaft (FRaft m) = runWriterT m

liftF :: F a -> FRaft a
liftF m = FRaft $ lift m

-- | Prohibit floating here.  It's a run-time error if any code is moved past
--   this point.
noFloat :: FRaft a -> F a
noFloat (FRaft m) = do
  (x, w) <- runWriterT m
  case w of Here -> return x
            _ -> internalError "noFloat"

-- | A CPS-transformed 'FRaft'.  In a sequence of computations, each
--   computation executes inside the context produced by the previous
--   computation.
--
--   The sequence @m1 >> m2@
--   concatenates @m1@'s raft with @m2@'s raft and propagates @m1@'s type
--   environment to @m2@.
newtype Hoist a =
  Hoist {unHoist :: forall r. (a -> FRaft r) -> FRaft r}

-- | Run a piece of code that performs hoisting.  Any changes to the
--   renaming and type environment remain confined within this computation.
runHoist :: Hoist a -> FRaft a
runHoist h = unHoist h return

instance Functor Hoist where
  fmap f m = Hoist $ \k -> unHoist m (k . f)

instance Applicative Hoist where
  pure = return
  (<*>) = ap

instance Monad Hoist where
  return x = Hoist ($ x)
  m >>= k = Hoist $ \k2 -> unHoist m $ \x -> unHoist (k x) k2

liftHoist :: FRaft a -> Hoist a
liftHoist m = Hoist $ \k -> m >>= k

liftT :: (forall r. a -> (a -> FRaft r) -> FRaft r) -> a -> Hoist a
liftT t x = Hoist $ \k -> t x k

renameH :: Rename.Renameable a => a -> Hoist a
renameH = liftHoist . renameF

-- | Produce a raft to be moved away from this segment of code
float :: Raft -> Hoist ()
float r = liftHoist $ FRaft $ tell r

-- | Add a type binding to the environment.
--   This function is called for newly created bindings.
--   Preexisting bindings are added to the environment by 'withBinder'.
assumeHoistedType v ty = Hoist $ \k -> assume v ty $ k ()

-- | Get the bindings that mention the given variables and apply them to the
--   expression.
anchor :: [Var] -> Hoist ExpM -> FRaft ExpM
anchor vs m = FRaft $ WriterT $ do
  ((x, ty), raft) <- runFRaft $ runHoist (m >>= computeTypeForAnchor)
  let (dependent, independent) = partitionRaft (Set.fromList vs) raft
  return (applyRaft dependent ty x, independent)

anchorAll :: Hoist ExpM -> F ExpM
anchorAll m = do
  ((x, ty), raft) <- runFRaft $ runHoist (m >>= computeTypeForAnchor)
  return $ applyRaft raft ty x

computeTypeForAnchor e = do
  ty <- liftHoist $ inferExpType e
  return (e, ty)

-------------------------------------------------------------------------------
-- Flattening expressions

-- | Given an expression that is used in exactly one place,
--   bind the expression to a new variable and float the binding.
--   The expression should have been renamed.
--   The new variable is returned.
bindNewVariable :: ExpM -> Hoist ExpM
bindNewVariable rhs = do
  ty <- liftHoist $ liftF $ inferExpType rhs
  v <- liftHoist $ liftF $ newAnonymousVar ObjectLevel
  let binder = setPatMDmd (Dmd OnceUnsafe Used) $ patM (v ::: ty)
      inf = expInfo $ fromExpM rhs
  float $ LetR inf binder rhs Here
  assumeHoistedType v ty
  return $ ExpM $ VarE inf v

-- | Flatten an expression and then hoist it into a new let-binding.
--   However, do not hoist trivial expressions.
hoistExp :: ExpM -> Hoist ExpM
hoistExp e = do
  e' <- flattenExp e
  if isTrivialExp e' then return e' else bindNewVariable e'

hoistExps = mapM hoistExp

hoistMaybeExp :: Maybe ExpM -> Hoist (Maybe ExpM)
hoistMaybeExp x = mapM hoistExp x

-- | Flatten an expression and then hoist it into a new let-binding.
--   However, do not hoist trivial expressions or introduction rules.
--   (Introduction rules are @LamE@ and @ConE@ expressions.)
hoistIntroExp :: ExpM -> Hoist ExpM
hoistIntroExp exp@(ExpM expression) =
  case expression
  of LamE {} -> flattenExp exp
     ConE {} -> flattenExp exp
     _       -> hoistExp exp

-- | Flatten an expression and then hoist it into a new let-binding.
--   However, do not hoist trivial expressions, introduction rules,
--   or case expressions.
--
--   This kind of flattening is performed on the
--   scrutinee of a case expression.
hoistScrutineeExp :: ExpM -> Hoist ExpM
hoistScrutineeExp exp@(ExpM expression) =
  case expression
  of CaseE {} -> flattenExp exp
     _        -> hoistIntroExp exp

-- | Extract a raft from an expression.  Recursively flatten under
--   subexpressions.
--
--   If @flattenExp rn e@ evaluates to @(r, e')@,
--   then @anchor r e'@ is equivalent to @rename rn e@.
flattenExp :: ExpM -> Hoist ExpM
flattenExp exp@(ExpM expression) =
  case expression
  of VarE inf v ->
       ExpM <$> (VarE inf <$> renameH v)
     LitE inf l ->
       pure $ ExpM $ LitE inf l
     ConE inf con_inst sps tob args ->
       ExpM <$> (ConE inf <$> renameH con_inst
                          <*> hoistExps sps
                          <*> hoistMaybeExp tob
                          <*> hoistExps args)

     AppE inf op ty_args args ->
       ExpM <$> (AppE inf <$> hoistIntroExp op
                          <*> renameH ty_args
                          <*> hoistExps args)

     LamE inf f -> do
       -- Do not hoist code out of the function
       f' <- liftHoist $ liftF $ visitFun f
       return (ExpM $ LamE inf f')

     LetE inf b rhs body -> do
       -- Flatten the right-hand side
       rhs' <- flattenExp rhs
       b' <- liftT withPatM b
       -- Turn the let-binding into a raft
       float $ LetR inf b' rhs' Here
       flattenExp body

     LetfunE inf group body -> do
       group' <- liftT flattenLocalGroup group
       -- Turn the letfun-binding into a raft
       float $ LetfunR inf group' Here
       flattenExp body

     CaseE inf scr sps alts -> flattenCaseExp exp inf scr sps alts

     ExceptE inf ty ->
       ExpM <$> (ExceptE inf <$> renameH ty)

     CoerceE inf t1 t2 e ->
       ExpM <$> (CoerceE inf <$> renameH t1
                             <*> renameH t2
                             <*> flattenExp e)

     ArrayE inf ty es ->
       ExpM <$> (ArrayE inf <$> renameH ty
                            <*> mapM flattenExp es)

flattenCaseExp :: ExpM -> ExpInfo -> ExpM -> [ExpM] -> [AltM] -> Hoist ExpM
flattenCaseExp case_exp inf scr sps alts = do
  -- Host size parameters first so that they'll be in scope over the
  -- scrutinee.  The scrutinee may remain un-hoisted.
  sps' <- hoistExps sps
  scr' <- hoistScrutineeExp scr

  case extractSingleCaseAlternative alts of
    Just (returning_alt, excepting_alts) -> do
       -- Turn this single-alternative case expression into a raft
       excepting_alts' <- renameH excepting_alts
       let exc_alts = map exceptingAltRaft excepting_alts'

       -- Flatten within the case alternative's body
       let AltM (Alt decon tyob params body) = returning_alt
       decon' <- liftT withDeConInst decon
       tyob' <- liftT withMaybePatM tyob
       params' <- liftT withPatMs params
       let normal_alt = RaftAlt decon' tyob' params' Here
       float $ Case1R inf scr' sps' normal_alt exc_alts
       flattenExp body

    Nothing -> do
      -- Cannot flatten this case expression
      alts' <- liftHoist $ liftF $ visitAlts alts
      return $ ExpM $ CaseE inf scr' sps' alts'

-- NB: Global variables are never renamed by 'flattenGroup'.
-- Due to how global type environments are handled, global variables
-- are in scope at their own definitions.  However, renaming removes
-- label tags, causing linking problems.

flattenGroup :: Rename.Renameable (t Mem) =>
                Bool            -- ^ Whether this is a global binding
             -> (t Mem -> Type) -- ^ Get type of an entity
             -> (DefAnn -> t Mem -> FRaft (t Mem)) -- ^ Flatten an entity
             -> DefGroup (Def t Mem)               -- ^ The definition group
             -> (DefGroup (Def t Mem) -> FRaft a)  -- ^ Flatten body
             -> FRaft a
flattenGroup is_global get_type flatten_entity (NonRec def) f = do
  -- Flatten in the function body
  new_definiens <- flatten_entity (defAnnotation def) $ definiens def
  new_ann <- renameF $ defAnnotation def

  -- After renaming the binder, continue with the body
  let flatten_body (new_name ::: new_type) =
        let def' = Def new_name new_ann new_definiens
        in f (NonRec def')

  -- Give the function a new name if appropriate
  let fun_binder = (definiendum def ::: get_type (definiens def))
  if is_global
    then assumeBinder fun_binder $ flatten_body fun_binder
    else withBinder fun_binder flatten_body

flattenGroup is_global get_type flatten_entity (Rec defs) f = do
  -- After renaming, continue with the local functions and body
  let flatten_body new_binders = do
        -- Rename definitions
        new_anns <- mapM (renameF . defAnnotation) defs
        new_definientia <-
          mapM (\d -> flatten_entity (defAnnotation d) (definiens d)) defs
        let defs' = zipWith3 Def (map binderVar new_binders) new_anns new_definientia
        f (Rec defs')

  -- Rename variables that shadow existing names
  let binders = [definiendum d ::: get_type (definiens d) | d <- defs]
  if is_global
    then assumeBinders binders $ flatten_body binders
    else withBinders binders flatten_body

flattenLocalGroup :: DefGroup (FDef Mem)
                  -> (DefGroup (FDef Mem) -> FRaft a)
                  -> FRaft a
flattenLocalGroup = flattenGroup False functionType flatten_function
  where
    flatten_function ann f = liftF $ visitFun f

flattenGlobalGroup :: DefGroup (Def Ent Mem)
                   -> (DefGroup (Def Ent Mem) -> FRaft a)
                   -> FRaft a

flattenGlobalGroup = flattenGroup True entityType flatten_ent
  where
  flatten_ent ann e = liftF $ visitEnt e

-- | Perform flattening in an expression, but do not hoist any terms out
--   of the expression.
visitExp :: ExpM -> F ExpM
visitExp exp = anchorAll $ flattenExp exp

visitAlts :: [AltM] -> F [AltM]
visitAlts xs = mapM visitAlt xs

-- | Perform flattening in a case alternative.  Cannot float code out of the
--   case alternative.
visitAlt :: AltM -> F AltM
visitAlt (AltM (Alt decon tyob params body)) =
  withDeConInst decon $ \decon' ->
  withMaybePatM tyob $ \tyob' ->  
  withPatMs params $ \params' -> do
    body' <- visitExp body
    return $ AltM $ Alt decon' tyob' params' body'

-- | Perform flattening in a function body, but do not migrate any code out
--   of the function.
visitFun :: FunM -> F FunM
visitFun (FunM (Fun inf ty_params params ret body)) =
  withTyParams ty_params $ \ty_params' ->
  withPatMs params $ \params' -> do
    ret' <- renameF ret
    body' <- visitExp body
    return $ FunM $ Fun inf ty_params' params' ret' body'

visitEnt :: Ent Mem -> F (Ent Mem)
visitEnt (FunEnt f) = FunEnt `liftM` visitFun f
visitEnt (DataEnt c) = DataEnt `liftM` visitConstant c

visitConstant (Constant inf ty e) =
  Constant inf <$> renameF ty <*> visitExp e

visitExport (Export pos spec f) =
  Export pos spec <$> visitFun f

-------------------------------------------------------------------------------

-- | Extract the non-diverging case alternative, if there's exactly one.
--   An alternative is recognized as diverging if it diverges immediately.
extractSingleCaseAlternative :: [AltM] -> Maybe (AltM, [AltM])
extractSingleCaseAlternative alts =
  case partition is_diverging alts
  of (xs, [x]) -> Just (x, xs)
     _         -> Nothing
  where
    is_diverging (AltM (Alt {altBody = b})) =
      case b
      of ExpM (ExceptE {}) -> True
         _                 -> False

{-
-- | Perform flattening in a function body, extracting code if possible.
--   It is only safe to extract code from functions that are
--   _definitely_ called.
flattenFun :: Renaming -> FunM -> F (FunM, Raft)
flattenFun rn (FunM (Fun inf ty_params params ret body)) =
  runFRaft flatten_fun
  where
    flatten_fun = 
      withTyParams rn ty_params $ \rn1 ty_params' ->
      withPatMs rn1 params $ \rn2 params' -> do
        let local_vars = map tyPatVar ty_params' ++ map patMVar params'
        let ret' = rename rn2 ret
        body' <- anchor rn2 local_vars $ flattenExp body
        return $ FunM $ Fun inf ty_params' params' ret' body'
-}

flattenGlobals = withMany flattenGlobalGroup

flattenModule :: Module Mem -> IO (Module Mem)
flattenModule (Module name imports defs exports) = do
  withTheNewVarIdentSupply $ \id_supply -> do
    i_tenv <- readInitGlobalVarIO the_memTypes
    tenv <- thawTypeEnv i_tenv
    runTypeEvalM (runF flatten) id_supply tenv
  where
    flatten = do
      (_, (defs', exports')) <-
        -- Add imports to the type environment; don't transform them
        assumeGDefGroup (Rec imports) (return ()) $

        -- Cannot float bindings to the top level
        noFloat $

        -- Flatten all global bindings and exported bindings
        flattenGlobals defs $ \defs' -> do
          exports' <- liftF $ mapM visitExport exports
          return (defs', exports')
      return $ Module name imports defs' exports'
