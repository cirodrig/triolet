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
to avoid accidentally introducing variable name shadowing.  Shadowing is
permitted in some circumstances (see the example at the end).

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

Flattening can introduce name shadowing. 
Shadowing is introduced when one binding is moved past a nested scope
containing the same binding.
Suppose we start with two non-nested occurrences of variable @x@:

> letrec f y =
>   letrec g x = x + y in
>   let x = 1 in
>   g x in
> f 2

After flattening, we may end up with the following.

> let x = 1 in
> letrec f y =
>   letrec g x = x + y in
>   g x in
> f 2

The binding @let x = 1$ has been moved above the binding @letrec g x = ...@.
Nevertheless, every use of @x@ still refers to the same variable it referred
to originally.
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
import Builtins.Builtins
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
--   A trivial expression is a variable, literal, or the data values
--   @True@ or @False@.
isTrivialExp :: ExpM -> Bool
isTrivialExp (ExpM e) = 
  case e
  of VarE {} -> True
     LitE {} -> True
     ConE _ (VarCon v [] []) [] Nothing []
       | v `isCoreBuiltin` The_True || v `isCoreBuiltin` The_False -> True
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

-- | Give a new name to a variable
freshen :: Renaming -> Var -> UnboxedTypeEvalM (Renaming, Var)
freshen rn v = do v' <- newClonedVar v
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
withBinder :: FlattenMonad m => Bool -> Binder -> (Binder -> m a) -> m a
withBinder always_freshen (v ::: t) f = do
  rn <- getRenaming
  (rn', v') <- liftTypeEvalM $ if always_freshen
                               then freshen rn v
                               else freshenIfInEnvironment rn v
  let b' = v' ::: rename rn t
  setRenaming rn' $ assumeBinder b' $ f b'

withBinders always_freshen = withMany (withBinder always_freshen)

withDeConInst :: FlattenMonad m => DeConInst -> (DeConInst -> m a) -> m a
withDeConInst dc f =
  case dc
  of VarDeCon op ty_args ex_types -> do
       ty_args' <- renameF ty_args
       withBinders False ex_types $ \ex_types' ->
          f (VarDeCon op ty_args' ex_types')
     TupleDeCon ty_args -> do
       ty_args' <- renameF ty_args
       f (TupleDeCon ty_args')

withTyParam_ext always_rename (TyPat b) m =
  withBinder always_rename b (m . TyPat)

withTyParam :: FlattenMonad m => TyPat -> (TyPat -> m a) -> m a
withTyParam = withTyParam_ext False

-- | Like 'withTyParam', but always rename the variable
withFreshTyParam :: FlattenMonad m => TyPat -> (TyPat -> m a) -> m a
withFreshTyParam = withTyParam_ext True

withTyParams :: FlattenMonad m => [TyPat] -> ([TyPat] -> m a) -> m a
withTyParams = withMany withTyParam

-- | Like 'withTyParams', but always rename the variable
withFreshTyParams :: FlattenMonad m => [TyPat] -> ([TyPat] -> m a) -> m a
withFreshTyParams = withMany withFreshTyParam

withPatM_ext always_rename (PatM b u) m =
  withBinder always_rename b $ \b' -> m (PatM b' u)

withPatM :: FlattenMonad m => PatM -> (PatM -> m a) -> m a
withPatM = withPatM_ext False

withMaybePatM Nothing  f = f Nothing
withMaybePatM (Just p) f = withPatM p (f . Just)

withPatMs :: FlattenMonad m => [PatM] -> ([PatM] -> m a) -> m a
withPatMs = withMany withPatM

-- | Like 'withPatM', but always rename the variable
withFreshPatM = withPatM_ext True

withFreshPatMs = withMany withFreshPatM

-------------------------------------------------------------------------------
-- Generating and moving code rafts

-- | A flattening computation that extracts some code into a raft.
--   The result of flattening is normally a simplified piece of code 
--   that goes inside the raft.
--
--   This monad is mostly used as a component of the 'Hoist' monad, which
--   ensures that variables from the current raft are in the current
--   type environment.
--   The function 'anchorAll' runs an 'FRaft' computation
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

getRaft :: FRaft a -> FRaft (a, Raft)
getRaft (FRaft m) = FRaft (listen m)

liftF :: F a -> FRaft a
liftF m = FRaft $ lift m

{-
-- | Prohibit floating here.  It's a run-time error if any code is moved past
--   this point.
noFloat :: FRaft a -> F a
noFloat (FRaft m) = do
  (x, w) <- runWriterT m
  case w of Here -> return x
            _ -> internalError "noFloat"
-}

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

anchorAll :: Hoist ExpM -> F ExpM
anchorAll m = do
  ((x, ty), raft) <- runFRaft $ runHoist (m >>= computeTypeForAnchor)
  return $ applyRaft raft ty x

computeTypeForAnchor e = do
  ty <- liftHoist $ inferExpType e
  return (e, ty)

-- | Do not hoist bindings past this point if they mention any
--   variables in 'vs'
anchor :: [Var] -> Hoist ExpM -> Hoist ExpM
anchor vs m = Hoist $ \k -> do
  -- Run 'm' and anchor variables.  Get the raft that is left after anchoring.
  (e, raft) <- getRaft $ anchorRaft vs m

  -- Add the raft to the type environment
  assumeRaft raft $ k e

-- | Get the bindings that mention the given variables and apply them to the
--   expression.  This is a helper function for 'anchor'.
anchorRaft :: [Var] -> Hoist ExpM -> FRaft ExpM
anchorRaft vs m = FRaft $ WriterT $ do
  ((x, ty), raft) <- runFRaft $ runHoist (m >>= computeTypeForAnchor)
  let (dependent, independent) = partitionRaft (Set.fromList vs) raft
  return (applyRaft dependent ty x, independent)

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
  let binder = patM (v ::: ty)
      inf = expInfo $ fromExpM rhs
  floatLetBinding inf binder rhs
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
       floatLetBinding inf b' rhs'
       flattenExp body

     LetfunE inf group body -> do
       group' <- flattenLocalGroup group
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

-- | Float a let-binding.  If the right-hand side is a lambda term, convert
--   it to a nonrecursive letfun binding.
floatLetBinding inf pat rhs =
  case rhs
  of ExpM (LamE _ f) ->
       let fun_def = modifyDefAnnotation (\a -> a {defAnnUses = patMDmd pat}) $
                     mkDef (patMVar pat) f
           group = NonRec fun_def
       in float $ LetfunR inf group Here
     _ -> float $ LetR inf pat rhs Here

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

-- | Flatten a definition group in the 'Hoist' monad.
--   Bindings from functions in the group, as well as from the body,
flattenGroup_Hoist :: Rename.Renameable (t Mem) =>
                    (t Mem -> Type) -- ^ Get type of an entity
             -> ([Var] -> DefAnn -> t Mem -> Hoist (t Mem)) -- ^ Flatten an entity
             -> DefGroup (Def t Mem)               -- ^ The definition group
             -> Hoist (DefGroup (Def t Mem))
flattenGroup_Hoist get_type flatten_entity (NonRec def) = do
  -- Flatten in the function body
  new_definiens <- flatten_entity [] (defAnnotation def) $ definiens def
  new_ann <- liftHoist $ renameF $ defAnnotation def

  -- Give the function a new name if appropriate
  let fun_binder = (definiendum def ::: get_type (definiens def))

  -- After renaming the binder, continue with the body
  new_binder@(new_name ::: new_type) <- liftT (withBinder False) fun_binder
  let def' = Def new_name new_ann new_definiens
  return (NonRec def')

flattenGroup_Hoist get_type flatten_entity (Rec defs) = do
  -- Rename variables that shadow existing names
  let binders = [definiendum d ::: get_type (definiens d) | d <- defs]
  new_binders <- liftT (withBinders False) binders
  let def_vars = map binderVar new_binders

  -- Rename local definitions
  new_anns <- liftHoist $ mapM (renameF . defAnnotation) defs
  new_definientia <-
    mapM (\d -> flatten_entity def_vars (defAnnotation d) (definiens d)) defs

  -- Continue with the body
  let defs' = zipWith3 Def def_vars new_anns new_definientia
  return (Rec defs')

flattenLocalGroup :: DefGroup (FDef Mem)
                  -> Hoist (DefGroup (FDef Mem))
flattenLocalGroup = flattenGroup_Hoist functionType flatten_function
  where
    flatten_function bound_vs ann f =
      -- If function is definitely called, then allow code to be hoisted out
      -- of the function.
      if defAnnCalled ann
      then flattenFun bound_vs f
      else liftHoist $ liftF $ visitFun f

-- NB: Global variables are never renamed by 'flattenGroup'.
-- Due to how global type environments are handled, global variables
-- are in scope at their own definitions.  However, renaming removes
-- label tags, causing linking problems.

flattenGroup :: Rename.Renameable (t Mem) =>
                Bool            -- ^ Whether this is a global binding
             -> (t Mem -> Type) -- ^ Get type of an entity
             -> (DefAnn -> t Mem -> F (t Mem)) -- ^ Flatten an entity
             -> DefGroup (Def t Mem)               -- ^ The definition group
             -> (DefGroup (Def t Mem) -> F a)  -- ^ Flatten body
             -> F a
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
    else withBinder False fun_binder flatten_body

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
    else withBinders False binders flatten_body

flattenGlobalGroup :: DefGroup (Def Ent Mem)
                   -> (DefGroup (Def Ent Mem) -> F a)
                   -> F a
flattenGlobalGroup = flattenGroup True entityType flatten_ent
  where
    flatten_ent ann e = visitEnt e

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

-- | Perform flattening in a function body, extracting code if possible.
--   It is only safe to extract code from functions that are
--   _definitely_ called.
--
--   This function may be part of a recursive binding, in which case
--   any code using the recursive variables must remain inside the function.  
--   Recursive bound variables (if any) are passed in as parameters.
flattenFun :: [Var] -> FunM -> Hoist FunM
flattenFun bound_vs (FunM (Fun inf ty_params params ret body)) = do
  -- Always rename the function parameters to avoid name shadowing.
  -- The function parameter bindings may be moved under other bindings.
  ty_params' <- liftT withFreshTyParams ty_params
  params' <- liftT withFreshPatMs params

  let local_vars = bound_vs ++ map tyPatVar ty_params' ++ map patMVar params'
  ret' <- liftHoist $ renameF ret
  body' <- anchor local_vars $ flattenExp body
  return $ FunM $ Fun inf ty_params' params' ret' body'

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

        -- Flatten all global bindings and exported bindings
        flattenGlobals defs $ \defs' -> do
          exports' <- mapM visitExport exports
          return (defs', exports')
      return $ Module name imports defs' exports'
