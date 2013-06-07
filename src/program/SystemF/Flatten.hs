{-| Expression flattening turns nested expressions into non-nested ones,
    increasing opportunities for subsequent optimizations.

Rafts are extracted from:

1. Arguments of data constructors
2. Arguments of functions
3. Right-hand-sides of let expressions
4. Bodies of letfun-bound initializer functions
5. Arguments of case expressions

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

-- | If true, do additional error checking
sanityCheck = True

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

{-
-- | Add a variable to the environment, renaming if necessary.
--   If the flag is true, then unconditionally rename the variable because
--   the variable binding may be hoisted to a new location.
withBoundVariable :: Bool -> Renaming -> Var -> (Renaming -> Var -> F a) -> F a
withBoundVariable rename_always rn v k
  | rename_always                = rename
  | Just _ <- Rename.lookup v rn = rename -- Rename to avoid shadowing
  | otherwise                    = k rn v -- Don't rename
  where
    rename = do
      v' <- newClonedVar v
      let rn' = Rename.extend v v' rn
      k rn' v'
-}

-- | Rename the binder.
--   Give the bound variable a new name if the current name is in scope. 
freshenIfInEnvironment :: EvalMonad m =>
                          Renaming -> Var -> m (Renaming, Var)
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

freshenIfInEnvironmentList :: EvalMonad m =>
                              Renaming -> [Var] -> m (Renaming, [Var])
freshenIfInEnvironmentList rn (v:vs) = do
  (rn', v') <- freshenIfInEnvironment rn v
  (rn'', vs') <- freshenIfInEnvironmentList rn' vs
  return (rn'', v':vs')

freshenIfInEnvironmentList rn [] = return (rn, [])

-- | Rename a binder and add the bound variable to the environment.
withBinder :: EvalMonad m =>
              Renaming -> Binder -> (Renaming -> Binder -> m a) -> m a
withBinder rn (v ::: t) f = do
  (rn', v') <- freshenIfInEnvironment rn v
  let b' = v' ::: rename rn t
  assumeBinder b' $ f rn' b'

withBinders rn (b:bs) f =
  withBinder rn b $ \rn' b' -> withBinders rn' bs $ \rn'' bs' -> f rn'' (b':bs')

withBinders rn [] f = f rn []

-- | Rename a deconstructor and add bound variables to the environment.
withDeConInst :: EvalMonad m =>
                 Renaming -> DeConInst -> (Renaming -> DeConInst -> m a) -> m a
withDeConInst rn dc f =
  case dc
  of VarDeCon op ty_args ex_types ->
       let ty_args' = rename rn ty_args
       in withBinders rn ex_types $ \rn' ex_types' ->
          f rn' (VarDeCon op ty_args' ex_types')
     TupleDeCon ty_args ->
       let ty_args' = rename rn ty_args
       in f rn (TupleDeCon ty_args')

withTyParam :: EvalMonad m =>
               Renaming -> TyPat -> (Renaming -> TyPat -> m a) -> m a
withTyParam rn (TyPat b) m = withBinder rn b $ \rn' b' -> m rn' (TyPat b')

withTyParams :: EvalMonad m =>
                Renaming -> [TyPat] -> (Renaming -> [TyPat] -> m a) -> m a
withTyParams rn (p:ps) m =
  withTyParam rn p $ \rn' p' -> withTyParams rn' ps $ \rn'' ps' -> m rn'' (p':ps')

withTyParams rn [] m = m rn []

-- | Rename a pattern binding and add it to the type environment
withPatM :: EvalMonad m =>
            Renaming -> PatM -> (Renaming -> PatM -> m a) -> m a
withPatM rn (PatM b u) m = withBinder rn b $ \rn' b' -> m rn' (PatM b' u)

withMaybePatM rn Nothing k = k rn Nothing
withMaybePatM rn (Just p) k = withPatM rn p $ \rn' p' -> k rn' (Just p')

withPatMs :: EvalMonad m =>
             Renaming -> [PatM] -> (Renaming -> [PatM] -> m a) -> m a
withPatMs rn (p:ps) f =
  withPatM rn p $ \rn' p' -> withPatMs rn' ps $ \rn'' ps' -> f rn'' (p':ps')

withPatMs rn [] f = f rn []

-------------------------------------------------------------------------------

-- | Flattening involves type inference in order to create new
--   temporary variables
type F = UnboxedTypeEvalM

-- | A raft-constructing expression
newtype FRaft a = FRaft (WriterT Raft F a)
              deriving(Functor, Applicative, Monad, MonadIO)

runFRaft (FRaft m) = runWriterT m

instance Supplies FRaft (Ident Var) where
  fresh = FRaft $ lift fresh

instance TypeEnvMonad FRaft where
  type EvalBoxingMode FRaft = UnboxedMode
  getTypeEnv = FRaft $ lift getTypeEnv
  liftTypeEnvM m = FRaft $ lift $ liftTypeEnvM m

instance EvalMonad FRaft where
  liftTypeEvalM m = FRaft $ lift $ liftTypeEvalM m

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
  Hoist {runHoist :: Renaming -> forall r. (a -> Renaming -> FRaft r) -> FRaft r}

instance Functor Hoist where
  fmap f m = Hoist $ \rn k -> runHoist m rn $ \x rn' -> k (f x) rn'

instance Applicative Hoist where
  pure = return
  (<*>) = ap

instance Monad Hoist where
  return x = Hoist $ \rn k -> k x rn
  m >>= k = Hoist $ \rn k2 -> runHoist m rn $ \x rn' -> runHoist (k x) rn' k2

liftHoistWithRenaming :: (Renaming -> FRaft a) -> Hoist a
liftHoistWithRenaming f = Hoist $ \rn k -> f rn >>= \x -> k x rn

liftHoist :: FRaft a -> Hoist a
liftHoist m = Hoist $ \rn k -> m >>= \x -> k x rn

liftT :: (forall r. Renaming -> a -> (Renaming -> a -> FRaft r) -> FRaft r)
      -> a -> Hoist a
liftT t x = Hoist $ \rn k -> t rn x (\rn' x' -> k x' rn')

-- | Apply the current renaming to a term
renameBeforeHoisting :: Rename.Renameable a => a -> Hoist a
renameBeforeHoisting x = Hoist $ \rn k -> k (rename rn x) rn

-- | Produce a raft to be moved away from this segment of code
float_new :: Raft -> Hoist ()
float_new r = liftHoist $ FRaft $ tell r

-- TODO: integrate assumeHoistedType with float_new
assumeHoistedType v ty = Hoist $ \rn k -> assume v ty $ k () rn

assumeHoistedBinder b = Hoist $ \rn k -> assumeBinder b $ k () rn

-- | Get the bindings that mention the given variables and apply them to the
--   expression.
anchor_new :: Renaming -> [Var] -> Hoist ExpM -> FRaft ExpM
anchor_new rn vs m = FRaft $ WriterT $ do
  ((x, ty), raft) <- runFRaft $ runHoist m rn computeTypeForAnchor
  let (dependent, independent) = partitionRaft (Set.fromList vs) raft
  return (applyRaft dependent ty x, independent)

anchorAll_new :: Renaming -> Hoist ExpM -> F ExpM
anchorAll_new rn m = do
  ((x, ty), w) <- runFRaft $ runHoist m rn computeTypeForAnchor
  return $ applyRaft w ty x

computeTypeForAnchor e _ = do
  ty <- inferExpType e
  return (e, ty)

-- | Given an expression that is used in exactly one place,
--   bind the expression to a new variable and float the binding.
--   The expression should have been renamed.
--   The new variable is returned.
bindNewVariable_new :: ExpM -> Hoist ExpM
bindNewVariable_new rhs = do
  ty <- liftHoist $ liftF $ inferExpType rhs
  v <- liftHoist $ liftF $ newAnonymousVar ObjectLevel
  let binder = setPatMDmd (Dmd OnceUnsafe Used) $ patM (v ::: ty)
      inf = expInfo $ fromExpM rhs
  float_new $ LetR inf binder rhs Here
  assumeHoistedType v ty
  return $ ExpM $ VarE inf v

-- | Flatten an expression and then hoist it into a new let-binding.
--   However, do not hoist trivial expressions.
hoistExp_new :: ExpM -> Hoist ExpM
hoistExp_new e = do
  e' <- flattenExp_new e 
  if isTrivialExp e' then return e' else bindNewVariable_new e'

hoistExps_new = mapM hoistExp_new

hoistMaybeExp_new :: Maybe ExpM -> Hoist (Maybe ExpM)
hoistMaybeExp_new x = mapM hoistExp_new x

-- | Flatten an expression and then hoist it into a new let-binding.
--   However, do not hoist trivial expressions or introduction rules.
--   (Introduction rules are @LamE@ and @ConE@ expressions.)
hoistIntroExp_new :: ExpM -> Hoist ExpM
hoistIntroExp_new exp@(ExpM expression) =
  case expression
  of LamE {} -> flattenExp_new exp
     ConE {} -> flattenExp_new exp
     _       -> hoistExp_new exp

-- | Flatten an expression and then hoist it into a new let-binding.
--   However, do not hoist trivial expressions, introduction rules,
--   or case expressions.
--
--   This kind of flattening is performed on the
--   scrutinee of a case expression.
hoistScrutineeExp_new :: ExpM -> Hoist ExpM
hoistScrutineeExp_new exp@(ExpM expression) =
  case expression
  of CaseE {} -> flattenExp_new exp
     _        -> hoistIntroExp_new exp

-- | Extract a raft from an expression.  Recursively flatten under
--   subexpressions.
--
--   If @flattenExp rn e@ evaluates to @(r, e')@,
--   then @anchor r e'@ is equivalent to @rename rn e@.
flattenExp_new :: ExpM -> Hoist ExpM
flattenExp_new exp@(ExpM expression) =
  case expression
  of VarE inf v ->
       ExpM <$> (VarE inf <$> renameBeforeHoisting v)
     LitE inf l ->
       pure $ ExpM $ LitE inf l
     ConE inf con_inst sps tob args ->
       ExpM <$> (ConE inf <$> renameBeforeHoisting con_inst
                          <*> hoistExps_new sps
                          <*> hoistMaybeExp_new tob
                          <*> hoistExps_new args)

     AppE inf op ty_args args ->
       ExpM <$> (AppE inf <$> hoistIntroExp_new op
                          <*> renameBeforeHoisting ty_args
                          <*> hoistExps_new args)

     LamE inf f -> do
       -- Do not hoist code out of the function
       f' <- liftHoistWithRenaming $ \rn -> liftF $ visitFun rn f
       return (ExpM $ LamE inf f')

     LetE inf b rhs body -> do
       -- Flatten the right-hand side
       rhs' <- flattenExp_new rhs
       b' <- liftT withPatM b
       -- Turn the let-binding into a raft
       float_new $ LetR inf b' rhs' Here
       flattenExp_new body

     LetfunE inf group body -> do
       group' <- liftT flattenLocalGroup group
       -- Turn the letfun-binding into a raft
       float_new $ LetfunR inf group' Here
       flattenExp_new body

     CaseE inf scr sps alts -> flattenCaseExp_new exp inf scr sps alts

     ExceptE inf ty ->
       ExpM <$> (ExceptE inf <$> renameBeforeHoisting ty)

     CoerceE inf t1 t2 e ->
       ExpM <$> (CoerceE inf <$> renameBeforeHoisting t1
                             <*> renameBeforeHoisting t2
                             <*> flattenExp_new e)

     ArrayE inf ty es ->
       ExpM <$> (ArrayE inf <$> renameBeforeHoisting ty
                            <*> mapM flattenExp_new es)

flattenCaseExp_new :: ExpM -> ExpInfo -> ExpM -> [ExpM] -> [AltM] -> Hoist ExpM
flattenCaseExp_new case_exp inf scr sps alts = do
  -- Host size parameters first so that they'll be in scope over the
  -- scrutinee.  The scrutinee may remain un-hoisted.
  sps' <- hoistExps_new sps
  scr' <- hoistScrutineeExp_new scr

  case extractSingleCaseAlternative alts of
    Just (returning_alt, excepting_alts) -> do
       -- Turn this single-alternative case expression into a raft
       excepting_alts' <- renameBeforeHoisting excepting_alts
       let exc_alts = map exceptingAltRaft excepting_alts'

       -- Flatten within the case alternative's body
       let AltM (Alt decon tyob params body) = returning_alt
       decon' <- liftT withDeConInst decon
       tyob' <- liftT withMaybePatM tyob
       params' <- liftT withPatMs params
       let normal_alt = RaftAlt decon' tyob' params' Here
       float_new $ Case1R inf scr' sps' normal_alt exc_alts
       flattenExp_new body

    Nothing -> do
      -- Cannot flatten this case expression
      alts' <- liftHoistWithRenaming $ \rn -> liftF $ visitAlts rn alts
      return $ ExpM $ CaseE inf scr' sps' alts'

-------------------------------------------------------------------------------
-- Old code

{-
-- | Produce a raft to be moved away from this segment of code
float :: Raft -> FRaft ()
float r = FRaft $ tell r

-- | Get the bindings that mention the given variables and apply them to the
--   expression.
anchor :: [Var] -> (forall a. (Renaming -> ExpM -> FRaft a) -> FRaft a) -> FRaft ExpM
anchor vs f = FRaft $ WriterT $ do
  ((x, ty), raft) <- runWriterT (case f compute_type of FRaft m -> m)
  i_type_env <- freezeTypeEnv
  let (dependent, independent) = partitionRaft (Set.fromList vs) raft
  -- ty <- traceShow (pprTypeEnv i_type_env $$ pprExp (applyRaft dependent intT x)) $ inferExpType x
  return (applyRaft dependent ty x, independent)
  where
    compute_type _ e = do
      ty <- inferExpType e
      return (e, ty)

anchorAll :: (forall a. (Renaming -> ExpM -> FRaft a) -> FRaft a) -> F ExpM
anchorAll f = do
  ((x, ty), w) <- runWriterT (case f compute_type of FRaft m -> m)
  i_type_env <- freezeTypeEnv
  -- ty <- traceShow (pprTypeEnv i_type_env $$ pprExp (applyRaft w intT x)) $ inferExpType x
  return $ applyRaft w ty x
  where
    compute_type _ e = do
      ty <- inferExpType e
      return (e, ty)

-- | Given an expression that is used in exactly one place,
--   bind the expression to a new variable and float the binding.
--   The expression should have been renamed.
--   The new variable is returned.
bindNewVariable :: ExpM -> (ExpM -> FRaft a) -> FRaft a
bindNewVariable rhs k = do
  ty <- liftF $ inferExpType rhs
  v <- liftF $ newAnonymousVar ObjectLevel
  let binder = setPatMDmd (Dmd OnceUnsafe Used) $ patM (v ::: ty)
      inf = expInfo $ fromExpM rhs
  float $ LetR inf binder rhs Here
  assume v ty $ k (ExpM $ VarE inf v)

hoistExps :: Renaming -> [ExpM] -> (Renaming -> [ExpM] -> FRaft a) -> FRaft a
hoistExps rn (e:es) k =
  hoistExp rn e $ \rn' e' -> hoistExps rn' es $ \rn'' es' -> k rn'' (e':es')

hoistExps rn [] k = k rn []

-- | Flatten an expression and then hoist it into a new let-binding.
--   However, do not hoist trivial expressions.
hoistExp :: Renaming -> ExpM -> (Renaming -> ExpM -> FRaft a) -> FRaft a
hoistExp rn e k = flattenExp rn e $ \rn' e' ->
  if isTrivialExp e' then k rn' e' else bindNewVariable e' (k rn')

hoistMaybeExp :: Renaming -> Maybe ExpM
              -> (Renaming -> Maybe ExpM -> FRaft a)
              -> FRaft a
hoistMaybeExp rn Nothing  k = k rn Nothing
hoistMaybeExp rn (Just e) k = hoistExp rn e (\rn' e' -> k rn' (Just e'))

-- | Flatten an expression and then hoist it into a new let-binding.
--   However, do not hoist trivial expressions or introduction rules.
--   (Introduction rules are @LamE@ and @ConE@ expressions.)
hoistIntroExp :: Renaming -> ExpM -> (Renaming -> ExpM -> FRaft a) -> FRaft a
hoistIntroExp rn exp@(ExpM expression) k =
  case expression
  of LamE {} -> flattenExp rn exp k
     ConE {} -> flattenExp rn exp k
     _       -> hoistExp rn exp k

-- | Flatten an expression and then hoist it into a new let-binding.
--   However, do not hoist trivial expressions, introduction rules,
--   or case expressions.
--
--   This kind of flattening is performed on the
--   scrutinee of a case expression.
hoistScrutineeExp :: Renaming -> ExpM -> (Renaming -> ExpM -> FRaft a) -> FRaft a
hoistScrutineeExp rn exp@(ExpM expression) k =
  case expression
  of CaseE {} -> flattenExp rn exp k
     _        -> hoistIntroExp rn exp k

flattenExps :: Renaming -> [ExpM] -> (Renaming -> [ExpM] -> FRaft a) -> FRaft a
flattenExps rn (e:es) k = 
  flattenExp rn e $ \rn' e' -> flattenExps rn' es $ \rn'' es' -> k rn'' (e':es')

flattenExps rn [] k = k rn []

-- | Extract a raft from an expression.  Recursively flatten under
--   subexpressions.
--
--   If @flattenExp rn e@ evaluates to @(r, e')@,
--   then @anchor r e'@ is equivalent to @rename rn e@.
flattenExp :: Renaming -> ExpM -> (Renaming -> ExpM -> FRaft a) -> FRaft a
flattenExp rn exp@(ExpM expression) k =
  case expression
  of VarE inf v ->
       k rn $ ExpM $ VarE inf (rename rn v)
     LitE inf l ->
       k rn $ ExpM $ LitE inf l
     ConE inf con_inst sps tob args ->
       let con_inst' = rename rn con_inst
       in hoistExps rn sps $ \rn' sps' -> 
          hoistMaybeExp rn' tob $ \rn'' tob' -> 
          hoistExps rn'' args $ \rn''' args' -> 
          k rn''' $ ExpM $ ConE inf con_inst' sps' tob' args'

     AppE inf op ty_args args ->
       let ty_args' = rename rn ty_args
       in hoistIntroExp rn op $ \rn' op' ->
          hoistExps rn' args $ \rn'' args' ->
          k rn'' $ ExpM $ AppE inf op' ty_args' args'

     LamE inf f -> do
       -- Do not hoist code out of the function 
       f' <- liftF $ visitFun rn f
       k rn (ExpM $ LamE inf f')

     LetE inf b rhs body ->
       -- Flatten the right-hand side
       flattenExp rn rhs $ \rn' rhs' ->
       withPatM rn' b $ \rn'' b' -> do
         -- Turn the let-binding into a raft
         float $ LetR inf b' rhs' Here
         flattenExp rn'' body k

     LetfunE inf group body ->
       flattenLocalGroup rn group $ \rn' group' -> do
         -- Turn the letfun-binding into a raft
         float $ LetfunR inf group' Here
         flattenExp rn' body k

     CaseE inf scr sps alts -> flattenCaseExp exp rn inf scr sps alts k

     ExceptE inf ty ->
       k rn (ExpM $ ExceptE inf (rename rn ty))

     CoerceE inf t1 t2 e ->
       flattenExp rn e $ \rn' e' ->
       k rn' (ExpM $ CoerceE inf (rename rn' t1) (rename rn' t2) e')

     ArrayE inf ty es ->
       flattenExps rn es $ \rn' es' ->
       k rn' (ExpM $ ArrayE inf (rename rn' ty) es')

flattenCaseExp :: ExpM -> Renaming -> ExpInfo -> ExpM -> [ExpM] -> [AltM]
               -> (Renaming -> ExpM -> FRaft a) -> FRaft a
flattenCaseExp case_exp rn inf scr sps alts k =
  case extractSingleCaseAlternative alts
  of Just (returning_alt, excepting_alts) -> do
       -- Turn this single-alternative case expression into a raft

       -- Host size parameters first so that they'll be in scope over the
       -- scrutinee.  The scrutinee may remain un-hoisted.
       hoistExps rn sps $ \rn' sps' ->
         hoistScrutineeExp rn' scr $ \rn'' scr' -> do
           let exc_alts = map exceptingAltRaft $ rename rn'' excepting_alts

           -- Flatten within the case alternative's body
           let AltM (Alt decon tyob params body) = returning_alt
           withDeConInst rn'' decon $ \rn1 decon' ->
             withMaybePatM rn1 tyob $ \rn2 tyob' ->
             withPatMs rn2 params $ \rn3 params' -> do
               let normal_alt = RaftAlt decon' tyob' params' Here
               float $ Case1R inf scr' sps' normal_alt exc_alts
               flattenExp rn3 body k

     Nothing ->
       -- Cannot flatten this case expression
       hoistExps rn sps $ \rn' sps' ->
       hoistScrutineeExp rn' scr $ \rn'' scr' -> do
         alts' <- liftF $ visitAlts rn'' alts
         k rn'' $ ExpM $ CaseE inf scr' sps' alts'
-}

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
flattenFun :: Renaming -> FunM -> F (FunM, Raft)
flattenFun rn (FunM (Fun inf ty_params params ret body)) =
  runFRaft flatten_fun
  where
    flatten_fun = 
      withTyParams rn ty_params $ \rn1 ty_params' ->
      withPatMs rn1 params $ \rn2 params' -> do
        let local_vars = map tyPatVar ty_params' ++ map patMVar params'
        let ret' = rename rn2 ret
        body' <- anchor_new rn2 local_vars $ flattenExp_new body
        return $ FunM $ Fun inf ty_params' params' ret' body'

-- | Perform flattening in an expression, but do not hoist any terms out
--   of the expression.
visitExp :: Renaming -> ExpM -> F ExpM
visitExp rn exp = anchorAll_new rn $ flattenExp_new exp

visitAlts :: Renaming -> [AltM] -> F [AltM]
visitAlts rn xs = mapM (visitAlt rn) xs

visitAlt :: Renaming -> AltM -> F AltM
visitAlt rn (AltM (Alt decon tyob params body)) =
  withDeConInst rn decon $ \rn1 decon' ->
  withMaybePatM rn1 tyob $ \rn2 tyob' ->  
  withPatMs rn2 params $ \rn3 params' -> do
    body' <- visitExp rn3 body
    return $ AltM $ Alt decon' tyob' params' body'

-- | Perform flattening in a function body, but do not migrate any code out
--   of the function.
visitFun :: Renaming -> FunM -> F FunM
visitFun rn (FunM (Fun inf ty_params params ret body)) =
  withTyParams rn ty_params $ \rn1 ty_params' ->
  withPatMs rn1 params $ \rn2 params' -> do
    let ret' = rename rn2 ret
    body' <- visitExp rn2 body
    return $ FunM $ Fun inf ty_params' params' ret' body'

visitEnt :: Renaming -> Ent Mem -> F (Ent Mem)
visitEnt rn (FunEnt f) = FunEnt `liftM` visitFun rn f
visitEnt rn (DataEnt c) = DataEnt `liftM` visitConstant rn c

visitConstant rn (Constant inf ty e) = do
  e' <- visitExp rn e
  return $ Constant inf (rename rn ty) e'

-- NB: Global variables are never renamed by 'flattenGroup'.
-- Due to how global type environments are handled, global variables
-- are in scope at their own definitions.  However, renaming removes
-- label tags, causing linking problems.
flattenGroup :: Rename.Renameable (t Mem) =>
                Bool
             -> (t Mem -> Type)
             -> (Renaming -> DefAnn -> t Mem -> FRaft (t Mem))
             -> Renaming -> DefGroup (Def t Mem)
             -> (Renaming -> DefGroup (Def t Mem) -> FRaft a)
             -> FRaft a
flattenGroup is_global get_type rename_entity rn (NonRec def) f = do
  -- Rename in the function body
  let new_ann = rename rn $ defAnnotation def
  new_definiens <- rename_entity rn new_ann $ definiens def
  let fun_type = get_type new_definiens

  -- Give the function a new name if appropriate
  (rn', new_name) <- if is_global
                     then return (rn, definiendum def)
                     else freshenIfInEnvironment rn $ definiendum def
  let def' = Def new_name new_ann new_definiens

  -- Add to environment and process body
  assume new_name fun_type $ f rn' (NonRec def')

flattenGroup is_global get_type rename_entity rn (Rec defs) f = do
  -- Rename variables that shadow existing names
  (rn', new_vars) <- if is_global
                     then return (rn, map definiendum defs)
                     else freshenIfInEnvironmentList rn $ map definiendum defs

  -- Add to environment
  let function_types = map (get_type . rename rn . definiens) defs
  assumeBinders [v ::: t | (v, t) <- zip new_vars function_types] $ do

    -- Rename definitions
    let new_anns = map (rename rn' . defAnnotation) defs
    new_definientia <- zipWithM (\d a -> rename_entity rn' a $ definiens d) defs new_anns
    let defs' = zipWith3 Def new_vars new_anns new_definientia

    -- Process body
    f rn' (Rec defs')

flattenExport rn (Export pos spec f) = do
  f' <- visitFun rn f
  return $ Export pos spec f'

flattenLocalGroup :: Renaming -> DefGroup (FDef Mem)
                  -> (Renaming -> DefGroup (FDef Mem) -> FRaft a)
                  -> FRaft a
flattenLocalGroup = flattenGroup False functionType flatten_function
  where
    flatten_function rn ann f = liftF $ visitFun rn f

flattenGlobalGroup :: Renaming -> DefGroup (Def Ent Mem)
                   -> (Renaming -> DefGroup (Def Ent Mem) -> FRaft a)
                   -> FRaft a

flattenGlobalGroup = flattenGroup True entityType flatten_ent
  where
  flatten_ent rn ann e = liftF $ visitEnt rn e

flattenGlobals rn (g:gs) m =
  flattenGlobalGroup rn g $ \rn1 g' ->
  flattenGlobals rn1 gs $ \rn2 gs' ->
  m rn2 (g':gs')

flattenGlobals rn [] m = m rn []

flattenModule :: Module Mem -> IO (Module Mem)
flattenModule (Module name imports defs exports) = do
  withTheNewVarIdentSupply $ \id_supply -> do
    i_tenv <- readInitGlobalVarIO the_memTypes
    tenv <- thawTypeEnv i_tenv
    runTypeEvalM flatten id_supply tenv
  where
    flatten = do
      (_, (defs', exports')) <-
        assumeGDefGroup (Rec imports) (return ()) $ noFloat $
        flattenGlobals Rename.empty defs $ \rn1 defs' -> do
          exports' <- liftF $ mapM (flattenExport rn1) exports
          return (defs', exports')
      return $ Module name imports defs' exports'

