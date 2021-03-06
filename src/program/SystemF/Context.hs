{-| Expression contexts.

An expression context represents some code that can be put around an
expression to bind variables and guard execution.  This module provides
ways to construct and transform contexts.  In particular, context-handling
functions can merge contexts without risk of name capture, by renaming
variables in contexts as needed.

Contexts don't represent a fully encapsulated variable scope.  Things
outside a context may refer to variables that are bound by the
context.  It is only the contexts themselves that are not allowed to refer  
to one another's variables.
-}

{-# LANGUAGE FlexibleContexts #-}
module SystemF.Context
       (isUnfloatableCase,
        Contexted,

        -- * Creating contexts
        unitContext, letContext, caseContext, letfunContext, exceptingContext,
        asLetContext, asCaseContext,
        
        -- * Eliminating contexts
        discardContext,
        eliminateContext,
        contextExpression,
        pprContext,

        -- * Inspecting contexts
        isUnitContext, isExceptingContext,
        contextFreeVariables,

        -- * Transformations
        mapContext,
        traverseContext, inContext,
        joinTraverseContext, joinInContext,
        joinContext,
        merge,
        mergeWith,
        mergeList,
        nubContext,

        -- * Context splitting
        splitContext,
        anchor, anchorVar, anchorVarList
       )
where

import Control.Monad
import Control.Monad.Trans
import Data.List
import Data.Maybe
import qualified Data.Set as Set
import Text.PrettyPrint.HughesPJ

import Common.Identifier
import Common.Supply
import Common.MonadLogic
import SystemF.Syntax
import SystemF.MemoryIR
import SystemF.Rename
import SystemF.TypecheckMem(functionType)
import SystemF.PrintMemoryIR
import Type.Compare
import Type.Environment
import Type.Eval
import Type.Type
import qualified Type.Rename as Rename
import Type.Rename(Renaming, Renameable(..))
import qualified Type.Substitute as Substitute
import Type.Substitute(substitute, freshen, Substitutable(..))

-- | Do s1 and s2 intersect?
intersects :: Ord a => Set.Set a -> Set.Set a -> Bool
s1 `intersects` s2 = not $ Set.null $ Set.intersection s1 s2

-- | Whether the argument is a case statement that has multiple non-excepting
--   branches.
isUnfloatableCase :: ExpM -> Bool
isUnfloatableCase e@(ExpM (CaseE {})) = isNothing $ asCaseContext True e
isUnfloatableCase _ = False

-- | Return True if the expression ends with an exception-raising statement 
--   and does not return normally.
isExceptingExp :: ExpM -> Bool
isExceptingExp (ExpM exp) =
  case exp
  of LetE _ _ _ body  -> isExceptingExp body
     LetfunE _ _ body -> isExceptingExp body
     CaseE _ scr _ alts -> all isExceptingAlt alts
     ExceptE {}       -> True
     _                -> False

isExceptingAlt :: AltM -> Bool
isExceptingAlt (AltM alt) =
  isExceptingExp $ altBody alt

-- | Remove demand information from a pattern.  Demand information is removed
--   from floated patterns because their uses may be changed by floating.
clearDemand :: PatM -> PatM
clearDemand = setPatMDmd unknownDmd

-- | An expression with a hole in it.  An expression can be put into the hole
--   to build a new expression.
data CtxItem =
    -- | A let expression that binds a variable.
    --
    --   @let <pattern> = <rhs> in (...)@
    LetCtx ExpInfo !PatM ExpM

    -- | A case expression with a single alternative that returns normally.
    --
    --   Other alternatives that raise exceptions are permitted.
    --
    --   The normal alternative's fields are included as part of the context.
    --
    --   @case <scrutinee> [<size-parameters>]
    --    of { <alternative>. (...); <excepting alternatives>}@
  | CaseCtx ExpInfo ExpM [ExpM] !AltBinders [AltBinders]

    -- | A group of function definitions
  | LetfunCtx ExpInfo !(DefGroup (FDef Mem))

-- | The binders from a case alternative
data AltBinders = AltBinders !DeConInst (Maybe PatM) [PatM]

renameAltBinders rn (AltBinders decon ty_ob params) k =
  renameDeConInst rn decon $ \rn' decon' ->
  renameMaybePatM rn' ty_ob $ \rn'' ty_ob' ->
  renamePatMs rn'' params $ \rn''' params' ->
  k rn''' (AltBinders decon' ty_ob' params')

altBindersFreeVariables (AltBinders decon ty_ob params) =
  deConFreeVariables decon $
  freeVariables (map patMDmd params) `Set.union`
  freeVariables (fmap patMDmd ty_ob) `Set.union`
  freeVariables (fmap patMType ty_ob) `Set.union`
  freeVariables (map patMType params)

substituteAltBinders s (AltBinders decon ty_ob params) k =
  substituteDeConInst (typeSubst s) decon $ \ts' decon' ->
  substituteMaybePatM (setTypeSubst ts' s) ty_ob $ \s' ty_ob' ->
  substitutePatMs s' params $ \s'' params' ->
  k s'' (AltBinders decon' ty_ob' params')

ctxItemFreeVariables :: CtxItem -> Set.Set Var
ctxItemFreeVariables (LetCtx _ pat rhs) =
  freeVariables (patMType pat) `Set.union`
  freeVariables (patMDmd pat) `Set.union`
  freeVariables rhs

ctxItemFreeVariables (CaseCtx _ scr sps normal_alt exc_alts) =
  freeVariables scr `Set.union`
  freeVariables sps `Set.union`
  Set.unions (map altBindersFreeVariables (normal_alt : exc_alts))

ctxItemFreeVariables (LetfunCtx _ defs) =
  defGroupFreeVariables defs Set.empty

ctxItemBoundVariables :: CtxItem -> Set.Set Var
ctxItemBoundVariables (LetCtx _ pat rhs) =
  Set.singleton $ patMVar pat

ctxItemBoundVariables (CaseCtx _ _ _ (AltBinders decon ty_ob params) _) =
  let ex_vars = [v | v ::: _ <- deConExTypes decon]
      param_vars = map patMVar $ maybeToList ty_ob ++ params
  in Set.fromList $ ex_vars ++ param_vars

ctxItemBoundVariables (LetfunCtx _ group) =
  Set.fromList $ map definiendum $ defGroupMembers group

renameCtxItem rn ctx k =
  case ctx
  of LetCtx inf pat rhs ->
       let rhs' = rename rn rhs
       in renamePatM rn pat $ \rn' pat' ->
          k rn' (LetCtx inf pat' rhs')
     CaseCtx inf scr sps normal_alt exc_alts ->
       let scr' = rename rn scr
           sps' = rename rn sps
           exc_alts' = [renameAltBinders rn alt (\_ x -> x) | alt <- exc_alts]
       in renameAltBinders rn normal_alt $ \rn' normal_alt' ->  
          k rn' (CaseCtx inf scr' sps' normal_alt' exc_alts')
     LetfunCtx inf defs ->
       renameDefGroup rn defs $ \rn' defs' ->
       k rn' (LetfunCtx inf defs')

substituteCtxItem s ctx k =
  case ctx
  of LetCtx inf pat rhs -> do
       rhs' <- substitute s rhs
       substitutePatM s pat $ \s' pat' ->
         k s' (LetCtx inf pat' rhs')
     CaseCtx inf scr sps normal_alt exc_alts -> do
       scr' <- substitute s scr
       sps' <- substitute s sps
       exc_alts' <- forM exc_alts $ \alt ->
         substituteAltBinders s alt $ \_ alt' -> return alt'
       substituteAltBinders s normal_alt $ \s' normal_alt' -> 
         k s' (CaseCtx inf scr' sps' normal_alt' exc_alts')
     LetfunCtx inf defs ->
       substituteDefGroup substitute s defs $ \s' defs' ->
       k s' (LetfunCtx inf defs')

assumeCtxItem :: TypeEnvMonad m => CtxItem -> m a -> m a
assumeCtxItem (LetCtx _ pat _) m =
  assumePatM pat m

assumeCtxItem (CaseCtx _ _ _ (AltBinders decon ty_ob params) _) m =
  assumeBinders (deConExTypes decon) $
  assumeMaybePatM ty_ob $ assumePatMs params m

assumeCtxItem (LetfunCtx _ defs) m = assume_defs m
  where
    assume_defs m = foldr assume_def m $ defGroupMembers defs
    assume_def def m =
      assume (definiendum def) (functionType $ definiens def) m

-------------------------------------------------------------------------------

type Ctx = [CtxItem]

-- | Compute the set of variables bound by the context
ctxBoundVariables :: Ctx -> Set.Set Var
ctxBoundVariables ctx = Set.unions $ map ctxItemBoundVariables ctx

-- | Compute the set of free variables used by the context
ctxFreeVariables :: Ctx -> Set.Set Var
ctxFreeVariables ctx = fst $ ctxFreeBoundVariables ctx

-- | Compute the set of free and bound variables used by the context
ctxFreeBoundVariables :: Ctx -> (Set.Set Var, Set.Set Var)
ctxFreeBoundVariables ctx = free_variables Set.empty Set.empty ctx
  where
    -- Process the context from head to tail.
    -- Given the set of free and bound variables discovered so far,
    -- use the tail of the context to compute the complete set of free
    -- and bound variables.
    free_variables free bound (item:ctx') =
      let item_free = ctxItemFreeVariables item
          item_bound = ctxItemBoundVariables item

          -- Variables that are free here, and not bound in an
          -- enclosing context, are added to the free set
          free' = free `Set.union` (item_free Set.\\ bound)
          bound' = bound `Set.union` item_bound
      in free_variables free' bound' ctx'

    free_variables free bound [] = (free, bound)

renameCtx :: Renaming -> Ctx -> (Renaming -> Ctx -> a) -> a
renameCtx = renameMany renameCtxItem

substituteCtx :: EvalMonad m =>
                 Subst -> Ctx -> (Subst -> Ctx -> m a) -> m a
substituteCtx = renameMany substituteCtxItem

assumeCtx ctx m = foldr assumeCtxItem m ctx

-- | Build an expression from the context
ctxExpression :: Ctx -> Type -> ExpM -> ExpM
ctxExpression ctx return_type body = go ctx
  where
    raise_exception =
      ExpM $ ExceptE defaultExpInfo return_type

    alt alt_body (AltBinders decon ty_ob params) =
      AltM $ Alt decon ty_ob params alt_body

    go (LetCtx inf pat rhs : ctx') =
      ExpM $ LetE inf pat rhs (go ctx')

    go (CaseCtx inf scr sps normal_alt exc_alts : ctx') =
      let case_alternatives =
            alt (go ctx') normal_alt : map (alt raise_exception) exc_alts
      in ExpM $ CaseE inf scr sps case_alternatives
    
    go (LetfunCtx inf defs : ctx') =
      ExpM $ LetfunE inf defs (go ctx')
    
    go [] = body

-------------------------------------------------------------------------------

-- | A thing inside a context.
--
--   'Contexted' supports a monad-like interface through 'unitContext' and
--   'joinContext'.  It's not declared as a monad because the type of the
--   contents is limited to things that can be substituted and renamed.
--
--   The context may have name shadowing.  In particular, renaming a
--   @Contexted a@ may produce name shadowing.  However, functions embedded
--   in a 'TypeEvalM' will rename to eliminate name shadowing so that shadowing
--   never affects the type environment.
data Contexted a =
    -- | A normal context containing a thing
    ApplyContext
    { _ctxFree :: Set.Set Var
    , _ctxContext :: Ctx
    , _ctxBody :: a
    }
    -- | An exception-raising context.
    --   The body is unreachable because the context is code that raises an
    --   exception before the body has a chance to execute.
  | ExceptingContext

-- | Test whether the context contains no bindings.
isUnitContext :: Contexted a -> Bool
isUnitContext (ApplyContext {_ctxContext = []}) = True
isUnitContext _ = False

-- | Test whether the context raises an exception instead of generating
--   its body
isExceptingContext :: Contexted a -> Bool
isExceptingContext ExceptingContext = True
isExceptingContext _ = False

-- | Get the free variables mentioned in the context.
--   Doesn't include free variables mentioned in the body.
contextFreeVariables :: Contexted a -> Set.Set Var
contextFreeVariables (ApplyContext {_ctxFree = fv}) = fv
contextFreeVariables ExceptingContext = Set.empty

setContextedBody :: b -> Contexted a -> Contexted b
setContextedBody x (ApplyContext f c _) = ApplyContext f c x
setContextedBody _ ExceptingContext = ExceptingContext

unitContext :: a -> Contexted a
unitContext x =
  ApplyContext {_ctxFree = Set.empty, _ctxContext = [], _ctxBody = x}

addContextItem :: CtxItem -> Contexted a -> Contexted a
addContextItem item (ApplyContext { _ctxFree = fv
                                  , _ctxContext = c
                                  , _ctxBody = x}) =
  let fv' = ctxItemFreeVariables item `Set.union`
            (fv Set.\\ ctxItemBoundVariables item)
  in ApplyContext { _ctxFree = fv'
                  , _ctxContext = item : c
                  , _ctxBody = x}

addContextItem _ ExceptingContext = ExceptingContext

-- | Add a @let@ term to the outside of the given context
letContext :: Bool              -- ^ Whether to preserve demand annotations
           -> ExpInfo           -- ^ Source information
           -> PatM              -- ^ Let binder
           -> ExpM              -- ^ Right-hand side
           -> Contexted a 
           -> Contexted a
letContext keep_demands inf pat rhs body =
  let pat' = if keep_demands then pat else clearDemand pat
  in addContextItem (LetCtx inf pat' rhs) body

-- | Add a @case@ term to the outside of the given context
caseContext :: Bool             -- ^ Whether to preserve demand annotations
            -> ExpInfo -> ExpM -> [ExpM] -> DeConInst
            -> Maybe PatM -> [PatM] -> [AltM]
            -> Contexted a -> Contexted a
caseContext keep_demands inf scr sps decon ty_ob params ex_alts body =
  let fix_demands = if keep_demands then id else clearDemand
      ex_binders =
        [AltBinders decon ty_ob (map fix_demands pats)
        | AltM (Alt decon ty_ob pats _) <- ex_alts]
      normal_binder = AltBinders decon ty_ob (map fix_demands params)
  in addContextItem (CaseCtx inf scr sps normal_binder ex_binders) body

-- | Add a @letfun@ term to the outside of the given context
letfunContext :: ExpInfo -> DefGroup (FDef Mem) -> Contexted a -> Contexted a
letfunContext inf defs body =
  addContextItem (LetfunCtx inf defs) body

-- | Create a context that raises an exception
exceptingContext :: Contexted a
exceptingContext = ExceptingContext

-- | Create a new let-binding that binds the result of the given expression to 
--   a new variable.
--
--   The variable binding is annotated with the least precise use
--   information.  One reason we do this is to prevent optimizations from 
--   immediately propagating the variable back to its original position.
--
--   The expression enters the context.  A new variable is created and bound
--   to the original expression's value The original occurrence of
--   the expression is replaced by a new variable.
asLetContext :: EvalMonad m => Type -> ExpM -> m (Contexted ExpM)
asLetContext ty expression = do
  let inf = case expression of ExpM e -> expInfo e
  bound_var <- newAnonymousVar ObjectLevel
  let pat = patM (bound_var ::: ty)
  return $
    letContext True inf pat expression $
    unitContext (ExpM $ VarE inf bound_var)
  
-- | Decompose the expression into a case context and a body expression, if
--   the expression can be decomposed this way.  There must be exactly one
--   case alternative that does not always raise an exception.
asCaseContext :: Bool -> ExpM -> Maybe (Contexted ExpM)
asCaseContext keep_demands (ExpM (CaseE inf scr sps alts)) =
  let (exc_alts, normal_alts) = partition isExceptingAlt alts
      exc_binders = map from_exc_alt exc_alts
  in case normal_alts
     of [AltM (Alt decon ty_ob params body)] -> 
          let ctx = [CaseCtx inf scr sps (AltBinders decon ty_ob (map fix_demands params)) exc_binders]
          in Just $ ApplyContext { _ctxFree = ctxFreeVariables ctx
                                 , _ctxContext = ctx
                                 , _ctxBody = body}
        _ -> Nothing
  where
    fix_demands = if keep_demands then id else clearDemand

    from_exc_alt (AltM (Alt decon ty_ob params _)) =
      AltBinders decon ty_ob (map fix_demands params)

asCaseContext _ _ = Nothing

-- | Combine two contexts.
--   The inner context becomes nested inside the outer one.
joinContext :: Contexted (Contexted a) -> Contexted a
joinContext (ApplyContext {_ctxFree = fv1, _ctxContext = c1, _ctxBody = ctx}) =
  case ctx
  of ApplyContext {_ctxFree = fv2, _ctxContext = c2, _ctxBody = x} ->
       ApplyContext { _ctxFree = fv1 `Set.union`
                                 (fv2 Set.\\ ctxBoundVariables c1)
                    , _ctxContext = c1 ++ c2
                    , _ctxBody = x}
     ExceptingContext -> ExceptingContext

joinContext ExceptingContext = ExceptingContext

discardContext :: Contexted a -> a
discardContext = _ctxBody

-- | Rebuild an expression from a context
contextExpression :: EvalMonad m => Contexted ExpM -> Type -> m ExpM
contextExpression ctx ty = do
  -- Rename to avoid name conflicts with the given type
  ctx' <- freshen ctx
  return $! case ctx'
            of ApplyContext {_ctxContext = c, _ctxBody = e} ->
                 ctxExpression c ty e
               ExceptingContext ->
                 ExpM $ ExceptE defaultExpInfo ty

pprContext :: (a -> Doc) -> Contexted a -> Doc
pprContext show_body (ApplyContext {_ctxContext = c, _ctxBody = b}) =
  let context = map show_context c
  in vcat context $$ show_body b
  where
    show_context (LetCtx _ pat e) =
      text "let" <+> pprPat pat <+> text "=" <+> pprExp e

    show_context (CaseCtx _ scr sps (AltBinders decon ty_ob pats) other_alts) =
      text "let" <+> hang decon_doc 4 (vcat $ map exception other_alts)
      where
        ty_ob_doc = maybe empty (brackets . pprPat) ty_ob
        sps_doc = brackets $ sep $ punctuate comma $ map pprExp sps
        decon_doc =
          hang (sep [pprPatternMatch decon ty_ob pats, sps_doc] <+> text "=") 4
          (pprExp scr)
        exception (AltBinders decon ty_ob pats) =
          text "except if" <+> pprPatternMatch decon ty_ob pats

    show_context (LetfunCtx _ defs) =
      text "letrec" <+> pprFDefGroup defs
  
-- | Split a context into a part that is dependent on a set of variables and
--   a part that is independent.  In the result, the outer part is independent
--   of the set of variables and the inner part is dependent.
splitContext :: (EvalMonad m, Substitutable a, Substitution a ~ Subst) =>
                Set.Set Var -> Contexted a -> m (Contexted (Contexted a))
splitContext dependent_set ctx@(ApplyContext {_ctxFree = fv})
  | Set.null relevant_dependent_vars =
      -- Entire context is independent
      return $ mapContext unitContext ctx

  | otherwise = do
      -- Ensure that there's no name shadowing in the context
      ctx' <- freshen ctx
      
      -- Split into independent and dependent parts
      let (indep, dep) =
            select id id relevant_dependent_vars (_ctxContext ctx')

      -- Build the return value
      let dependent_ctx = ApplyContext { _ctxFree = ctxFreeVariables dep
                                       , _ctxContext = dep
                                       , _ctxBody = _ctxBody ctx'}
          split_ctx = ApplyContext { _ctxFree = ctxFreeVariables indep
                                   , _ctxContext = indep
                                   , _ctxBody = dependent_ctx}
      return split_ctx
  where
    -- The set of dependent variables that are also free in ctx
    relevant_dependent_vars = Set.intersection dependent_set fv

    -- Select the parts of the context that are dependent
    select indep_head dep_head dep_set (c:cs)
      | Set.null $ dep_set `Set.intersection` ctxItemFreeVariables c =
          -- This part of the context is independent
          select (indep_head . (c:)) dep_head dep_set cs

      | otherwise =
          -- This part of the context is dependent
          let dep_set' = dep_set `Set.union` ctxItemBoundVariables c
          in select indep_head (dep_head . (c:)) dep_set' cs

    select indep_head dep_head _ [] = (indep_head [], dep_head [])
      

splitContext _ ExceptingContext = return ExceptingContext

-- | Remove bindings that mention the given set of variables from the context.
--   The bindings are added to the expression inside the context.
anchor :: EvalMonad m =>
          Set.Set Var           -- ^ Variables to anchor onto
       -> TypeEvalM (EvalBoxingMode m) Type -- ^ Computation of the expression's type
       -> Contexted ExpM        -- ^ Input expression and context
       -> m (Contexted ExpM)    -- ^ Computes the new expression with
                                --   bindings anchored
anchor anchor_vars compute_type cexp =
  liftTypeEvalM $ anchor' anchor_vars compute_type cexp

anchor' anchor_vars compute_type cexp
  | anchor_vars `intersects` contextFreeVariables cexp = do
      -- First, simplify the context by removing redundant bindings
      cexp1 <- nubContext cexp

      -- Split the context
      cexp2 <- splitContext anchor_vars cexp

      -- Turn the inner context into an expression
      ty <- compute_type
      traverseContext (flip contextExpression ty) cexp2

  | otherwise = do
      -- None of the context's free variables are anchored, so
      -- no bindings are removed
      return cexp

-- | A variant of 'anchor' that anchors on a single variable
anchorVar :: EvalMonad m =>
          Var
       -> TypeEvalM (EvalBoxingMode m) Type
       -> Contexted ExpM
       -> m (Contexted ExpM)
anchorVar v = anchor (Set.singleton v)

-- | A variant of 'anchor' that anchors on a list of variables
anchorVarList :: EvalMonad m =>
                 [Var]
              -> TypeEvalM (EvalBoxingMode m) Type
              -> Contexted ExpM
              -> m (Contexted ExpM)
anchorVarList vs = anchor (Set.fromList vs)

-- | Apply a function to the body of a 'Contexted' value.
--   This should only be used when there is no risk of variable name shadowing.
--   If name scope matters, use 'traverseContext' instead.
mapContext :: (a -> b) -> Contexted a -> Contexted b
mapContext f ctx@(ApplyContext {_ctxBody = x}) = ctx {_ctxBody = f x}
mapContext _ ExceptingContext = ExceptingContext

instance Renameable a => Renameable (Contexted a) where
  rename rn (ApplyContext { _ctxFree = fv
                          , _ctxContext = context
                          , _ctxBody = body}) = let
    -- Rename the free variables
    fv' = Set.map (\v -> fromMaybe v $ Rename.lookup v rn) fv
    
    -- Rename the context
    in renameCtx rn context $ \rn' context' ->
       -- Rename what's in the hole
       let body' = rename rn' body
       in ApplyContext { _ctxFree = fv'
                       , _ctxContext = context'
                       , _ctxBody = body'}

  rename rn ExceptingContext = ExceptingContext

  freeVariables (ApplyContext { _ctxFree = fv
                              , _ctxContext = context
                              , _ctxBody = body}) =
    fv `Set.union` (freeVariables body Set.\\ ctxBoundVariables context)
  
  freeVariables ExceptingContext = Set.empty

instance (Substitutable a, Substitution a ~ Subst) =>
         Substitutable (Contexted a) where
  type Substitution (Contexted a) = Subst
  substituteWorker s (ApplyContext { _ctxContext = context
                                   , _ctxBody = body}) =
    substituteCtx s context $ \s' context' -> do
      body' <- substitute s' body
      return $ ApplyContext { _ctxFree = ctxFreeVariables context'
                            , _ctxContext = context'
                            , _ctxBody = body'}

  substituteWorker _ ExceptingContext = return ExceptingContext

traverseContext :: (EvalMonad m, Substitutable a, Substitutable b,
                    Substitution a ~ Subst, Substitution b ~ Subst) =>
                   (a -> m b) -> Contexted a -> m (Contexted b)
traverseContext f ctx_x = do
  -- Ensure there's no name conflicts
  fresh_ctx_x <- freshen ctx_x

  case fresh_ctx_x of
    ApplyContext {_ctxContext = ctx, _ctxBody = x} -> do
      -- Transform the contents
      y <- assumeCtx ctx $ f x

      -- Rebuild the object
      return $ setContextedBody y fresh_ctx_x

    ExceptingContext ->
      return ExceptingContext

-- | 'traverseContext' with arguments reversed
inContext :: (EvalMonad m, Substitutable a, Substitutable b,
              Substitution a ~ Subst, Substitution b ~ Subst) =>
             Contexted a -> (a -> m b) -> m (Contexted b)
inContext = flip traverseContext

joinTraverseContext :: (EvalMonad m, Substitutable a, Substitutable b,
                  Substitution a ~ Subst, Substitution b ~ Subst) =>
                 (a -> m (Contexted b)) -> Contexted a -> m (Contexted b)
joinTraverseContext f c = liftM joinContext (traverseContext f c)

joinInContext :: (EvalMonad m, Substitutable a, Substitutable b,
                  Substitution a ~ Subst, Substitution b ~ Subst) =>
                 Contexted a -> (a -> m (Contexted b)) -> m (Contexted b)
joinInContext c f = liftM joinContext (traverseContext f c)

eliminateContext :: (EvalMonad m, Substitutable a, Substitution a ~ Subst) =>
                    (a -> m (Substitute.Nameless Subst b))
                 -> Contexted a
                 -> m b
eliminateContext f x = do
  y <- traverseContext f x
  return $ case discardContext y of Substitute.Nameless y' -> y'

-- | Merge two contexts, renaming variables if necessary to avoid name
--   capture.  Only the contexts are checked for name capture.
merge :: (Renameable a, Substitutable b, EvalMonad m,
          Substitution b ~ Subst) => 
         Contexted a -> Contexted b -> m (Contexted (a, b))
merge x y = mergeWith (,) x y

mergeWith :: (Renameable a, Substitutable b, EvalMonad m,
              Substitution b ~ Subst) => 
             (a -> b -> c) -> Contexted a -> Contexted b -> m (Contexted c)
mergeWith f (ApplyContext {_ctxFree = fv1, _ctxContext = c1, _ctxBody = x})
            (ApplyContext {_ctxFree = fv2, _ctxContext = c2, _ctxBody = y})
  | let bv = ctxBoundVariables c1
    in bv `intersects` fv2 || bv `intersects` ctxBoundVariables c2 = do
      -- Rename 'c2' and 'y' to eliminate name conflicts
      let rename_y = substituteCtx emptySubst c2 $ \subst c2' -> do
            y' <- substitute subst y
            return (c2', y')
      (c2', y') <- assumeCtx c1 rename_y

      -- Concatenate the contexts
      return $ ApplyContext { _ctxFree = fv1 `Set.union` ctxFreeVariables c2'
                            , _ctxContext = c1 ++ c2'
                            , _ctxBody = f x y'}

  | otherwise =
      -- No name conflicts.  Concatenate the contexts without renaming.
      return $ ApplyContext { _ctxFree = Set.union fv1 fv2
                            , _ctxContext = c1 ++ c2
                            , _ctxBody = f x y}

-- If either context raises an exception, the merged context raises an
-- exception
mergeWith _ ExceptingContext _ = return ExceptingContext
mergeWith _ _ ExceptingContext = return ExceptingContext

mergeList :: (Renameable a, Substitutable a, EvalMonad m,
              Substitution a ~ Subst) => 
             [Contexted a] -> m (Contexted [a])
mergeList [x]    = return $ mapContext (\x -> [x]) x
mergeList (x:xs) = mergeWith (:) x =<< mergeList xs
mergeList []     = return $ unitContext []

-- | Find a value indexed by a type.  Analogous to 'lookup'.
findByType :: BoxingMode b => Type -> [(Type, a)] -> TypeEvalM b (Maybe a)
findByType ptype assocs = search assocs
  where
    search ((ty, val) : assocs) = do
      found <- compareTypes ptype ty
      if found then return (Just val) else search assocs

    search [] = return Nothing

-- | Remove redundant definitions of the same dictionary from the context.
--   The outermost definition is retained.  When a definition is removed,
--   references of the discarded dictionary are renamed to a preexisting
--   dictionary.
nubContext :: (Renameable a, Substitutable a, EvalMonad m,
               Substitution a ~ Subst) =>
              Contexted a -> m (Contexted a)
nubContext ctx = liftTypeEvalM (nubContext' ctx)  

nubContext' :: (Renameable a, Substitutable a, Substitution a ~ Subst,
                BoxingMode b) =>
              Contexted a -> TypeEvalM b (Contexted a)
nubContext' ExceptingContext = return ExceptingContext 

nubContext' (ApplyContext {_ctxContext = ctx, _ctxBody = body_value}) =
  nub_items [] emptySubst [] ctx $ \subst ctx' -> do
    body_value' <- substitute subst body_value
    return $ ApplyContext { _ctxFree = ctxFreeVariables ctx'
                          , _ctxContext = ctx'
                          , _ctxBody = body_value'}
  where
    -- | Process the context starting at the outermost binding.
    --   First, apply the renaming that has been computed so far.
    --   Then either include the current item in the output or
    --   rename the variable it defines.
    nub_items :: BoxingMode b =>
                 [(Type, Var)]      -- ^ Dictionary types that are defined
              -> Subst              -- ^ Renaming of variables
              -> Ctx                -- ^ Output context (reversed)
              -> Ctx                -- ^ Input context
              -> (Subst -> Ctx -> TypeEvalM b a)
              -> TypeEvalM b a
    nub_items types subst new_ctx (c:cs) k =
      -- Rename this item
      substituteCtxItem subst c $ \subst' c' ->
      
      -- Only let-bindings of singleton types can be eliminated
      cond c'
      [ do LetCtx _ pat rhs <- it
           Just (op, _) <- lift $ deconVarAppType $ patMType pat
           aguard $ isSingletonCon op
           lift $ do
             -- Is there already a definition of this variable?
             defined_var <- findByType (patMType pat) types
             case defined_var of
               Just v ->
                 -- Eliminate this item and rename
                 eliminate_item subst' (patMVar pat) v
               Nothing ->
                 -- Keep this item and add to list of dictionary types
                 keep_item subst' (Just (patMType pat, patMVar pat)) c'
      , lift $ keep_item subst' Nothing c'
      ]
      where
        eliminate_item subst' eliminated_v replacement_v =
          let subst'' =
                modifyValueSubst
                (extendV eliminated_v (RenamedVar replacement_v)) subst'
          in nub_items types subst'' new_ctx cs k

        keep_item subst' new_type item =
          assumeCtxItem item $
          nub_items (maybe id (:) new_type types) subst' (item : new_ctx) cs k

    nub_items _ subst new_ctx [] k = k subst (reverse new_ctx)
