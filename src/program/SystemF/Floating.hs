{-| Selective floating-out of let and case statements.

Some code is aggressively moved upward as far as possible
to increase opportunities for other optimizations.  We float definitions of
singleton values, case-of-dictionary expressions, and case-of-read-variable 
expressions this way.
-}

{-# LANGUAGE FlexibleInstances, FlexibleContexts, ViewPatterns #-}
module SystemF.Floating
       (Context,
        ContextItem, contextItem,
        ContextExp(..),
        freshenContextExp,
        applyContext,
        floatedParameters',
        floatModule)
where

import Prelude hiding(mapM)
import Control.Applicative
import Control.Monad hiding(forM, mapM)
import Data.List
import Data.Maybe
import Data.Monoid
import qualified Data.IntSet as IntSet
import qualified Data.Set as Set
import Data.Traversable

import Common.Error
import Common.Identifier
import Common.Supply
import Common.MonadLogic
import Builtins.Builtins
import SystemF.Rename
import SystemF.Syntax
import SystemF.MemoryIR
import Type.Compare
import Type.Environment
import Type.Eval
import Type.Rename
import Type.Type
import Globals
import GlobalVar

-- | Do s1 and s2 intersect?
intersects :: Ord a => Set.Set a -> Set.Set a -> Bool
s1 `intersects` s2 = not $ Set.null $ Set.intersection s1 s2

-- | Is this a singleton type?
isSingletonType :: Type -> Bool
isSingletonType ty =
  case fromVarApp ty
  of Just (op, _) -> isSingletonCon op
     _ -> False

-- | Return true if this is the type of a floatable let-binding parameter.
--   The type must be a singleton type, and it must be in the type's natural
--   representation.
isFloatableSingletonParamType :: ParamType -> Bool
isFloatableSingletonParamType (prepr ::: ptype) =
  floatable_repr prepr && isSingletonType ptype
  where
    -- Only allow floating on values in their natural representation.
    -- If the representation is boxed or value,
    -- it's the natural representation.
    floatable_repr BoxPT = True
    floatable_repr (ValPT Nothing) = True
    floatable_repr _ = False

-- | Find a value indexed by a type.  Analogous to 'lookup'.
findByType :: IdentSupply Var -> TypeEnv -> Type -> [(Type, a)] -> IO (Maybe a)
findByType id_supply tenv ptype assocs = search assocs
  where
    search ((ty, val) : assocs) = do
      found <- compareTypes id_supply tenv ptype ty
      if found then return (Just val) else search assocs
    
    search [] = return Nothing

-- | Determine which parameters of a data constructor application
--   should be converted to direct style.  It's an error if the wrong
--   number of type parameters is given.  Returns a list containing a
--   'ParamType' for each
--   argument that should be converted.  The list length may be different
--   from the number of operands in an appliation term.  Excess operands
--   should not be floated.
directStyleAppParameters :: DataConType
                         -> [TypM]
                         -> [Maybe ParamType]
directStyleAppParameters dcon_type ty_args
  -- Float if all type arguments are supplied,
  -- and the representation is Value or Boxed
  | length ty_args /= length (dataConPatternParams dcon_type) +
                      length (dataConPatternExTypes dcon_type) =
      internalError "directStyleAppParameters: Wrong number of type arguments"
  | otherwise =
      let types = map fromTypM ty_args
          (field_types, _) =
            instantiateDataConTypeWithExistentials dcon_type types
      in map floatable field_types
  where
    -- Value and boxed operands are floatable
    floatable (rrepr ::: ty) =
      case rrepr
      of ValRT -> Just (ValPT Nothing ::: ty)
         BoxRT -> Just (BoxPT ::: ty)
         _ -> Nothing

-- | Based on the operator variable, pick which arguments should be floated.
--
-- A Just value means the argument should be moved, and has the given type.
-- If unknown, don't move an argument.
floatedParameters :: TypeEnv -> Var -> [TypM] -> [Maybe ParamType]
floatedParameters tenv op_var ty_args =
  case lookupDataCon op_var tenv
  of Just dcon_type ->
       -- Move the movable fields of data constructors
       directStyleAppParameters dcon_type ty_args ++ repeat Nothing
     Nothing
       | op_var `isPyonBuiltin` the_store ->
           -- Also move the argument of 'store', so that we can
           -- do store-load propagation 
           let [TypM store_type] = ty_args
           in [Nothing, Just (ValPT Nothing ::: store_type), Nothing]
       | op_var `isPyonBuiltin` the_storeBox ->
           -- Also move the argument of 'storeBox', so that we can
           -- do store-load propagation 
           let [TypM store_type] = ty_args
           in [Just (BoxPT ::: store_type), Nothing]
       | otherwise ->
           repeat Nothing

-- | Determine which parameters should be floated.  Return True if the
--   parameter should be floated, False otherwise.  For parameters where it's
--   unknown, False is returned.
floatedParameters' :: TypeEnv -> Var -> [TypM] -> [Bool]
floatedParameters' tenv op ty_args =
  map isJust $ floatedParameters tenv op ty_args

-------------------------------------------------------------------------------
-- Floatable contexts

-- | A floatable context.
--
--   The head of the list is the innermost context, and may reference variables
--   defined in outer contexts. 
type Context = [ContextItem]

-- | A @ContextItem@ is an expression sans body that can be floated
--   outward.  A list of free variables is included to help decide how far
--   to float.
data ContextItem =
  ContextItem
  { ctxUses :: Set.Set Var
  , ctxExp :: !ContextExp}

-- | Make a 'ContextItem'.
contextItem :: ContextExp -> ContextItem
contextItem e = ContextItem (freeVariablesContextExp e) e
  where
    freeVariablesContextExp (LetCtx _ pat rhs) =
      freeVariables (patMType pat) `Set.union` freeVariables rhs

    freeVariablesContextExp (CaseCtx _ scrutinee _ ty_args ty_pats pats) = 
      let scr_fv = freeVariables scrutinee
          ty_fv = Set.unions $ map freeVariables ty_args
          typat_fv = Set.unions $ map freeVariables [t | TyPatM _ t <- ty_pats]
          
          -- Get free variables from patterns; remove existential variables
          pat_fv1 = Set.unions $ map (freeVariables . patMType) pats
          pat_fv = foldr Set.delete pat_fv1 [v | TyPatM v _ <- ty_pats]
      in Set.unions [scr_fv, ty_fv, typat_fv, pat_fv]
   
    freeVariablesContextExp (LetfunCtx _ defgroup) =
      case defgroup
      of NonRec (Def v f) -> freeVariables f
         Rec defs -> 
           let functions_fv =
                 Set.unions $ map freeVariables [f | Def _ f <- defs]
               local_variables = [v | Def v _ <- defs]
           in foldr Set.delete functions_fv local_variables

-- | An expression sans body that can be floated outward.
data ContextExp =
    -- | A let expression that doesn't allocate local memory (not @LocalVarP@).
    --
    --   @let <pattern> = <rhs> in (...)@
    LetCtx ExpInfo PatM ExpM
    -- | A case expression with a single alternative.  The alternative's
    --   fields are included, sans the alternative body.
    --
    --   @case <scrutinee> of <alternative>. (...)@
  | CaseCtx ExpInfo ExpM !Var [TypM] [TyPatM] [PatM]
    -- | A letfun expression
  | LetfunCtx ExpInfo (DefGroup (Def Mem))

isLetfunCtx (LetfunCtx {}) = True
isLetfunCtx _ = False

renameContextItem :: Renaming -> ContextItem -> ContextItem
renameContextItem rn item =
  let uses' = Set.map (rename rn) $ ctxUses item
      exp' = renameContextExp rn $ ctxExp item
  in ContextItem uses' exp'

freshenContextItem :: (Monad m, Supplies m VarID) =>
                      ContextItem -> m (ContextItem, Renaming)
freshenContextItem item = do
    (e, rn) <- freshenContextExp $ ctxExp item
    return (item {ctxExp = e}, rn)
  
renameContextExp :: Renaming -> ContextExp -> ContextExp
renameContextExp rn cexp = 
  case cexp
  of LetCtx inf pat body ->
       LetCtx inf (renamePatM rn pat) (rename rn body)
     CaseCtx inf scr con ty_args ty_params params ->
       CaseCtx inf (rename rn scr) con (rename rn ty_args)
       (map (renameTyPatM rn) ty_params)  
       (map (renamePatM rn) params)
     LetfunCtx inf defs ->
       LetfunCtx inf (fmap (renameDefM rn) defs)

freshenContextExp :: (Monad m, Supplies m VarID) =>
                     ContextExp -> m (ContextExp, Renaming)
freshenContextExp (LetCtx inf pat body) = do
  (pat', rn) <- freshenPatM pat
  return (LetCtx inf pat' (rename rn body), rn)

freshenContextExp (CaseCtx inf scr alt_con ty_args ty_params params) = do
  (ty_params', ty_renaming) <- freshenTyPatMs ty_params 
  (params', param_renaming) <-
    freshenPatMs $ map (renamePatM ty_renaming) params
  let rn = ty_renaming `mappend` param_renaming
  return (CaseCtx inf scr alt_con ty_args ty_params' params', rn)

freshenContextExp (LetfunCtx inf defs) =
  case defs
  of NonRec (Def v f) -> do
       v' <- newClonedVar v
       let new_defs = NonRec (Def v' f)
       return (LetfunCtx inf new_defs, singletonRenaming v v')
     Rec defs -> do
       let local_vars = [v | Def v _ <- defs]
       new_vars <- mapM newClonedVar local_vars
       let rn = renaming $ zip local_vars new_vars
           new_defs = map (renameDefM rn) defs
       return (LetfunCtx inf (Rec new_defs), rn)

-- | Get the variables defined by the context
ctxDefs :: ContextItem -> [Var]
ctxDefs item =
  case ctxExp item
  of LetCtx _ pat _ -> [patMVar' pat]
     CaseCtx _ _ _ _ ty_params params ->
       [v | TyPatM v _ <- ty_params] ++ mapMaybe patMVar params
     LetfunCtx _ defs ->
       [v | Def v _ <- defGroupMembers defs]

-- | Extract the part of the context that satisfies the predicate, 
--   as well as any dependent parts of the context.
--   The context is partitioned into two contexts, of which the first is
--   dependent on and the second is independent of the predicate.
splitContext :: (ContextItem -> Bool) -> Context -> (Context, Context)
splitContext predicate ctx =
  -- Start processing from the outermost context and work inwards
  split Set.empty [] [] (reverse ctx)
  where
    split varset dep indep (c:ctx)
      | predicate c || ctxUses c `intersects` varset =
          -- This element of the context should be retained,
          -- or depends on something that should be retained.
          let varset' = foldr Set.insert varset $ ctxDefs c
          in split varset' (c : dep) indep ctx
      | otherwise =
          -- This element of the context is not dependent.
          split varset dep (c : indep) ctx

    split _ dep indep [] = (dep, indep)

-- | Remove redundant definitions of the same dictionary from the context.
--   The outermost definition is retained.
--
--   In the process, variables defined by discarded definitions are
--   renamed to other variables.
nubContext :: IdentSupply Var -> TypeEnv -> Context
           -> IO (Context, Renaming)
nubContext id_supply tenv ctx =
  nub_r [] mempty [] (reverse ctx)
  where
    -- | The context is processed in dependency order, from outermost to 
    --   innermost.  Later contexts may refer to variables defined in
    --   earlier contexts, so we rename them as we go along.
    nub_r :: [(Type, Var)]      -- ^ Dictionary types that are defined
          -> Renaming           -- ^ Renamed replaced variables
          -> Context            -- ^ Output context (not reversed)
          -> [ContextItem]      -- ^ Reversed context
          -> IO ([ContextItem], Renaming)
    nub_r types rn new_ctx (c:cs) =
      let rn_c = renameContextItem rn c -- Rename before inspecting
      in case ctxExp rn_c
         of LetCtx _ pat@(MemVarP {}) rhs
              | isFloatableSingletonParamType (patMParamType pat) -> do
                  -- This context can be eliminated
                  -- Is there already a definition of this variable?
                  defined_var <- findByType id_supply tenv (patMType pat) types
                  case defined_var of
                    Just v -> eliminate_item (patMVar' pat) v
                    Nothing ->
                      -- Not eliminated; add to context
                      let types' = (patMType pat, patMVar' pat) : types
                          new_ctx' = rn_c : new_ctx
                      in nub_r types' rn new_ctx' cs
            _ ->
              -- This context can't be eliminated
              let new_ctx' = rn_c : new_ctx
              in nub_r types rn new_ctx' cs
      where
        eliminate_item pvar v =
          -- Eliminate this item from the context.  Rename the variable
          -- that was bound by this item.
          nub_r types (insertRenaming pvar v rn) new_ctx cs

    nub_r _ rn new_ctx [] = return (new_ctx, rn)

-- | Apply a context to an expression to produce a new expression
applyContext :: Context -> ExpM -> ExpM
applyContext (c:ctx) e =
  let apply_c =
        case ctxExp c
        of LetCtx inf pat rhs -> ExpM $ LetE inf pat rhs e
           CaseCtx inf scr con ty_args ty_params params ->
             let alt = AltM $ Alt con ty_args ty_params params e
             in ExpM $ CaseE inf scr [alt]
           LetfunCtx inf defs ->
             ExpM $ LetfunE inf defs e
  in applyContext ctx $! apply_c

applyContext [] e = e

-------------------------------------------------------------------------------
-- The floating monad

data FloatCtx = 
  FloatCtx { fcVarSupply :: {-# UNPACK #-}!(IdentSupply Var)
             -- | The global type environment.  Local types are not added to
             --   the environment.
           , fcTypeEnv :: !TypeEnv
             -- | IDs of readable reference variables that are not in
             -- @fcTypeEnv@.
           , fcReadVars :: IntSet.IntSet
             -- | IDs of variables that are not global and not defined by a
             --   floated binding.  If a binding does /not/ depend on any of
             --   these variables, it can float to the top level.
           , fcLocalVars :: IntSet.IntSet
           }

newtype Flt a =
  Flt {runFlt :: FloatCtx -> IO (a, Context)}

-- | Perform floating on something top-level.  Verify that nothing was
--   floated out to the top level.
runTopLevelFlt :: Flt a -> FloatCtx -> IO a
runTopLevelFlt f ctx = do
  (x, floated_stuff) <- runFlt f ctx
  when (not $ null floated_stuff) $
    internalError "runTopLevelFlt: Something was floated to the top level"
  return x

liftFreshVarM :: FreshVarM a -> Flt a
liftFreshVarM m = Flt $ \ctx -> do
  result <- runFreshVarM (fcVarSupply ctx) m
  return (result, [])

-- | The 'Flt' monad keeps track of what bindings have been floated out.
--
--   In the list of floated bindings, bindings that are floated first
--   (outer bindings) appear later than bindings that are floated later
--   (inner bindings).
instance Monad Flt where
  return x = Flt (\_ -> return (x, []))
  m >>= k = Flt $ \ctx -> do
    (x, w1) <- runFlt m ctx
    (y, w2) <- runFlt (k x) ctx
    return (y, w2 ++ w1)

instance Functor Flt where
  fmap f (Flt g) = Flt (\ctx -> do (x, context) <- g ctx 
                                   return (f x, context))

instance Applicative Flt where
  pure = return
  (<*>) = ap

instance Supplies Flt (Ident Var) where
  fresh = Flt $ \ctx -> do x <- supplyValue (fcVarSupply ctx)
                           return (x, [])

getTypeEnv :: Flt TypeEnv
getTypeEnv = Flt $ \ctx -> return (fcTypeEnv ctx, [])

-- | Float a binding.  The binding will be renamed.
--   The returned renaming should be applied to any 
--   expression that may use the binding.
float :: ContextExp -> Flt Renaming
float ctx_exp = do
  -- Rename floated variables to avoid name conflicts
  (ctx_exp', rn) <- freshenContextExp ctx_exp
  let ctx = [contextItem ctx_exp']

  -- Float this binding
  Flt $ \_ -> return (rn, ctx)

-- | Helper function for calling 'nubContext'
fltNubContext :: FloatCtx -> Context -> IO (Context, Renaming)
fltNubContext ctx context =
  nubContext (fcVarSupply ctx) (fcTypeEnv ctx) context

-- | Run a computation that returns a predicate.  Capture floated bindings
--   that are produced by the computation, if they satisfy the predicate.
--
--   The process can rename and eliminate unneeded bindings.
--   A renaming is returned.  The
--   renaming should be applied to any code over which the bindings are in
--   scope.
grabContext :: Flt (a, ContextItem -> Bool) -> Flt (a, Context, Renaming)
grabContext m = Flt $ \ctx -> do
  ((x, predicate), context) <- runFlt m ctx
  
  -- Find dependent bindings
  let (dep, indep) = splitContext predicate context

  -- Remove redundant bindings
  (dep', rn) <- fltNubContext ctx dep

  return ((x, dep', rn), indep)

-- | Put floated bindings here if they satisfy the predicate or if they
--   depend on a binding that satisfies the predicate
anchor :: (ContextItem -> Bool) -> Flt ExpM -> Flt ExpM
anchor predicate m = do
  (exp, dep_context, rn) <- grabContext $ do
    x <- m
    return (x, predicate)

  return $ applyContext dep_context (rename rn exp)

-- | Put floated bindings here, if they depend on the specified variable
anchorOnVar :: Var -> Flt ExpM -> Flt ExpM
anchorOnVar v m = addLocalVar v $ anchor check m
  where
    check c = v `Set.member` ctxUses c

-- | Put floated bindings here, if they depend on the specified variables
anchorOnVars :: [Var] -> Flt ExpM -> Flt ExpM
anchorOnVars vs m = addLocalVars vs $ anchor check m
  where
    var_set = Set.fromList vs
    check c = ctxUses c `intersects` var_set

-- | Anchor bindings inside a top-level function.  Only function bindings
--   are permitted to float out.  Function bindings are floated only if they
--   do not depend on the given variables.
anchorOuterScope :: [Var] -> Flt ExpM -> Flt ExpM
anchorOuterScope vs m = addLocalVars vs $ anchor check m
  where
    vars_set = Set.fromList vs
    check c = not (isLetfunCtx $ ctxExp c) || ctxUses c `intersects` vars_set

-- | Get all floated bindings.  No bindings are floated out of this call.
getFloatedBindings :: Flt a -> Flt (a, Context)
getFloatedBindings m = Flt $ \ctx -> do
  (x, context) <- runFlt m ctx
  return ((x, context), [])

isReadReference :: Var -> Flt Bool
isReadReference v = Flt $ \ctx ->
  let readable_local = fromIdent (varID v) `IntSet.member` fcReadVars ctx
      readable_global = case lookupType v (fcTypeEnv ctx)
                        of Just (ReadRT ::: _) -> True
                           _ -> False
  in return (readable_local || readable_global, [])

-- | Indicate that a variable is a readable reference
addReadVar :: Var -> Flt ExpM -> Flt ExpM
addReadVar v m = Flt $ \ctx ->
  let ctx' = ctx {fcReadVars = IntSet.insert (fromIdent $ varID v) $
                               fcReadVars ctx}
  in runFlt m ctx'

-- | Indicate that a variable is a local variable
addLocalVar :: Var -> Flt ExpM -> Flt ExpM
addLocalVar v m = Flt $ \ctx ->
  let ctx' = ctx {fcLocalVars = IntSet.insert (fromIdent $ varID v) $
                                fcLocalVars ctx}
  in runFlt m ctx'

addLocalVars :: [Var] -> Flt ExpM -> Flt ExpM
addLocalVars vs m = Flt $ \ctx ->
  let ids = map (fromIdent . varID) vs
      ctx' = ctx {fcLocalVars = foldr IntSet.insert (fcLocalVars ctx) ids}
  in runFlt m ctx'

-- | Add a pattern variable to the environment.
--   If the pattern binds a readable variable, indicate that the variable is
--   a readable reference.  The pattern's type is ignored.
--
--   A @LocalVarP@ is counted as a readable reference.
--   It's only a readable reference in the body of a let-binding, not the rhs.
addPatternVar :: PatM -> Flt ExpM -> Flt ExpM
addPatternVar pat m = addRnPatternVar mempty pat m

-- | Rename the pattern and then add it to the environment.
--   The renaming is applied to the pattern-bound variables as well as the
--   types.
--
--   We use this when a binding is renamed and floated.
addRnPatternVar :: Renaming -> PatM -> Flt ExpM -> Flt ExpM
addRnPatternVar rn pat =
  case pat
  of MemVarP {}
       | ReadPT <- patMRepr pat -> addReadVar (rename rn $ patMVar' pat)
     LocalVarP {} -> addReadVar (rename rn $ patMVar' pat)
     _ -> id

addPatternVars ps x = foldr addPatternVar x ps

addRnPatternVars rn ps x = foldr (addRnPatternVar rn) x ps

-------------------------------------------------------------------------------

-- | Flatten an application.  Some of the application's operands are
--   bound to new variables and floated up a short distance.  They aren't 
--   floated past any preexisting variable bindings.
--
--   The purpose of flattening is to partially convert the application to
--   direct style.  For example, flattening @f(g(x), y, h(1))@ produces
--
--   > let tmp1 = g(x) in
--   > let tmp2 = h(1) in
--   > f(tmp1, y, tmp2)
--
--   This goes on simultaneously with regular, long-distance floating.
--   Dictionary construction is floated as far as possible.
--   Data constructor applications are converted to direct style, except
--   that fields that are initialized by a writer function are left alone.
--   Other terms are not converted to direct style.
--   Lambda expressions are long-distance floated if they would be flattened,
--   or left in place otherwise.
flattenApp :: ExpM -> Flt (ExpM, Context)
flattenApp expression =
  case fromExpM expression
  of AppE inf (ExpM (VarE _ op_var)) ty_args args ->
       -- Convert this expression to direct style
       createFlattenedApp inf op_var ty_args args

     AppE inf op ty_args args -> do
       -- Don't flatten this expresion.  Flatten subexpressions.
       (op', op_context) <- flattenApp op
       (args', arg_contexts) <- mapAndUnzipM flattenApp args
       let new_exp = ExpM $ AppE inf op' ty_args args'
       return (new_exp, concat (op_context : arg_contexts))

     _ -> do
       -- Don't alter
       new_exp <- floatInExp expression
       return (new_exp, [])

createFlattenedApp inf op_var ty_args args = do
  -- Determine which parameters should be moved
  tenv <- getTypeEnv
  let moved = floatedParameters tenv op_var ty_args

  -- Flatten arguments
  (unzip -> (args', concat -> arg_contexts)) <- zipWithM flatten_arg moved args
  
  -- Create the new expression
  let new_expr = ExpM $ AppE inf (ExpM $ VarE inf op_var) ty_args args'

  -- If this is a dictionary expression, then float it.
  -- Otherwise return it.
  if isDictionaryDataCon op_var
    then do dict_expr <- floatDictionary inf new_expr op_var ty_args
            return (dict_expr, arg_contexts)
    else return (new_expr, arg_contexts)
  where
    flatten_arg Nothing arg =
      -- This argument stays in place
      flattenApp arg

    -- Special case: lambda (...) becomes a letfun and gets floated
    flatten_arg (Just _) arg@(ExpM (LamE lam_info f)) = do
      f' <- floatInFun (LocalAnchor []) f

      -- Bind the function to a new variable and float it outward
      tmpvar <- newAnonymousVar ObjectLevel
      let floated_ctx = LetfunCtx lam_info (NonRec (Def tmpvar f'))
      rn <- float floated_ctx
      
      -- Get the renamed variable
      let floated_var = rename rn tmpvar
      return (ExpM $ VarE inf floated_var, [])

    flatten_arg (Just param_type) arg = do
      (arg_expr, subcontext) <- flattenApp arg

      -- If this argument is trivial, leave it where it is.
      -- Otherwise, bind it to a new variable.
      if is_trivial_arg arg_expr
        then return (arg, [])
        else do
          tmpvar <- newAnonymousVar ObjectLevel
          let binding =
                contextItem $ LetCtx inf (memVarP tmpvar param_type) arg_expr
          return (ExpM $ VarE inf tmpvar, subcontext ++ [binding])
    
    is_trivial_arg (ExpM (VarE {})) = True
    is_trivial_arg (ExpM (LitE {})) = True
    is_trivial_arg _ = False

floatInExp :: ExpM -> Flt ExpM
floatInExp (ExpM expression) =
  case expression
  of VarE {} -> return $ ExpM expression
     LitE {} -> return $ ExpM expression
     AppE {} -> floatInApp (ExpM expression)
     LamE inf f -> do
       f' <- floatInFun (LocalAnchor []) f
       return $ ExpM $ LamE inf f'
     
     -- Special case: let x = lambda (...) becomes a letfun
     LetE inf pat@(MemVarP {}) (ExpM (LamE _ f)) body ->
       floatInExp $ ExpM $ LetfunE inf (NonRec (Def (patMVar' pat) f)) body

     LetE inf pat rhs body ->
       floatInLet inf pat rhs body

     LetfunE inf defs body ->
       floatInLetfun inf defs body

     CaseE inf scr alts ->
       floatInCase inf scr alts

floatInApp :: ExpM -> Flt ExpM
floatInApp expression = do
  -- Flatten the expression and catch any floated bindings that depend on
  -- local variables
  ((new_expression, local_context), dependent_context, rn) <-
    grabContext flatten_expression 
  
  -- Put the dependent context inside the local context
  return $ applyContext local_context $
           applyContext dependent_context $
           rename rn new_expression
  where 
    flatten_expression = do
      -- Flatten the expression
      result@(_, local_context) <- flattenApp expression
    
      -- Find the new variable bindings that were created
      let local_defs = IntSet.fromList $ map (fromIdent . varID) $
                       concatMap ctxDefs local_context
    
      -- Any floated bindings that mention these variables should be caught
      let check c = or [fromIdent (varID v) `IntSet.member` local_defs
                       | v <- Set.toList $ ctxUses c]

      return (result, check)

floatInLet inf pat rhs body =
  case pat
  of MemVarP pat_var pat_type _ -> do
       -- Float the RHS
       rhs' <- floatInExp rhs
       if isFloatableSingletonParamType pat_type
         then do
           -- Float this binding.  Since the binding may be combined with
           -- other bindings, set the uses to 'many'.
           rn <- float $ LetCtx inf (setPatMUses Many pat) rhs'

           -- Rename and continue processing the body
           addPatternVar pat $ floatInExp $ rename rn body
         else do
           body' <- addPatternVar pat $ anchorOnVar pat_var $ floatInExp body
           return $ ExpM $ LetE inf pat rhs' body'

     LocalVarP pat_var pat_type pat_dict uses -> do
       pat_dict' <- floatInExp pat_dict
       rhs' <- anchorOnVar pat_var $ floatInExp rhs
       body' <- addPatternVar pat $ anchorOnVar pat_var $ floatInExp body
       let pat' = LocalVarP pat_var pat_type pat_dict' uses
       return $ ExpM $ LetE inf pat' rhs' body'

     MemWildP {} -> internalError "floatInLet"

floatInLetfun inf defs body = do
  -- Float the contents of these functions.  If it's a recursive binding,
  -- don't float anything that mentions one of the local functions.
  defs' <-
    case defs
    of NonRec {} -> traverse (float_function_body []) defs
       Rec {}    -> traverse (float_function_body def_vars) defs

  -- Float these functions
  rn <- float (LetfunCtx inf defs')
  
  -- Float the body
  floatInExp $ rename rn body
  where
    def_vars = [v | Def v _ <- defGroupMembers defs]
    
    -- Perform floating in the function body
    float_function_body local_vars (Def v f) = do
      f' <- floatInFun (LocalAnchor local_vars) f
      return (Def v f')

floatInCase inf scr alts = do
  scr' <- floatInExp scr
  floatable <- is_floatable scr'
  if floatable
    then do rn <- float ctx
            -- The floated variables were renamed. 
            -- Add the /renamed/ pattern variables to the environment.
            addRnPatternVars rn alt_params $ floatInExp $ rename rn alt_body
    else do alts' <- mapM floatInAlt alts
            return $ ExpM $ CaseE inf scr' alts'
  where
    AltM (Alt con alt_targs alt_tparams alt_params alt_body) = head alts
    ctx = CaseCtx inf scr con alt_targs alt_tparams alt_params
    
    is_floatable scr'
      | length alts /= 1 =
          -- Don't float a case with multiple alternatives
          return False
      | isDictionaryDataCon con =
          -- Always float dictionary inspection 
          return True
      | ExpM (VarE _ scr_var) <- scr' =
          -- Float if scrutinee is a readable reference
          isReadReference scr_var
      | otherwise =
          return False

-- | Float out a dictionary construction expression
floatDictionary inf dict_expr op_var ty_args = do
  -- Compute the type of the dictionary
  tenv <- getTypeEnv
  let dict_repr ::: dict_type = dictionary_type tenv
  
  -- Create the binding that will be floated
  dict_var <- newAnonymousVar ObjectLevel
  let dict_param_type = returnReprToParamRepr dict_repr ::: dict_type
      ctx = LetCtx inf (memVarP dict_var dict_param_type) dict_expr
      
  -- Return the variable
  rn <- float ctx
  return $ ExpM $ VarE inf (rename rn dict_var)
  where
    dictionary_type tenv
      | Just dc_type <- lookupDataCon op_var tenv =
        -- Determine which type arguments are universally quantified
        let num_universal_types = length $ dataConPatternParams dc_type
            num_existential_types = length $ dataConPatternExTypes dc_type
            inst_type_args = map fromTypM $ take num_universal_types ty_args
               
            -- Existential variables cannot appear in the return type
            inst_ex_args = replicate num_existential_types $
                           internalError "floatDictionary: Unexpected use of existential variable"
            (_, _, result_type) =
              instantiateDataConType dc_type inst_type_args inst_ex_args
        in result_type
      | otherwise = internalError "floatDictionary"

floatInAlt :: AltM -> Flt AltM
floatInAlt (AltM alt) = do
  body' <- addPatternVars (altParams alt) $
           anchorOnVars local_vars $
           floatInExp (altBody alt)
  return $ AltM $ alt {altBody = body'}
  where
    local_vars =
      [v | TyPatM v _ <- altExTypes alt] ++ mapMaybe patMVar (altParams alt)

-- | What needs to be anchored when floating in a function definition.
data FunAnchor =
    LocalAnchor [Var]           -- ^ Anchor the given local variables
  | GlobalAnchor                -- ^ Anchor everything except function bindings

-- | Perform floating on a function.
--
--   If a Just value, @m_local_vars@ is the set of variables whose definitions 
--   should not be floated out of the function.  If Nothing, then 
--   it's a top-level function, and only function bindings may be floated out.
--   The function's parameters will not be floated out
--   regardless of the value given.
floatInFun :: FunAnchor -> FunM -> Flt FunM
floatInFun m_local_vars (FunM fun) = do
  body <- addPatternVars (funParams fun) $ anchor_local_vars $
          floatInExp (funBody fun)
  return $ FunM $ fun {funBody = body}
  where
    anchor_local_vars m =
      case m_local_vars
      of GlobalAnchor -> anchorOuterScope param_vars m
         LocalAnchor extra_local_vars ->
           anchorOnVars (param_vars ++ extra_local_vars) m

    param_vars = [v | TyPatM v _ <- funTyParams fun] ++
                 mapMaybe patMVar (funParams fun)

-- | Perform floating on a top-level function definition.
--   No bindings are floated out of the function.
floatInTopLevelDef :: Def Mem -> Flt (Def Mem)
floatInTopLevelDef (Def v f) = do
  f' <- floatInFun GlobalAnchor f
  return (Def v f')

-- | Perform floating on a top-level definition group.
--
--   If function bindings were floated out, they may be produced as
--   a new definition group.
floatInTopLevelDefGroup :: DefGroup (Def Mem) -> Flt [DefGroup (Def Mem)]
floatInTopLevelDefGroup defgroup = 
  case defgroup
  of NonRec def -> do
       (def', bindings) <- getFloatedBindings $ floatInTopLevelDef def
       return $! case makeDefGroup bindings
                 of Nothing -> [NonRec def']
                    Just b_defs -> [b_defs, NonRec def']
     Rec defs -> do
       (defs', bindings) <- getFloatedBindings $ mapM floatInTopLevelDef defs
       return $! case makeDefGroup bindings
                 of Nothing -> [Rec defs']
                    Just b_defs -> [mergeDefGroups b_defs $ Rec defs']

-- | Perform floating on an exported function definition.  The floated
--   definitions become a new definition group.
floatInExport :: Export Mem -> Flt ([DefGroup (Def Mem)], Export Mem)
floatInExport exp = do
  (f', bindings) <-
    getFloatedBindings $ floatInFun GlobalAnchor $ exportFunction exp
  return (maybeToList $ makeDefGroup bindings, exp {exportFunction = f'})

mergeDefGroups :: DefGroup (Def Mem)
               -> DefGroup (Def Mem)
               -> DefGroup (Def Mem)
mergeDefGroups dg1 dg2 = Rec (defGroupMembers dg1 ++ defGroupMembers dg2)
    
makeDefGroup :: Context -> Maybe (DefGroup (Def Mem))
makeDefGroup xs = case concatMap (fromLetfunCtx . ctxExp) xs
                  of []   -> Nothing
                     defs -> Just (Rec defs)
  where
    fromLetfunCtx (LetfunCtx _ dg) = defGroupMembers dg

floatModule :: Module Mem -> IO (Module Mem)
floatModule (Module mod_name defss exports) =
  withTheNewVarIdentSupply $ \id_supply -> do
    tenv <- readInitGlobalVarIO the_memTypes
    let flt_env = FloatCtx {fcVarSupply = id_supply,
                            fcTypeEnv = tenv,
                            fcReadVars = IntSet.empty}
    defss' <- runTopLevelFlt float_defss flt_env
    (unzip -> (export_defs, exports')) <-
      runTopLevelFlt float_exports flt_env
    return $ Module mod_name (concat $ defss' ++ export_defs) exports'
  where
    float_defss = mapM floatInTopLevelDefGroup defss
    float_exports = mapM floatInExport exports
    
    