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
        isTrivialExp,
        floatedParameters',
        floatModule)
where

import Prelude hiding(mapM)
import Control.Applicative
import Control.Monad hiding(forM, mapM)
import Control.Monad.Trans
import Data.List
import Data.Maybe
import Data.Monoid
import qualified Data.IntSet as IntSet
import qualified Data.Set as Set
import Data.Traversable
import Debug.Trace
import Text.PrettyPrint.HughesPJ hiding(float)

import Common.Error
import Common.Identifier
import Common.Supply
import Common.MonadLogic
import Builtins.Builtins
import SystemF.Demand
import qualified SystemF.DictEnv as DictEnv
import SystemF.Rename
import SystemF.ReprDict
import SystemF.Syntax
import SystemF.MemoryIR
import SystemF.PrintMemoryIR
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

-- | Return True if a case statement deconstructing a value with this data
--   constructor should always be floated.
--
--   These data types have a single constructor.  Furthermore, they are
--   value data types (therefore cheap to construct) or inserted by the
--   compiler (therefore we can somewhat bound the amount of work performed
--   by executing them).
isFloatableCaseDataCon :: Var -> Bool
isFloatableCaseDataCon con =
  isDictionaryDataCon con ||
  con `isPyonBuiltin` the_someIndexedInt ||
  isUnboxedTupleCon con

-- | If the given application term is floatable, then determine its type
--   and return a binder for it.  Otherwise return Nothing.
floatableAppParamType :: TypeEnv -> Var -> [TypM] -> [ExpM] -> Maybe ParamType
floatableAppParamType tenv op_var ty_args args
  | isDictionaryDataCon op_var = Just dictionary_binding
  | isReprCon op_var           = Just repr_binding
  | op_var `isPyonBuiltin` the_defineIntIndex &&
    length args == 1           = Just intindex_binding
  | otherwise                  = Nothing
  where
    -- Type of op_var, if it is a data constructor
    Just dc_type = lookupDataCon op_var tenv
    
    -- Type of op_var
    Just op_type = lookupType op_var tenv

    -- The parameter type for a floated dictionary expression
    dictionary_binding =
      -- Determine which type arguments are universally quantified
      let num_universal_types = length $ dataConPatternParams dc_type
          num_existential_types = length $ dataConPatternExTypes dc_type
          inst_type_args = map fromTypM $ take num_universal_types ty_args
               
          -- Existential variables cannot appear in the return type
          inst_ex_args = replicate num_existential_types $
                         internalError "floatDictionary: Unexpected use of existential variable"
      in case instantiateDataConType dc_type inst_type_args inst_ex_args
         of (_, _, rrepr ::: rtype) ->
              returnReprToParamRepr rrepr ::: rtype

    -- The parameter type for a floated Repr expression
    repr_binding =
      let app_type = computeInstantiatedType op_type ty_args
      in case drop_arg_types (length args) app_type
         of BoxRT ::: t -> BoxPT ::: t
      where
        drop_arg_types 0 t = t
        drop_arg_types n (BoxRT ::: (FunT _ rt)) = drop_arg_types (n - 1) rt

    intindex_binding =
      -- Return value has type SomeIndexedInt
      ValPT Nothing ::: VarT (pyonBuiltin the_SomeIndexedInt)

-- | Return True if the expression is a variable or literal, False otherwise.
isTrivialExp :: ExpM -> Bool
isTrivialExp (ExpM (VarE {})) = True
isTrivialExp (ExpM (LitE {})) = True
isTrivialExp _                = False

-- | Return True if the expression performs data movement,
--   i.e., if it's a load, store, or copy expression.
isDataMovementExp :: ExpM -> Bool
isDataMovementExp expr =
  case unpackVarAppM expr
  of Just (op, _, _)
       | op `isPyonBuiltin` the_store ||
         op `isPyonBuiltin` the_copy ||
         op `isPyonBuiltin` the_load -> True
     _ -> False

-- | Return True if the expression is worth floating out of a data constructor.
--   If the expression performs any computation other than moving data into
--   the destination, it's worth floating.
isOkParamForFloating :: ExpM -> Bool
isOkParamForFloating e = not (isTrivialExp e || isDataMovementExp e)

-- | Find a value indexed by a type.  Analogous to 'lookup'.
findByType :: IdentSupply Var -> TypeEnv -> Type -> [(Type, a)] -> IO (Maybe a)
findByType id_supply tenv ptype assocs = search assocs
  where
    search ((ty, val) : assocs) = do
      found <- compareTypes id_supply tenv ptype ty
      if found then return (Just val) else search assocs
    
    search [] = return Nothing

-- | Compute the type of a type application.  We assume there's no 
--   type error in the application.
computeInstantiatedType :: ReturnType -> [TypM] -> ReturnType
computeInstantiatedType op_rtype args = apply_types op_rtype args
  where
    apply_types op_rtype [] = op_rtype
    apply_types (BoxRT ::: FunT arg_ptype ret_rtype) (arg:args) =
      case arg_ptype
      of ValPT (Just param) ::: _ ->
           let subst = singletonSubstitution param (fromTypM arg)
           in apply_types (substituteBinding subst ret_rtype) args
         ValPT Nothing ::: _ -> ret_rtype
         _ -> bad_application

    apply_types _ _ = bad_application

    bad_application = internalError "Unexpected type error during floating"

-- | How to float a parameter of a data constructor or function.
data FltParamType =
    -- | Do not float this parameter
    Don'tFloat
    -- | Float this parameter by assigning its value to a local variable
  | FloatParam ParamType Specificity
    -- | Float this parameter by writing it into a local variable, then
    --   copying the local variable
  | FloatLocal Type Specificity

-- | Determine which parameters of a data constructor application
--   should be converted to direct style.  It's an error if the wrong
--   number of type parameters is given.  Returns a list containing a
--   'ParamType' for each
--   argument that should be converted.  The list length may be different
--   from the number of operands in an appliation term.  Excess operands
--   should not be floated.
--
--   Specificities are used to help decide whether to float reference fields.
--   A reference field is not floated if a specificity is not provided.
directStyleAppParameters :: DataConType
                         -> [TypM]
                         -> [Specificity]
                         -> [FltParamType]
directStyleAppParameters dcon_type ty_args spcs
  | length ty_args /= length (dataConPatternParams dcon_type) +
                      length (dataConPatternExTypes dcon_type) =
      internalError "directStyleAppParameters: Wrong number of type arguments"
  | otherwise =
      let types = map fromTypM ty_args
          (field_types, _) =
            instantiateDataConTypeWithExistentials dcon_type types
      in zipWith floatable field_types (map Just spcs ++ repeat Nothing)
  where
    -- Value and boxed operands are floatable.
    -- Read operands may be floated, depending on how they are demanded.
    floatable (rrepr ::: ty) spc =
      case rrepr
      of ValRT -> FloatParam (ValPT Nothing ::: ty) (fromMaybe Used spc)
         BoxRT -> FloatParam (BoxPT ::: ty) (fromMaybe Used spc)
         ReadRT -> case spc
                   of Nothing -> Don'tFloat
                      Just Unused -> Don'tFloat
                      Just s -> FloatLocal ty s

-- | Based on the operator variable, pick which arguments should be floated.
--
-- A Just value means the argument should be moved, and has the given type.
-- If unknown, don't move an argument.
floatedParameters :: TypeEnv -> Specificity -> Var -> [TypM] -> [FltParamType]
floatedParameters tenv spc op_var ty_args =
  case lookupDataCon op_var tenv
  of Just dcon_type ->
       -- Move the movable fields of data constructors
       case spc
       of Decond con _ _ spcs
            | con /= op_var ->
              internalError "floatedParameters: Invalid demand"
            | otherwise ->
              directStyleAppParameters dcon_type ty_args spcs ++ repeat Don'tFloat
          _ ->
            directStyleAppParameters dcon_type ty_args [] ++ repeat Don'tFloat
     Nothing
       | op_var `isPyonBuiltin` the_store ->
           -- Also move the argument of 'store', so that we can
           -- do store-load propagation 
           let [TypM store_type] = ty_args
           in [FloatParam (ValPT Nothing ::: store_type) Used,
               Don'tFloat]
       | op_var `isPyonBuiltin` the_storeBox ->
           -- Also move the argument of 'storeBox', so that we can
           -- do store-load propagation 
           let [TypM store_type] = ty_args
           in [FloatParam (BoxPT ::: store_type) Used,
               Don'tFloat]
       | op_var `isPyonBuiltin` the_copy ->
           -- Move the source argument of 'copy' to increase the success rate
           -- of copy elimination
           let [TypM store_type] = ty_args
           in [Don'tFloat,
               FloatParam (ReadPT ::: store_type) Used,
               Don'tFloat]
       | otherwise ->
           repeat Don'tFloat

-- | Determine which parameters should be floated.  Return True if the
--   parameter should be floated, False otherwise.  For parameters where it's
--   unknown, False is returned.
floatedParameters' :: TypeEnv -> Var -> [TypM] -> [Bool]
floatedParameters' tenv op ty_args =
  map is_floated $ floatedParameters tenv Used op ty_args
  where
    is_floated (FloatParam{}) = True
    is_floated _ = False

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
       -- Don't need to rename inside the definition
       v' <- newClonedVar v
       let new_defs = NonRec (Def v' f)
       return (LetfunCtx inf new_defs, singletonRenaming v v')
     Rec defs -> do
       -- Rename bodies of all local functions
       let local_vars = [v | Def v _ <- defs]
       new_vars <- mapM newClonedVar local_vars
       let rn = renaming $ zip local_vars new_vars
           new_defs = [Def new_var (rename rn f)
                      | (new_var, Def _ f) <- zip new_vars defs]
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
             -- | Representation dictionaries in scope
           , fcDictEnv :: MkDictEnv
             -- | Indexed integers in scope
           , fcIntEnv :: IntIndexEnv
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

instance MonadIO Flt where
  liftIO m = Flt (\_ -> do {x <- m; return (x, [])})

instance ReprDictMonad Flt where
  getVarIDs = Flt $ \ctx -> return (fcVarSupply ctx, [])
  getTypeEnv = Flt $ \ctx -> return (fcTypeEnv ctx, [])
  getDictEnv = Flt $ \ctx -> return (fcDictEnv ctx, [])
  getIntIndexEnv = Flt $ \ctx -> return (fcIntEnv ctx, [])
  localDictEnv f m = Flt $ \ctx ->
    let ctx' = ctx {fcDictEnv = f $ fcDictEnv ctx}
    in runFlt m ctx'
  localIntIndexEnv f m = Flt $ \ctx ->
    let ctx' = ctx {fcIntEnv = f $ fcIntEnv ctx}
    in runFlt m ctx'

-- | Float a binding, when the bound variable is a fresh variable.
--   This should not be used to float preexisting bindings; use
--   'floatAndRename' for that.
float :: ContextExp -> Flt ()
float ctx_exp = Flt $ \_ -> return ((), [contextItem ctx_exp])

-- | Float a binding.  The binding will be renamed.
--   The returned renaming should be applied to any 
--   expression that may use the binding.
floatAndRename :: ContextExp -> Flt Renaming
floatAndRename ctx_exp = do
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
  (x, _) <- anchor' predicate (do {x <- m; return (x, ())})
  return x

anchor' :: (ContextItem -> Bool) -> Flt (ExpM, a) -> Flt (ExpM, a)
anchor' predicate m = do
  ((exp, other_data), dep_context, rn) <- grabContext $ do
    x <- m
    return (x, predicate)

  return (applyContext dep_context (rename rn exp), other_data)

-- | Put floated bindings here, if they depend on the specified variable
anchorOnVar :: Var -> Flt ExpM -> Flt ExpM
anchorOnVar v m = addLocalVar v $ anchor check m
  where
    check c = v `Set.member` ctxUses c

anchorOnVar' :: Var -> Flt (ExpM, a) -> Flt (ExpM, a)
anchorOnVar' v m = addLocalVar v $ anchor' check m
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
addLocalVar :: Var -> Flt a -> Flt a
addLocalVar v m = Flt $ \ctx ->
  let ctx' = ctx {fcLocalVars = IntSet.insert (fromIdent $ varID v) $
                                fcLocalVars ctx}
  in runFlt m ctx'

addLocalVars :: [Var] -> Flt a -> Flt a
addLocalVars vs m = Flt $ \ctx ->
  let ids = map (fromIdent . varID) vs
      ctx' = ctx {fcLocalVars = foldr IntSet.insert (fcLocalVars ctx) ids}
  in runFlt m ctx'

-- | Add a pattern variable to the environment.
--   If the pattern binds a readable variable, indicate that the variable is
--   a readable reference.  If the pattern binds a representation dictionary,
--   add the dictionary to the environment.
--
--   A @LocalVarP@ is counted as a readable reference.
--   It's only a readable reference in the body of a let-binding, not the rhs.
addPatternVar :: PatM -> Flt ExpM -> Flt ExpM
addPatternVar pat m = addRnPatternVar mempty pat m

-- | Rename the pattern and then add it to the environment.
--
--   The renaming is applied to the pattern-bound variables as well as the
--   pattern's types.
--
--   We use this when a binding is renamed and floated.
addRnPatternVar :: Renaming -> PatM -> Flt ExpM -> Flt ExpM
addRnPatternVar rn pat =
  case pat
  of MemVarP {}
       | ReadPT <- patMRepr pat -> addReadVar (rename rn $ patMVar' pat)
     LocalVarP {} -> addReadVar (rename rn $ patMVar' pat)
     MemVarP pat_var ptype uses ->
       let rn_pattern =
             MemVarP (rename rn pat_var) (renameBinding rn ptype) uses
       in saveReprDictPattern rn_pattern
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
--
--   Initializers (copy and store calls) are floated only if
--   @float_initializers@ is True.  They should only be floated when the
--   application appears in the RHS of an assignment that can be eliminated.
flattenApp :: Bool -> Specificity -> ExpM -> Flt (ExpM, Context)
flattenApp float_initializers spc expression =
  case fromExpM expression
  of AppE inf (ExpM (VarE _ op_var)) ty_args args ->
       -- Convert this expression to direct style
       createFlattenedApp float_initializers spc inf op_var ty_args args

     AppE inf op ty_args args -> do
       -- Don't flatten this expresion.  Flatten subexpressions.
       (op', op_context) <- flattenApp False Used op
       (args', arg_contexts) <- mapAndUnzipM (flattenApp False Used) args
       let new_exp = ExpM $ AppE inf op' ty_args args'
       return (new_exp, concat (op_context : arg_contexts))

     _ -> do
       -- Don't alter
       new_exp <- floatInExp expression
       return (new_exp, [])

createFlattenedApp float_initializers spc inf op_var ty_args args = do
  -- Determine which parameters should be moved
  tenv <- getTypeEnv
  let moved = floatedParameters tenv spc op_var ty_args

  -- Flatten arguments
  (unzip -> (args', concat -> arg_contexts)) <- zipWithM flatten_arg moved args
  
  -- Create the new expression
  let new_expr = ExpM $ AppE inf (ExpM $ VarE inf op_var) ty_args args'

  -- If this is a floatable expression, then float it and substitute a variable
  -- in its place.  Otherwise return it.
  floated_expr <- 
    case floatableAppParamType tenv op_var ty_args args'
    of Just ptype -> do
         floated_var <- newAnonymousVar ObjectLevel
         float (LetCtx inf (memVarP floated_var ptype) new_expr)
         return (ExpM $ VarE inf floated_var)
       Nothing ->
         return new_expr

  return (floated_expr, arg_contexts)
  where
    flatten_arg Don'tFloat arg =
      -- This argument stays in place
      flattenApp False Used arg

    -- Special case: lambda (...) becomes a letfun and gets floated
    flatten_arg (FloatParam _ _) arg@(ExpM (LamE lam_info f)) = do
      f' <- floatInFun (LocalAnchor []) f

      -- Bind the function to a new variable and float it outward
      tmpvar <- newAnonymousVar ObjectLevel
      let floated_ctx = LetfunCtx lam_info (NonRec (Def tmpvar f'))
      float floated_ctx
      
      -- Return the function variable
      return (ExpM $ VarE inf tmpvar, [])

    flatten_arg (FloatParam param_type spc) arg = do
      (arg_expr, subcontext) <- flattenApp False spc arg

      -- If this argument is trivial, leave it where it is.
      -- Otherwise, bind it to a new variable.
      if isTrivialExp arg_expr
         || (isDataMovementExp arg_expr && not float_initializers)
        then return (arg_expr, subcontext)
        else flatten_mem_arg arg_expr subcontext param_type spc
  
    flatten_arg (FloatLocal ty spc) arg = do
      (arg_expr, subcontext) <- flattenApp False spc arg

      -- If this argument is trivial, leave it where it is.
      -- Otherwise, bind it to a new variable.
      if isTrivialExp arg_expr
         || (isDataMovementExp arg_expr && not float_initializers)
        then return (arg_expr, subcontext)
        else flatten_local_arg arg_expr subcontext ty spc 

    flatten_mem_arg arg_expr subcontext param_type spc = do
      tmpvar <- newAnonymousVar ObjectLevel
      let binder = setPatMDmd (Dmd ManyUnsafe spc) $ memVarP tmpvar param_type 
          binding = contextItem $ LetCtx inf binder arg_expr
      return (ExpM $ VarE inf tmpvar, binding : subcontext)

    flatten_local_arg arg_expr subcontext param_type spc = do
      -- Write the value to a temporary variable
      tmpvar <- newAnonymousVar ObjectLevel
      dict <- withReprDict param_type return
      let binder = setPatMDmd (Dmd ManyUnsafe spc) $
                   localVarP tmpvar param_type dict
          initializer = ExpM $ AppE defaultExpInfo arg_expr []
                        [ExpM $ VarE defaultExpInfo tmpvar]
          binding = contextItem $ LetCtx inf binder initializer

      -- Copy the value to its destination.  The copy should be
      -- eliminated by DCE later.
      let copy = ExpM $ VarE defaultExpInfo (pyonBuiltin the_copy)
          tmpvar_exp = ExpM $ VarE inf tmpvar
          use = ExpM $ AppE defaultExpInfo copy [TypM param_type] [dict, tmpvar_exp]
      return (use, binding : subcontext)

floatInExp :: ExpM -> Flt ExpM
floatInExp = floatInExpDmd unknownDmd

-- | Perform floating on an expression in the RHS of a let statement.
--
--   The locally floated bindings are returned, and should be
--   placed outside the let:
--
--   > let FLOATED_BINDINGS
--   > in let ORIGINAL_BINDING
--   >    in ORIGINAL_BODY
floatInExpRhs :: Dmd -> ExpM -> Flt (ExpM, Context)
floatInExpRhs dmd expressionM@(ExpM expression) =
  case expression
  of AppE {} -> floatInApp True dmd expressionM
     _ -> do e <- floatInExpDmd dmd expressionM
             return (e, [])

-- | Perform floating on an expression whose result is demanded in a known way.
--
--   Demand information is taken from variable bindings.  It is produced by
--   demand analysis.
floatInExpDmd :: Dmd -> ExpM -> Flt ExpM
floatInExpDmd dmd (ExpM expression) =
  case expression
  of VarE {} -> return $ ExpM expression
     LitE {} -> return $ ExpM expression
     AppE {} -> do
       (new_expression, ctx) <- floatInApp False dmd (ExpM expression)
       return $ applyContext ctx new_expression
     LamE inf f -> do
       f' <- floatInFun (LocalAnchor []) f
       return $ ExpM $ LamE inf f'
     
     -- Special case: let x = lambda (...) becomes a letfun
     LetE inf pat@(MemVarP {}) (ExpM (LamE _ f)) body ->
       floatInExp $ ExpM $ LetfunE inf (NonRec (Def (patMVar' pat) f)) body

     LetE inf pat rhs body ->
       floatInLet dmd inf pat rhs body

     LetfunE inf defs body ->
       floatInLetfun dmd inf defs body

     CaseE inf scr alts ->
       floatInCase dmd inf scr alts

floatInApp :: Bool -> Dmd -> ExpM -> Flt (ExpM, Context)
floatInApp float_initializers dmd expression = do
  -- Flatten the expression and catch any floated bindings that depend on
  -- local variables
  ((new_expression, local_context), dependent_context, rn) <-
    grabContext flatten_expression 
  
  -- Put the dependent context inside the local context
  let context = dependent_context ++ local_context
  return (rename rn new_expression, context)
  where 
    flatten_expression = do
      -- Flatten the expression
      result@(_, local_context) <-
        flattenApp float_initializers (specificity dmd) expression
    
      -- Find the new variable bindings that were created
      let local_defs = IntSet.fromList $ map (fromIdent . varID) $
                       concatMap ctxDefs local_context
    
      -- Any floated bindings that mention these variables should be caught
      let check c = or [fromIdent (varID v) `IntSet.member` local_defs
                       | v <- Set.toList $ ctxUses c]

      return (result, check)

floatInLet dmd inf pat rhs body =
  case pat
  of MemVarP pat_var pat_type pat_dmd -> do
       -- Float the RHS
       (rhs', rhs_context) <- floatInExpRhs pat_dmd rhs
       if isFloatableSingletonParamType pat_type
         then do
           -- Float this binding.  Since the binding may be combined with
           -- other bindings, set the uses to 'many'.
           rn <- floatAndRename $ LetCtx inf (setPatMUses Many pat) $
                 applyContext rhs_context rhs'

           -- Rename and continue processing the body
           addRnPatternVar rn pat $ floatInExpDmd dmd $ rename rn body
         else unfloated_rhs rhs_context pat rhs'

     LocalVarP pat_var pat_type pat_dict pat_dmd -> do
       -- Float the dictionary argument
       pat_dict' <- floatInExp pat_dict
       let pat' = LocalVarP pat_var pat_type pat_dict' dmd
       (rhs', rhs_context) <- anchorOnVar' pat_var $ floatInExpRhs pat_dmd rhs
       unfloated_rhs rhs_context pat' rhs'

     MemWildP {} -> internalError "floatInLet"
  where
    -- The let-bound variable was not floated.  Process the body and rebuild
    -- a let expression.
    unfloated_rhs rhs_context new_pat new_rhs = do
      -- Float in the body of the let statement
      body' <- addPatternVar new_pat $
               anchorOnVar (patMVar' new_pat) $ floatInExpDmd dmd body

      -- Floated bindings from RHS are applied to the entire let-expression
      let new_expression = ExpM $ LetE inf new_pat new_rhs body'
      return $ applyContext rhs_context new_expression

floatInLetfun dmd inf defs body = do
  -- Float the contents of these functions.  If it's a recursive binding,
  -- don't float anything that mentions one of the local functions.
  defs' <-
    case defs
    of NonRec {} -> traverse (float_function_body []) defs
       Rec {}    -> traverse (float_function_body def_vars) defs

  -- Float these functions
  rn <- floatAndRename (LetfunCtx inf defs')
  
  -- Float the body
  floatInExpDmd dmd $ rename rn body
  where
    def_vars = [v | Def v _ <- defGroupMembers defs]
    
    -- Perform floating in the function body
    float_function_body local_vars (Def v f) = do
      f' <- floatInFun (LocalAnchor local_vars) f
      return (Def v f')

floatInCase dmd inf scr alts = do
  scr' <- floatInExp scr
  floatable <- is_floatable scr'
  if floatable
    then do rn <- floatAndRename ctx
            -- The floated variables were renamed. 
            -- Add the /renamed/ pattern variables to the environment.
            addRnPatternVars rn alt_params $ floatInExpDmd dmd $ rename rn alt_body
    else do alts' <- mapM floatInAlt alts
            return $ ExpM $ CaseE inf scr' alts'
  where
    AltM (Alt con alt_targs alt_tparams alt_params alt_body) = head alts
    ctx = CaseCtx inf scr con alt_targs alt_tparams alt_params
    
    is_floatable scr'
      | length alts /= 1 =
          return False  -- Don't float a case with multiple alternatives 
      | isFloatableCaseDataCon con =
          return True   -- Float if this is a desirable type to float 
      | ExpM (VarE _ scr_var) <- scr' =
          -- Float if scrutinee is a readable reference
          isReadReference scr_var
      | otherwise =
          return False

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
    (dict_env, int_env) <- runFreshVarM id_supply createDictEnv
    let flt_env = FloatCtx {fcVarSupply = id_supply,
                            fcTypeEnv = tenv,
                            fcDictEnv = dict_env,
                            fcIntEnv = int_env,
                            fcReadVars = IntSet.empty}
    defss' <- runTopLevelFlt float_defss flt_env
    (unzip -> (export_defs, exports')) <-
      runTopLevelFlt float_exports flt_env
    return $ Module mod_name (concat $ defss' ++ export_defs) exports'
  where
    float_defss = mapM floatInTopLevelDefGroup defss
    float_exports = mapM floatInExport exports
    
    