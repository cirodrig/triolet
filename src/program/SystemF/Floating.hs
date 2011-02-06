{-| Selective floating-out of let and case statements.

Some code is aggressively moved upward as far as possible
to increase opportunities for other optimizations.  We float definitions of
singleton values, case-of-dictionary expressions, and case-of-read-variable 
expressions this way.
-}

{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
module SystemF.Floating
       (Context,
        ContextItem, contextItem,
        ContextExp(..),
        applyContext,
        floatModule)
where

import Prelude hiding(mapM)
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

-- | Is this a singleton type?
isSingletonType :: Type -> Bool
isSingletonType ty =
  case fromVarApp ty
  of Just (op, _) -> isSingletonCon op
     _ -> False

-- | Return true if this is the type of a floatable let-binding parameter.
--   The type must be a singleton type, and it must be in the type's natural
--   representation.
isFloatableParamType :: ParamType -> Bool
isFloatableParamType (prepr ::: ptype) =
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

-- | Get the variables defined by the context
ctxDefs :: ContextItem -> [Var]
ctxDefs item =
  case ctxExp item
  of LetCtx _ pat _ -> [patMVar' pat]
     CaseCtx _ _ _ _ ty_params params ->
       [v | TyPatM v _ <- ty_params] ++ mapMaybe patMVar params

-- | Extract the part of the context that depends on the given variables.
--   The context is partitioned into two contexts, of which the first is
--   dependent on and the second is independent of the given variables.
splitContext :: [Var] -> Context -> (Context, Context)
splitContext vars ctx =
  -- Start processing from the outermost context and work inwards
  split (Set.fromList vars) [] [] (reverse ctx)
  where
    split varset dep indep (c:ctx)
      | not $ Set.null $ ctxUses c `Set.intersection` varset =
          -- This element of the context is dependent.
          -- Anything dependent on this element must be added to the 
          -- dependent set.
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
         of LetCtx _ (MemVarP pvar param_type@(_ ::: ptype)) rhs
              | isFloatableParamType param_type -> do
                  -- This context can be eliminated
                  -- Is there already a definition of this variable?
                  defined_var <- findByType id_supply tenv ptype types
                  case defined_var of
                    Just v -> eliminate_item pvar v
                    Nothing ->
                      -- Not eliminated; add to context
                      let types' = (ptype, pvar) : types
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
  in applyContext ctx $! apply_c

applyContext [] e = e

-------------------------------------------------------------------------------

data FloatCtx = 
  FloatCtx { fcVarSupply :: {-# UNPACK #-}!(IdentSupply Var)
             -- | The global type environment.  Local types are not added to
             --   the environment.
           , fcTypeEnv :: !TypeEnv
             -- | IDs of readable reference variables that are not in
             -- @fcTypeEnv@.
           , fcReadVars :: IntSet.IntSet 
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

-- | Put floated bindings here, if they depend on the specified variables
anchor :: [Var] -> Flt ExpM -> Flt ExpM
anchor vs m = Flt $ \ctx -> do
  (exp, context) <- runFlt m ctx
  
  -- Find dependent bindings
  let (dep, indep) = splitContext vs context
      
  -- Remove redundant bindings
  (dep', rn) <- fltNubContext ctx dep
  let new_exp = applyContext dep' (rename rn exp)

  return (new_exp, indep)

-- | Put all floated bindings here
anchorAll :: Flt ExpM -> Flt ExpM
anchorAll m = Flt $ \ctx -> do
  (exp, context) <- runFlt m ctx
  
  -- Remove redundant bindings
  (context', rn) <- fltNubContext ctx context
  let new_exp = applyContext context' (rename rn exp)
  return (new_exp, [])

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
  in runFlt m ctx

-- | If the pattern binds a readable variable, indicate that the variable is
--   a readable reference.  The pattern's type is ignored.
--
--   A @LocalVarP@ is counted as a readable reference.
--   It's only a readable reference in the body of a let-binding, not the rhs.
addPatternVar :: PatM -> Flt ExpM -> Flt ExpM
addPatternVar (MemVarP v (ReadPT ::: _)) = addReadVar v
addPatternVar (MemVarP v _)              = id
addPatternVar (LocalVarP v _ _)          = addReadVar v
addPatternVar (MemWildP _)               = id

addPatternVars ps x = foldr addPatternVar x ps

fltNubContext :: FloatCtx -> Context -> IO (Context, Renaming)
fltNubContext ctx context =
  nubContext (fcVarSupply ctx) (fcTypeEnv ctx) context

-------------------------------------------------------------------------------

floatInExp :: ExpM -> Flt ExpM
floatInExp (ExpM expression) =
  case expression
  of VarE {} -> return $ ExpM expression
     LitE {} -> return $ ExpM expression
     AppE inf (ExpM (VarE _ op_var)) ty_args args
       | isDictionaryDataCon op_var -> do
           -- Float out this dictionary constructor.
           -- Bind the dictionary value to a new variable.
           floatDictionary inf expression op_var ty_args args
     AppE inf op ty_args args -> do
       op' <- floatInExp op
       -- ty_args don't contain anything floatable
       args' <- mapM floatInExp args
       return $ ExpM $ AppE inf op' ty_args args'
     LamE inf f -> do
       f' <- floatInFun (Just []) f
       return $ ExpM $ LamE inf f'
     
     -- Special case: let x = lambda (...) becomes a letrec
     LetE inf (MemVarP v _) (ExpM (LamE _ f)) body ->
       floatInExp $ ExpM $ LetrecE inf (NonRec (Def v f)) body

     LetE inf pat rhs body ->
       floatInLet inf pat rhs body

     LetrecE inf defs body ->
       floatInLetrec inf defs body

     CaseE inf scr alts ->
       floatInCase inf scr alts
  
floatInLet inf pat rhs body =
  case pat
  of MemVarP pat_var pat_type
       | isFloatableParamType pat_type -> do
           -- Float this binding
           rn <- float $ LetCtx inf pat rhs

           -- Rename and continue processing the body
           addPatternVar pat $ floatInExp $ rename rn body
       | otherwise -> do
           rhs' <- floatInExp rhs
           body' <- addPatternVar pat $ anchor [pat_var] $ floatInExp body
           return $ ExpM $ LetE inf pat rhs' body'

     LocalVarP pat_var pat_type pat_dict -> do
       pat_dict' <- floatInExp pat_dict
       rhs' <- anchor [pat_var] $ floatInExp rhs
       body' <- addPatternVar pat $ anchor [pat_var] $ floatInExp body
       return $ ExpM $ LetE inf (LocalVarP pat_var pat_type pat_dict') rhs' body'

     MemWildP {} -> internalError "floatInLet"

floatInLetrec inf defs body = do
  defs' <- float_defs
  body' <- anchor def_vars $ floatInExp body
  return $ ExpM $ LetrecE inf defs' body'
  where
    def_vars = [v | Def v _ <- defGroupMembers defs]
    float_defs =
      case defs
      of NonRec (Def v f) -> do
           f' <- floatInFun (Just []) f
           return $ NonRec (Def v f')
         Rec defs -> liftM Rec $ forM defs $ \(Def v f) -> do
           -- Don't float anything that mentions one of the local functions
           f' <- floatInFun (Just def_vars) f
           return $ Def v f'
    
floatInCase inf scr alts = do
  scr' <- floatInExp scr
  floatable <- is_floatable scr'
  if floatable
    then do rn <- float ctx
            addPatternVars alt_params $ floatInExp $ rename rn alt_body
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
floatDictionary inf dict_expr op_var ty_args args = do
  -- Compute the type of the dictionary
  tenv <- getTypeEnv
  let dict_repr ::: dict_type = dictionary_type tenv
  
  -- Create the binding that will be floated
  dict_var <- newAnonymousVar ObjectLevel
  let dict_param_type = returnReprToParamRepr dict_repr ::: dict_type
      ctx = LetCtx inf (MemVarP dict_var dict_param_type) $ ExpM dict_expr
      
  -- Return the variable
  rn <- float ctx
  return $ ExpM $ VarE inf (rename rn dict_var)
  where
    dictionary_type tenv =
      case lookupDataCon op_var tenv
      of Just dc_type ->
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
         Nothing -> internalError "floatDictionary"

floatInAlt :: AltM -> Flt AltM
floatInAlt (AltM alt) = do
  body' <- addPatternVars (altParams alt) $
           anchor local_vars $
           floatInExp (altBody alt)
  return $ AltM $ alt {altBody = body'}
  where
    local_vars =
      [v | TyPatM v _ <- altExTypes alt] ++ mapMaybe patMVar (altParams alt)

-- | Perform floating on a function.
--
--   If a Just value, @m_local_vars@ is the set of variables whose definitions 
--   should not be floated out of the function.  If Nothing, then no bindings
--   will be floated out.  The function's parameters will not be floated out
--   regardless of the value given.
floatInFun :: Maybe [Var] -> FunM -> Flt FunM
floatInFun m_local_vars (FunM fun) = do
  body <- addPatternVars (funParams fun) $ anchor_local_vars $
          floatInExp (funBody fun)
  return $ FunM $ fun {funBody = body}
  where
    anchor_local_vars m =
      case m_local_vars
      of Nothing -> anchorAll m
         Just extra_local_vars -> anchor (param_vars ++ extra_local_vars) m

    param_vars = [v | TyPatM v _ <- funTyParams fun] ++
                 mapMaybe patMVar (funParams fun)

-- | Perform floating on a top-level function definition.
--   No bindings are floated out of the function.
floatInTopLevelDef :: Def Mem -> Flt (Def Mem)
floatInTopLevelDef (Def v f) = do
  f' <- floatInFun Nothing f
  return (Def v f')

floatInExport :: Export Mem -> Flt (Export Mem)
floatInExport exp = do
  f' <- floatInFun Nothing $ exportFunction exp
  return $ exp {exportFunction = f'}

floatModule :: Module Mem -> IO (Module Mem)
floatModule (Module mod_name defss exports) =
  withTheNewVarIdentSupply $ \id_supply -> do
    tenv <- readInitGlobalVarIO the_memTypes
    let flt_env = FloatCtx {fcVarSupply = id_supply,
                            fcTypeEnv = tenv,
                            fcReadVars = IntSet.empty}
    defss' <- runTopLevelFlt float_defss flt_env
    exports' <- runTopLevelFlt float_exports flt_env
    return $ Module mod_name defss' exports'
  where
    float_defss = mapM (mapM floatInTopLevelDef) defss
    float_exports = mapM floatInExport exports
    
    