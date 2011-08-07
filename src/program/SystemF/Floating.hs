{-| Selective floating-out of let and case statements.

Some code is aggressively moved upward as far as possible
to increase opportunities for other optimizations.  We float definitions of
singleton values, case-of-dictionary expressions, and case-of-read-variable 
expressions this way.
-}

{-# LANGUAGE FlexibleInstances, FlexibleContexts, ViewPatterns #-}
module SystemF.Floating
       (Context,
        assumeContext,
        ContextItem,
        contextItem,
        contextItemUses,
        ContextExp(..),
        freshenContextExp,
        asCaseCtx,
        applyContext,
        applyContextWithType,
        splitContext,
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
import SystemF.TypecheckMem
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
  con `isPyonBuiltin` the_someIndInt

-- | Return True if the expression ends with an exception-raising statement 
--   and does not return normally.
isExceptingExp :: ExpM -> Bool
isExceptingExp (ExpM exp) =
  case exp
  of LetE _ _ _ body  -> isExceptingExp body
     LetfunE _ _ body -> isExceptingExp body
     CaseE _ scr alts -> all isExceptingAlt alts
     ExceptE {}       -> True
     _                -> False

isExceptingAlt :: AltM -> Bool
isExceptingAlt (AltM alt) =
  isExceptingExp $ altBody alt

-- | Set the return type of a case alternative.  The alternative must
--   satisfy the 'isExceptingAlt' predicate.
setExceptionReturnType :: Type -> AltM -> AltM
setExceptionReturnType rt (AltM alt) =
  AltM $ alt {altBody = set_exp_type $ altBody alt}
  where
    set_exp_type (ExpM expression) =
      ExpM $
      case expression
      of LetE inf pat rhs body -> LetE inf pat rhs $ set_exp_type body
         LetfunE inf defs body -> LetfunE inf defs $ set_exp_type body
         CaseE inf e alts -> CaseE inf e $ map (setExceptionReturnType rt) alts
         ExceptE inf _ -> ExceptE inf rt
         _ -> internalError "setExceptionReturnType: Unexpected expression"

-- | If the given application term is floatable, then determine its type
--   and return a binder for it.  Otherwise return Nothing.
floatableAppParamType :: TypeEnv -> Var -> [TypM] -> [ExpM] -> Flt (Maybe Type)
floatableAppParamType tenv op_var ty_args args
  | isDictionaryDataCon op_var = dictionary_binding
  | isReprCon op_var           = repr_binding
  | op_var `isPyonBuiltin` the_defineIntIndex &&
    length args == 1           = return $ Just intindex_binding
  | otherwise                  = return Nothing
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
      in do (_, _, rtype) <-
              instantiateDataConType dc_type inst_type_args inst_ex_args
            return $ Just rtype

    -- The parameter type for a floated Repr expression
    repr_binding = do
      app_type <- inferAppType op_type ty_args []
      return $ Just $ drop_arg_types (length args) app_type
      where
        drop_arg_types 0 t = t
        drop_arg_types n (FunT _ rt) = drop_arg_types (n - 1) rt

    intindex_binding =
      -- Return value has type SomeIndInt
      VarT (pyonBuiltin the_SomeIndInt)

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
       | op `isPyonBuiltin` the_convertToBoxed ||
         op `isPyonBuiltin` the_copy ||
         op `isPyonBuiltin` the_convertToBare -> True
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
      found <- runTypeEvalM (compareTypes ptype ty) id_supply tenv
      if found then return (Just val) else search assocs
    
    search [] = return Nothing

{-
-- | Compute the type of a type application.  We assume there's no 
--   type error in the application.
computeInstantiatedType :: Type -> [TypM] -> TypeEvalM Type
computeInstantiatedType op_type args = apply_types op_type args
  where
    apply_types op_type [] = return op_type
    apply_types op_type (arg:args) = do 
      app_type <- typeOfTypeApp op_type (typeKind arg) arg
      case app_type of
        Nothing -> bad_application
        Just t -> apply_types t args

    bad_application = internalError "Unexpected type error during floating"
-}

-- | How to float a parameter of a data constructor or function.
data FltParamType =
    -- | Do not float this parameter
    Don'tFloat
    -- | Float this parameter and assign its value to a local variable.
  | FloatParam !BaseKind Type Specificity

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
directStyleAppParameters :: TypeEnv
                         -> DataConType
                         -> [TypM]
                         -> [Maybe Specificity]
                         -> Flt [FltParamType]
directStyleAppParameters tenv dcon_type ty_args spcs
  | length ty_args /= length (dataConPatternParams dcon_type) +
                      length (dataConPatternExTypes dcon_type) =
      internalError "directStyleAppParameters: Wrong number of type arguments"
  | otherwise = do
      let types = map fromTypM ty_args
      (field_types, _) <-
        instantiateDataConTypeWithExistentials dcon_type types
      return $ selectFloatableParameters tenv float don't_float field_types spcs
  where
    float kind ty spc = FloatParam kind ty spc
    don't_float = Don'tFloat

directStyleAppParameters' tenv dcon_type ty_args spcs
  | length ty_args /= length (dataConPatternParams dcon_type) +
                      length (dataConPatternExTypes dcon_type) =
      internalError "directStyleAppParameters': Wrong number of type arguments"
  | otherwise =
      let -- Add type parameters to the environment so that we can compute
          -- kinds 
          local_tenv = foldr insert_type tenv type_params
            where
              type_params = dataConPatternParams dcon_type ++ 
                            dataConPatternExTypes dcon_type
              insert_type (v ::: t) type_env = insertType v t type_env

          field_types = dataConPatternArgs dcon_type
      in selectFloatableParameters local_tenv float don't_float field_types spcs
  where
    float _ _ _ = True
    don't_float = False

-- | Given types and specificities of data constructor fields, determine which
--   parameters should be floated.
selectFloatableParameters :: TypeEnv
                          -> (BaseKind -> Type -> Specificity -> a)
                          -> a
                          -> [Type]
                          -> [Maybe Specificity]
                          -> [a]
selectFloatableParameters tenv float don't_float field_types field_specificities =
  zipWith floatable field_types field_specificities
  where
    -- Value and boxed operands are floatable.
    -- Read operands may be floated, depending on how they are demanded.
    floatable ty spc =
      case kind
      of ValK  -> float kind ty (fromMaybe Used spc)
         BoxK  -> float kind ty (fromMaybe Used spc)
         BareK -> don't_float {-case spc
                  of Nothing     -> Don'tFloat
                     Just Unused -> Don'tFloat
                     Just s      -> FloatParam BareK ty s-}
      where
        kind = toBaseKind (typeKind tenv ty)

-- | Given a variable that may be a data constructor, get its type 
--   and the specificities of its fields.
--   Helper function for 'floatedParameters'.
extractDataConTypeAndSpecificity :: TypeEnv -> Var -> Specificity
                                 -> Maybe (DataConType, [Maybe Specificity])
extractDataConTypeAndSpecificity tenv op_var spc =
  case lookupDataCon op_var tenv
  of Just dcon_type ->
       let specificities =
             case spc
             of Decond (MonoCon con _ _) spcs
                  | con /= op_var ->
                      internalError "floatedParameters: Invalid demand"
                  | otherwise ->
                      map Just spcs ++ repeat Nothing
                Decond _ _ -> 
                  internalError "floatedParameters: Invalid demand"
                _ -> repeat Nothing
       in Just (dcon_type, specificities)
     Nothing -> Nothing

-- | Based on the operator variable, pick which arguments should be floated.
floatedParameters :: TypeEnv -> Specificity -> Var -> [TypM] -> Flt [FltParamType]
floatedParameters tenv spc op_var ty_args =
  case extractDataConTypeAndSpecificity tenv op_var spc
  of Just (dcon_type, field_spcs) -> do
       direct_params <-
         directStyleAppParameters tenv dcon_type ty_args field_spcs 
       return (direct_params ++ repeat Don'tFloat)
     Nothing
       | op_var `isPyonBuiltin` the_copy ->
           -- Move the source argument of 'copy' to increase the success rate
           -- of copy elimination
           let [TypM store_type] = ty_args
           in return [Don'tFloat,
                      FloatParam BareK store_type Used,
                      Don'tFloat]
       | otherwise ->
           return $ repeat Don'tFloat

-- | Determine which parameters should be floated.  Return True if the
--   parameter should be floated, False otherwise.  For parameters where it's
--   unknown, False is returned.
floatedParameters' :: TypeEnv -> Var -> [TypM] -> [Bool]
floatedParameters' tenv op_var ty_args =
  case extractDataConTypeAndSpecificity tenv op_var Used
  of Just (dcon_type, field_spcs) ->
       directStyleAppParameters' tenv dcon_type ty_args field_spcs ++
       repeat False
     Nothing
       | op_var `isPyonBuiltin` the_copy ->
           -- Move the source argument of 'copy' to increase the success rate
           -- of copy elimination
           [False, True, False]
       | otherwise -> repeat False

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

-- | Get the set of variables that are used by the context item and not
--   defined by it.
contextItemUses :: ContextItem -> Set.Set Var
contextItemUses = ctxUses

-- | Make a 'ContextItem'.
contextItem :: ContextExp -> ContextItem
contextItem e = ContextItem (freeVariablesContextExp e) e
  where
    freeVariablesContextExp (LetCtx _ pat rhs) =
      freeVariables (patMType pat) `Set.union` freeVariables rhs

    freeVariablesContextExp (CaseCtx _ scrutinee (MonoCon _ ty_args ty_pats) pats exc_alts) =
      let scr_fv = freeVariables scrutinee
          ty_fv = Set.unions $ map freeVariables ty_args
          typat_fv = Set.unions $ map (freeVariables . binderType) ty_pats
          
          -- Get free variables from patterns; remove existential variables
          pat_fv1 = Set.unions $ map (freeVariables . patMType) pats
          pat_fv = foldr Set.delete pat_fv1 (map binderVar ty_pats)
          
          alts_fv = freeVariables exc_alts
      in Set.unions [scr_fv, ty_fv, typat_fv, pat_fv, alts_fv]
   
    freeVariablesContextExp (CaseCtx _ scrutinee (MonoTuple ty_args) pats exc_alts) =
      let scr_fv = freeVariables scrutinee
          ty_fv = Set.unions $ map freeVariables ty_args
          
          -- Get free variables from patterns
          pat_fv = Set.unions $ map (freeVariables . patMType) pats
          
          alts_fv = freeVariables exc_alts
      in Set.unions [scr_fv, ty_fv, pat_fv, alts_fv]

    freeVariablesContextExp (LetfunCtx _ defgroup) =
      case defgroup
      of NonRec def -> freeVariables $ definiens def
         Rec defs ->
           let functions_fv =
                 Set.unions $ map (freeVariables . definiens) defs
               local_variables = map definiendum defs
           in foldr Set.delete functions_fv local_variables

-- | An expression sans body that can be floated outward.
data ContextExp =
    -- | A let expression that doesn't allocate local memory (not @LocalVarP@).
    --
    --   @let <pattern> = <rhs> in (...)@
    LetCtx ExpInfo PatM ExpM
    -- | A case expression.  The case expression has a single
    --   alternative that can return normally, and possibly other
    --   alternatives that raise exceptions instead of returning.
    --   The normal alternative's fields are included except for the
    --   alternative body, which is not part of the context.
    --
    --   @case <scrutinee> 
    --    of { <alternative>. (...); <excepting alternatives>}@
  | CaseCtx ExpInfo ExpM !MonoCon [PatM] [AltM]
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
       renamePatM rn pat $ \rn' pat' -> LetCtx inf pat' (rename rn' body)
     CaseCtx inf scr (MonoCon con ty_args ty_params) params exc_alts ->
       let scr' = rename rn scr
           ty_args' = rename rn ty_args
       in renameBindings rn ty_params $ \rn1 ty_params' ->
          renamePatMs rn1 params $ \rn2 params' ->
          let mono_con = MonoCon con ty_args' ty_params'
          in CaseCtx inf scr' mono_con params' (map (rename rn2) exc_alts)
     CaseCtx inf scr (MonoTuple ty_args) params exc_alts ->
       let scr' = rename rn scr
           ty_args' = rename rn ty_args
       in renamePatMs rn params $ \rn1 params' ->
          let mono_con = MonoTuple ty_args'
          in CaseCtx inf scr' mono_con params' (map (rename rn1) exc_alts)
     LetfunCtx inf defs ->
       renameDefGroup rn defs $ \_ defs' -> LetfunCtx inf defs'

freshenContextExp :: (Monad m, Supplies m VarID) =>
                     ContextExp -> m (ContextExp, Renaming)
freshenContextExp (LetCtx inf pat body) = do
  (pat', rn) <- freshenPatM (const $ return True) pat
  return (LetCtx inf pat' (rename rn body), rn)

freshenContextExp (CaseCtx inf scr (MonoCon alt_con ty_args ty_params) params exc_alts) = do
  (ty_params', ty_renaming) <- freshenTyPatMs (const $ return True) (map TyPatM ty_params)
  renamePatMs ty_renaming params $ \ty_renaming2 params' -> do
    (params'', param_renaming) <- freshenPatMs (const $ return True) params'
    let rn = param_renaming `mappend` ty_renaming
    exc_alts' <- freshen (const $ return True) $ rename rn exc_alts
    let mono_con = MonoCon alt_con ty_args [b | TyPatM b <- ty_params']
    return (CaseCtx inf scr mono_con params'' exc_alts', rn)

freshenContextExp (CaseCtx inf scr mono_con@(MonoTuple _) params exc_alts) = do
  (params', param_renaming) <- freshenPatMs (const $ return True) params
  exc_alts' <- freshen (const $ return True) $ rename param_renaming exc_alts
  return (CaseCtx inf scr mono_con params' exc_alts', param_renaming)

freshenContextExp (LetfunCtx inf defs) =
  case defs
  of NonRec def -> do
       -- Don't need to rename inside the definition
       let v = definiendum def
       v' <- newClonedVar v
       let new_defs = NonRec (def {definiendum = v'})
       return (LetfunCtx inf new_defs, singletonRenaming v v')
     Rec defs -> do
       -- Rename bodies of all local functions
       let local_vars = map definiendum defs
       new_vars <- mapM newClonedVar local_vars
       let rn = renaming $ zip local_vars new_vars
           new_defs = [def {definiendum = new_var,
                            definiens = rename rn $ definiens def}
                      | (new_var, def) <- zip new_vars defs]
       return (LetfunCtx inf (Rec new_defs), rn)

-- | Get the variables defined by the context
ctxDefs :: ContextItem -> [Var]
ctxDefs item =
  case ctxExp item
  of LetCtx _ pat _ -> [patMVar pat]
     CaseCtx _ _ (MonoCon _ _ ty_params) params _ ->
       map binderVar ty_params ++ map patMVar params
     CaseCtx _ _ (MonoTuple _) params _ ->
       map patMVar params
     LetfunCtx _ defs -> map definiendum $ defGroupMembers defs

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
         of LetCtx _ pat rhs
              | isSingletonType (patMType pat) -> do
                  -- This context can be eliminated
                  -- Is there already a definition of this variable?
                  defined_var <- findByType id_supply tenv (patMType pat) types
                  case defined_var of
                    Just v -> eliminate_item (patMVar pat) v
                    Nothing ->
                      -- Not eliminated; add to context
                      let types' = (patMType pat, patMVar pat) : types
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

-- | Apply a context to an expression to produce a new expression.
--   If the context could contain a case statement with excepting branches,
--   then the expression's return type must be passed as an argument.
applyContextRT :: Maybe Type -> Context -> ExpM -> ExpM
applyContextRT m_return_type (c:ctx) e =
  let return_type =
        -- Get the return type.  It's only needed for excepting alternatives 
        -- in case statements.
        case m_return_type
        of Nothing ->
             internalError "applyContext: Need return type for floated case statement"
           Just rt -> rt

      apply_c =
        case ctxExp c
        of LetCtx inf pat rhs -> ExpM $ LetE inf pat rhs e
           CaseCtx inf scr mono_con params exc_alts ->
             let alts = altFromMonoCon mono_con params e :
                        map (setExceptionReturnType return_type) exc_alts
             in ExpM $ CaseE inf scr alts
           LetfunCtx inf defs ->
             ExpM $ LetfunE inf defs e
  in applyContextRT m_return_type ctx $! apply_c

applyContextRT _ [] e = e

applyContext = applyContextRT Nothing

applyContextWithType t = applyContextRT (Just t)

-- | Extend the environment with types and dictionary assignments from 
--   variables bound in a context.
--
--   Note that, since the head of the list is innermost, we use a left fold.
assumeContext :: (EvalMonad m, ReprDictMonad m) => Context -> m a -> m a
assumeContext ctx m = foldl (flip assumeContextItem) m ctx

-- | Extend the environment with types and dictionary assignments from
--   variables bound in a context item.
assumeContextItem :: (EvalMonad m, ReprDictMonad m) =>
                     ContextItem -> m a -> m a
assumeContextItem ci m =
  case ctxExp ci
  of LetCtx _ pat _ -> addPatternVar pat m
     CaseCtx _ _ (MonoCon _ _ ex_types) fields _ ->
       assumeBinders ex_types $ addPatternVars fields m
     CaseCtx _ _ (MonoTuple _) fields _ ->
       addPatternVars fields m
     LetfunCtx _ grp ->
       let function_types = [(definiendum def, functionType (definiens def))
                            | def <- defGroupMembers grp]
       in foldr (uncurry assume) m function_types

-------------------------------------------------------------------------------
-- The floating monad

data FloatCtx = 
  FloatCtx { fcVarSupply :: {-# UNPACK #-}!(IdentSupply Var)
             -- | The type environment
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

traceFlt d (Flt f) = Flt (\ctx -> traceShow d (f ctx))

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

instance TypeEnvMonad Flt where
  getTypeEnv = Flt $ \ctx -> return (fcTypeEnv ctx, [])
  assume v ty m = Flt $ \ctx ->
    let ctx' = ctx {fcTypeEnv = insertType v ty $ fcTypeEnv ctx}
    in runFlt m ctx'

instance EvalMonad Flt where
  liftTypeEvalM m = Flt $ \ctx -> do
    x <- runTypeEvalM m (fcVarSupply ctx) (fcTypeEnv ctx)
    return (x, [])

instance ReprDictMonad Flt where
  getVarIDs = Flt $ \ctx -> return (fcVarSupply ctx, [])
  getDictEnv = Flt $ \ctx -> return (fcDictEnv ctx, [])
  getIntIndexEnv = Flt $ \ctx -> return (fcIntEnv ctx, [])
  localDictEnv f m = Flt $ \ctx ->
    let ctx' = ctx {fcDictEnv = f $ fcDictEnv ctx}
    in runFlt m ctx'
  localIntIndexEnv f m = Flt $ \ctx ->
    let ctx' = ctx {fcIntEnv = f $ fcIntEnv ctx}
    in runFlt m ctx'

-- | Add a variable from a type pattern to the type environment
assumeTyPatM :: (EvalMonad m, ReprDictMonad m) => TyPatM -> m a -> m a
assumeTyPatM (TyPatM binder) m = assumeBinder binder m

assumeTyParams ty_params m = foldr assumeTyPatM m ty_params

-- | Add a definition group to the type environment,
--   after renaming the function names.
--
--   It's not necessary to rename the function types.
assumeRnDefGroup :: Renaming -> DefGroup (Def Mem) -> Flt a -> Flt a
assumeRnDefGroup rn defgroup m =
  let function_types = [(rename rn $ definiendum def,
                         functionType (definiens def))
                       | def <- defGroupMembers defgroup]
  in foldr (uncurry assume) m function_types
     
-- | Float a binding, when the bound variable is a fresh variable.
--   This should not be used to float preexisting bindings; use
--   'floatAndRename' for that.
float :: ContextExp -> Flt ()
float ctx_exp = Flt $ \_ -> return ((), [contextItem ctx_exp])

-- | Float a binding.  The binding will be renamed.
--   The renamed context will be returned along with the renaming that
--   was performed.  In the caller, the returned renaming should be applied 
--   to any expression where the binding is in scope.
floatAndRename :: ContextExp -> Flt (Context, Renaming)
floatAndRename ctx_exp = do
  -- Rename floated variables to avoid name conflicts
  (ctx_exp', rn) <- freshenContextExp ctx_exp
  let ctx = [contextItem ctx_exp']

  -- Float this binding
  Flt $ \_ -> return ((ctx, rn), ctx)

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
anchor :: (ContextItem -> Bool) -> Flt (ExpM, Type) -> Flt (ExpM, Type)
anchor predicate m = do
  (x, rt, _) <- anchor' predicate (do {(x, rt) <- m; return (x, rt, ())})
  return (x, rt)

anchor' :: (ContextItem -> Bool) -> Flt (ExpM, Type, a) -> Flt (ExpM, Type, a)
anchor' predicate m = do
  ((exp, return_type, other_data), dep_context, rn) <- grabContext $ do
    x <- m
    return (x, predicate)

  return (applyContext dep_context (rename rn exp),
          rename rn return_type,
          other_data)

-- | Put floated bindings here, if they depend on the specified variable
anchorOnVar :: Var -> Flt (ExpM, Type) -> Flt (ExpM, Type)
anchorOnVar v m = addLocalVar v $ anchor check m
  where
    check c = v `Set.member` ctxUses c

anchorOnVar' :: Var -> Flt (ExpM, Type, a) -> Flt (ExpM, Type, a)
anchorOnVar' v m = addLocalVar v $ anchor' check m
  where
    check c = v `Set.member` ctxUses c

-- | Put floated bindings here, if they depend on the specified variables
anchorOnVars :: [Var] -> Flt (ExpM, Type) -> Flt (ExpM, Type)
anchorOnVars vs m = addLocalVars vs $ anchor check m
  where
    var_set = Set.fromList vs
    check c = ctxUses c `intersects` var_set

-- | Anchor bindings inside a top-level function.  Only function bindings
--   are permitted to float out.  Function bindings are floated only if they
--   do not depend on the given variables.
anchorOuterScope :: [Var] -> Flt (ExpM, Type) -> Flt (ExpM, Type)
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
  case lookupType v (fcTypeEnv ctx)
  of Just t ->
       let is_read = toBaseKind (typeKind (fcTypeEnv ctx) t) == BareK
       in return (is_read, [])
     _ -> internalError "isReadReference: No type for variable"

-- | Indicate that a variable is a readable reference
addReadVar :: Var -> Flt a -> Flt a
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

-- | Add a pattern variable to the type environment.
--   If the pattern binds a representation dictionary,
--   add the dictionary to the environment.
addPatternVar :: (EvalMonad m, ReprDictMonad m) => PatM -> m a -> m a
addPatternVar pat m =
  assumeBinder (patMBinder pat) $ saveReprDictPattern pat m

{-
-- | Rename the pattern and then add it to the environment.
--
--   The renaming is applied to the pattern-bound variables as well as the
--   pattern's types.
--
--   We use this when a binding is renamed and floated.
addRnPatternVar :: Renaming -> PatM -> Flt a -> Flt a
addRnPatternVar rn pat =
  let rn_pattern =
        case pat
        of MemVarP v ptype uses ->
             MemVarP (rename rn v) (renameBinding rn ptype) (rename rn uses)
           MemWildP ptype ->
             MemWildP (renameBinding rn ptype)

  in case rn_pattern
     of MemVarP v ptype uses ->
          assume v (patMType rn_pattern) .
          saveReprDictPattern rn_pattern
        MemWildP _ -> id-}

addPatternVars ps x = foldr addPatternVar x ps

-- addRnPatternVars rn ps x = foldr (addRnPatternVar rn) x ps

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
flattenApp :: Bool -> Specificity -> ExpM -> Flt (ExpM, Type, Context)
flattenApp float_initializers spc expression =
  case fromExpM expression
  of AppE inf (ExpM (VarE _ op_var)) ty_args args ->
       -- Convert this expression to direct style
       createFlattenedApp expression float_initializers spc inf op_var ty_args args

     AppE inf op ty_args args -> do
       -- Don't flatten this expresion.  Flatten subexpressions.
       (op', op_type, op_context) <- flattenApp False Used op
       (unzip3 -> (args', arg_types, arg_contexts)) <-
         mapM (flattenApp False Used) args
       let new_exp = ExpM $ AppE inf op' ty_args args'

       return_type <- inferAppType op_type ty_args arg_types

       return (new_exp, return_type, concat (op_context : arg_contexts))

     _ -> do
       -- Don't alter
       (new_exp, rt) <- floatInExp expression
       return (new_exp, rt, [])

createFlattenedApp expression float_initializers spc inf op_var ty_args args = do
  -- Determine which parameters should be moved
  tenv <- getTypeEnv
  let op_type = case lookupType op_var tenv
                of Nothing -> internalError "createFlattenedApp"
                   Just t -> t
  moved <- floatedParameters tenv spc op_var ty_args

  -- Flatten arguments
  (unzip3 -> (args', arg_types, concat -> arg_contexts)) <-
    zipWithM flatten_arg moved args
  
  -- Create the new expression
  let new_expr = ExpM $ AppE inf (ExpM $ VarE inf op_var) ty_args args'
  return_type <- inferAppType op_type ty_args arg_types

  -- If this is a floatable expression, then float it and substitute a variable
  -- in its place.  Otherwise return it.
  floated_expr_type <- floatableAppParamType tenv op_var ty_args args'
  floated_expr <- 
    case floated_expr_type
    of Just ptype -> do
         floated_var <- newAnonymousVar ObjectLevel
         float (LetCtx inf (patM (floated_var ::: ptype)) new_expr)
         return (ExpM $ VarE inf floated_var)
       Nothing ->
         return new_expr

  return (floated_expr, return_type, arg_contexts)
  where
    flatten_arg :: FltParamType -> ExpM -> Flt (ExpM, Type, Context)
    flatten_arg Don'tFloat arg =
      -- This argument stays in place
      flattenApp False Used arg

    -- Special case: lambda (...) becomes a letfun and gets floated
    flatten_arg (FloatParam _ _ _) arg@(ExpM (LamE lam_info f)) = do
      f' <- floatInFun (LocalAnchor []) f

      -- Bind the function to a new variable and float it outward
      tmpvar <- newAnonymousVar ObjectLevel
      let floated_ctx = LetfunCtx lam_info (NonRec (mkDef tmpvar f'))
      float floated_ctx
      
      -- Return the function variable
      return (ExpM $ VarE inf tmpvar, functionType f', [])

    flatten_arg (FloatParam base_kind ty spc) arg = do
      (arg_expr, return_type, subcontext) <- flattenApp False spc arg

      -- If this argument is trivial, leave it where it is.
      -- Otherwise, bind it to a new variable.
      if isTrivialExp arg_expr
         || (isDataMovementExp arg_expr && not float_initializers)
        then return (arg_expr, return_type, subcontext)
        else flatten_mem_arg return_type arg_expr subcontext ty spc

    flatten_mem_arg rtype arg_expr subcontext param_type spc = do
      tmpvar <- newAnonymousVar ObjectLevel
      let binder = setPatMDmd (Dmd ManyUnsafe spc) $
                   patM (tmpvar ::: param_type)
          binding = contextItem $ LetCtx inf binder arg_expr
      return (ExpM $ VarE inf tmpvar, rtype, binding : subcontext)

    {- Removed because we no longer allow local variable patterns

    flatten_local_arg rtype arg_expr subcontext param_type spc = do
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
      return (use, rtype, binding : subcontext)
      -}

floatInExp :: ExpM -> Flt (ExpM, Type)
floatInExp = floatInExpDmd unknownDmd

-- | Perform floating on an expression in the RHS of a let statement.
--
--   The locally floated bindings are returned, and should be
--   placed outside the let:
--
--   > let FLOATED_BINDINGS
--   > in let ORIGINAL_BINDING
--   >    in ORIGINAL_BODY
floatInExpRhs :: Dmd -> ExpM -> Flt (ExpM, Type, Context)
floatInExpRhs dmd expressionM@(ExpM expression) =
  case expression
  of AppE {} -> floatInApp True dmd expressionM
     _ -> do (e, rt) <- floatInExpDmd dmd expressionM
             return (e, rt, [])

-- | Perform floating on an expression whose result is demanded in a known way.
--   Returns the floated expression and its return type.  Both of these may
--   have some variables renamed.
--
--   This function calls itself recursively,
--   possibly after renaming subexpressions.  Renamed variables are added to
--   the environment.
--
--   Demand information is taken from variable bindings.  It is produced by
--   demand analysis.
floatInExpDmd :: Dmd -> ExpM -> Flt (ExpM, Type)
floatInExpDmd dmd (ExpM expression) =
  case expression
  of VarE {} -> unchanged
     LitE {} -> unchanged
     UTupleE inf args -> floatInTuple dmd inf args
     AppE {} -> do
       (new_expression, rt, ctx) <- floatInApp False dmd (ExpM expression)
       return (applyContext ctx new_expression, rt)
     LamE inf f -> do
       f' <- floatInFun (LocalAnchor []) f
       return (ExpM $ LamE inf f', functionType f')
     
     -- Special case: let x = lambda (...) becomes a letfun
     LetE inf pat (ExpM (LamE _ f)) body ->
       floatInExp $ ExpM $ LetfunE inf (NonRec (mkDef (patMVar pat) f)) body

     LetE inf pat rhs body ->
       floatInLet dmd inf pat rhs body

     LetfunE inf defs body ->
       floatInLetfun dmd inf defs body

     CaseE inf scr alts ->
       floatInCase dmd inf scr alts

     ExceptE {} -> unchanged
     
     CoerceE {} -> unchanged
  where
    unchanged = do
      ty <- inferExpType (ExpM expression)
      return (ExpM expression, ty)

floatInTuple dmd inf args = do
  -- Determine the demand on each argument
  let arg_demands =
        case specificity dmd
        of Decond (MonoTuple _) spcs -> [Dmd OnceSafe spc | spc <- spcs]
           _ -> repeat (Dmd OnceSafe Used)
  (unzip -> (args', arg_types)) <- zipWithM floatInExpDmd arg_demands args
  
  -- Determine tuple type
  tenv <- getTypeEnv
  let arg_kinds = map (toBaseKind . typeKind tenv) arg_types
      tuple_type = typeApp (UTupleT arg_kinds) arg_types
  return (ExpM $ UTupleE inf args', tuple_type)
  
floatInApp :: Bool -> Dmd -> ExpM -> Flt (ExpM, Type, Context)
floatInApp float_initializers dmd expression = do
  -- Flatten the expression and catch any floated bindings that depend on
  -- local variables
  ((new_expression, return_type, local_context), dependent_context, rn) <-
    grabContext flatten_expression
  
  -- Put the dependent context inside the local context
  let context = dependent_context ++ local_context
  return (rename rn new_expression, rename rn return_type, context)
  where 
    flatten_expression = do
      -- Flatten the expression
      result@(_, return_type, local_context) <-
        flattenApp float_initializers (specificity dmd) expression
    
      -- Find the new variable bindings that were created
      let local_defs = IntSet.fromList $ map (fromIdent . varID) $
                       concatMap ctxDefs local_context
    
      -- Any floated bindings that mention these variables should be caught
      let check c = or [fromIdent (varID v) `IntSet.member` local_defs
                       | v <- Set.toList $ ctxUses c]

      return (result, check)

floatInLet dmd inf pat rhs body = do
  -- Float the RHS
  (rhs', _, rhs_context) <- floatInExpRhs (patMDmd pat) rhs
  if isSingletonType (patMType pat)
    then do
      -- Float this binding.  Since the binding may be combined with
      -- other bindings, set the uses to 'many'.
      (rn_ctx, rn) <-
        floatAndRename $ LetCtx inf (setPatMUses Many pat) $
        applyContext rhs_context rhs'

      -- Rename and continue processing the body
      assumeContext rn_ctx $ floatInExpDmd dmd $ rename rn body
    else unfloated_rhs rhs_context pat rhs'
  where
    -- The let-bound variable was not floated.  Process the body and rebuild
    -- a let expression.
    unfloated_rhs rhs_context new_pat new_rhs = do
      -- Float in the body of the let statement
      (body', body_type) <-
        addPatternVar new_pat $
        anchorOnVar (patMVar new_pat) $ floatInExpDmd dmd body

      -- Floated bindings from RHS are applied to the entire let-expression
      let new_expression = ExpM $ LetE inf new_pat new_rhs body'
      return (applyContext rhs_context new_expression, body_type)

floatInLetfun dmd inf defs body = do
  -- Float the contents of these functions.  If it's a recursive binding,
  -- don't float anything that mentions one of the local functions.
  defs' <-
    case defs
    of NonRec {} -> traverse (float_function_body []) defs
       Rec {}    -> assumeRnDefGroup mempty defs $
                    traverse (float_function_body def_vars) defs

  -- Float these functions
  (rn_ctx, rn) <- floatAndRename (LetfunCtx inf defs')

  -- Float the body
  assumeContext rn_ctx $ floatInExpDmd dmd $ rename rn body
  where
    def_vars = map definiendum $ defGroupMembers defs
    
    -- Perform floating in the function body
    float_function_body local_vars def =
      mapMDefiniens (floatInFun (LocalAnchor local_vars)) def

floatInCase dmd inf scr alts = do
  (scr', _) <- floatInExp scr
  
  -- Decide whether it's possible to float the case expression
  case asCaseCtx (ExpM (CaseE inf scr' alts)) of
    Nothing -> not_floatable scr'
    Just ((CaseCtx _ _ (MonoTuple _) _ _), _) -> not_floatable scr'
    Just (ctx@(CaseCtx _ _ (MonoCon con _ alt_tparams) alt_params _), alt_body) -> do
      floatable <- is_floatable con scr'
      if not floatable then not_floatable scr'  else do
        (rn_ctx, rn) <- floatAndRename ctx
        assumeContext rn_ctx $ floatInExpDmd dmd $ rename rn alt_body
  where
    not_floatable scr' = do
      (alts', return_type : _) <- mapAndUnzipM floatInAlt alts
      return (ExpM $ CaseE inf scr' alts', return_type)
    
    is_floatable con scr'
      | isFloatableCaseDataCon con =
          return True   -- Float if this is a desirable type to float 
      | ExpM (VarE _ scr_var) <- scr' =
          -- Float if scrutinee is a readable reference
          isReadReference scr_var
      | otherwise =
          return False

-- | Decompose the expression into a case context and a body expression, if
--   the expression can be decomposed this way.  There must be exactly one
--   case alternative that does not always raise an exception.
asCaseCtx :: ExpM -> Maybe (ContextExp, ExpM)
asCaseCtx (ExpM (CaseE inf scr alts)) =
  let (exc_alts, normal_alts) = partition isExceptingAlt alts
  in case normal_alts
     of [alt] -> 
          let (mono_con, params, body) = altToMonoCon alt
              ctx = CaseCtx inf scr mono_con params exc_alts
          in Just (ctx, body)
        _ -> Nothing

asCaseCtx _ = Nothing

floatInAlt :: AltM -> Flt (AltM, Type)
floatInAlt (AltM alt) = do
  (body', body_type) <-
    assumeTyParams (getAltExTypes alt) $
    addPatternVars (altParams alt) $
    anchorOnVars local_vars $
    floatInExp (altBody alt)
  return (AltM $ alt {altBody = body'}, body_type)
  where
    local_vars =
      [v | TyPatM (v ::: _) <- getAltExTypes alt] ++
      map patMVar (altParams alt)

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
  (body, _) <- assumeTyParams (funTyParams fun) $
               addPatternVars (funParams fun) $
               anchor_local_vars $
               floatInExp (funBody fun)
  return $ FunM $ fun {funBody = body}
  where
    anchor_local_vars m =
      case m_local_vars
      of GlobalAnchor -> anchorOuterScope param_vars m
         LocalAnchor extra_local_vars ->
           anchorOnVars (param_vars ++ extra_local_vars) m

    param_vars = [v | TyPatM (v ::: _) <- funTyParams fun] ++
                 map patMVar (funParams fun)

-- | Perform floating on a top-level function definition.
--   No bindings are floated out of the function.
floatInTopLevelDef :: Def Mem -> Flt (Def Mem)
floatInTopLevelDef def = do
  f' <- floatInFun GlobalAnchor $ definiens def
  return $ def {definiens = f'}

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
       (defs', bindings) <-
         assumeRnDefGroup mempty defgroup $
         getFloatedBindings $ mapM floatInTopLevelDef defs
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

floatTopLevel (defs:defss) exports = do
  new_defs <- floatInTopLevelDefGroup defs
  (defss', exports') <- assume_new_defs new_defs $ floatTopLevel defss exports
  return (new_defs ++ defss', exports')
  where
    assume_new_defs new_defs m = foldr (assumeRnDefGroup mempty) m new_defs

floatTopLevel [] exports = do
  (unzip -> (export_defs, exports')) <- mapM floatInExport exports
  return (concat export_defs, exports')

floatModule :: Module Mem -> IO (Module Mem)
floatModule mod@(Module mod_name imports defss exports) =
  withTheNewVarIdentSupply $ \id_supply -> do
    tenv <- readInitGlobalVarIO the_memTypes
    (dict_env, int_env) <- runFreshVarM id_supply createDictEnv
    let flt_env = FloatCtx {fcVarSupply = id_supply,
                            fcTypeEnv = tenv,
                            fcDictEnv = dict_env,
                            fcIntEnv = int_env,
                            fcReadVars = IntSet.empty}
    (defss', exports') <- runTopLevelFlt (floatTopLevel defss exports) flt_env
    return $ Module mod_name imports defss' exports'

