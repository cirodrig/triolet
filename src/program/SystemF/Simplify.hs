{-| The simplifier.

The simplifier makes a forward sweep through a program, more or less in
execution order, and tries to statically evaluate what it can.

This sweep performs copy propagation, constant propagation,
beta reduction (includes inlining), case-of-known-value elimination,
and some local expression reordering.
-}

{-# LANGUAGE TypeSynonymInstances, FlexibleContexts, Rank2Types #-}
module SystemF.Simplify (rewriteLocalExpr,
                         rewriteWithGeneralRules,
                         rewriteWithParallelRules,
                         rewriteWithSequentialRules)
where

import Prelude hiding(mapM)
import Control.Monad hiding(mapM)
import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import qualified Data.IntMap as IntMap
import Data.List as List
import Data.Maybe
import Data.Monoid
import qualified Data.Set as Set
import Data.Traversable(mapM)
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Builtins.Builtins
import SystemF.Demand
import SystemF.EtaReduce
import SystemF.Floating
import SystemF.MemoryIR
import SystemF.Syntax
import SystemF.Rename
import SystemF.Rewrite
import SystemF.TypecheckMem
import SystemF.PrintMemoryIR
import SystemF.KnownValue

import Common.Error
import Common.Identifier
import Common.Supply
import qualified SystemF.DictEnv as DictEnv
import SystemF.ReprDict
import Type.Compare
import Type.Rename
import Type.Type
import Type.Eval
import Type.Environment

import Globals
import GlobalVar

data LREnv =
  LREnv
  { lrIdSupply :: {-# UNPACK #-}!(Supply VarID)
    
    -- | Active rewrite rules
  , lrRewriteRules :: !RewriteRuleSet

    -- | Information about the values stored in variables
  , lrKnownValues :: IntMap.IntMap KnownValue
    
    -- | Types of variables
  , lrTypeEnv :: TypeEnv
    
  , lrDictEnv :: MkDictEnv
  , lrIntEnv :: IntIndexEnv
  }

newtype LR a = LR {runLR :: LREnv -> IO a}

instance Monad LR where
  return x = LR (\_ -> return x)
  m >>= k = LR $ \env -> do
    x <- runLR m env
    runLR (k x) env

instance MonadIO LR where
  liftIO m = LR (\_ -> m)
    
instance Supplies LR VarID where
  fresh = LR (\env -> supplyValue (lrIdSupply env))
  supplyToST = undefined

instance TypeEnvMonad LR where
  getTypeEnv = withTypeEnv return

instance ReprDictMonad LR where
  withVarIDs f = LR $ \env -> runLR (f $ lrIdSupply env) env
  withTypeEnv f = LR $ \env -> runLR (f $ lrTypeEnv env) env
  withDictEnv f = LR $ \env -> runLR (f $ lrDictEnv env) env
  getIntIndexEnv = LR $ \env -> return (lrIntEnv env)
  localDictEnv f m = LR $ \env ->
    let env' = env {lrDictEnv = f $ lrDictEnv env}
    in runLR m env'
  localIntIndexEnv f m = LR $ \env ->
    let env' = env {lrIntEnv = f $ lrIntEnv env}
    in runLR m env'

liftFreshVarM :: FreshVarM a -> LR a
liftFreshVarM m = LR $ \env -> do
  runFreshVarM (lrIdSupply env) m

liftTypeEvalM :: TypeEvalM a -> LR a
liftTypeEvalM m = LR $ \env -> do
  runTypeEvalM m (lrIdSupply env) (lrTypeEnv env)

getRewriteRules :: LR RewriteRuleSet
getRewriteRules = LR $ \env -> return (lrRewriteRules env)

lookupKnownValue :: Var -> LR MaybeValue
lookupKnownValue v = LR $ \env ->
  let val = IntMap.lookup (fromIdent $ varID v) $ lrKnownValues env
  in return val

-- | Add a variable's known value to the environment 
withKnownValue :: Var -> KnownValue -> LR a -> LR a
withKnownValue v val m = LR $ \env ->
  let insert_assignment mapping =
        IntMap.insert (fromIdent $ varID v) val mapping
      env' = env {lrKnownValues = insert_assignment $ lrKnownValues env}
  in runLR m env'
  where
    -- Debugging: Show the known value for this variable
    trace_assignment =
      traceShow (text "Simpl" <+> pprVar v <+> text "=" <+> pprKnownValue val)

-- | Add a variable's value to the environment, if known
withMaybeValue :: Var -> MaybeValue -> LR a -> LR a
withMaybeValue _ Nothing m = m
withMaybeValue v (Just val) m = withKnownValue v val m

-- | Add a function definition's value to the environment
withDefValue :: Def Mem -> LR a -> LR a
withDefValue (Def v _ f) m =
  let fun_info = funInfo $ fromFunM f
  in withKnownValue v (ComplexValue (Just v) $ FunValue fun_info f) m

-- | Add a function definition to the environment, but don't inline it
withUninlinedDefValue :: Def Mem -> LR a -> LR a
withUninlinedDefValue (Def v _ f) m =
  withMaybeValue v Nothing m

withDefValues :: DefGroup (Def Mem) -> LR a -> LR a
withDefValues (NonRec def) m = withDefValue def m
withDefValues (Rec _)      m = m

-- | Add a variable's type to the environment 
assume :: Var -> ReturnType -> LR a -> LR a
assume v rt m = LR $ \env ->
  let env' = env {lrTypeEnv = insertType v rt $ lrTypeEnv env}
  in runLR m env'

-- | Add a variable's type to the environment 
assumeParamType :: Var -> ParamType -> LR a -> LR a
assumeParamType v (prepr ::: ptype) m =
  assume v (paramReprToReturnRepr prepr ::: ptype) m

-- | Add a pattern-bound variable to the environment.  
--   This adds the variable's type to the environment and
--   its dictionary information if it is a dictionary.
--   The pattern must not be a local variable pattern.
assumePattern :: PatM -> LR a -> LR a
assumePattern (LocalVarP {}) _ = internalError "assumePattern"

assumePattern pat m =
  saveReprDictPattern pat $ 
  case patMVar pat of
    Just v -> assumeParamType v (patMParamType pat) m
    Nothing -> m

assumePatterns :: [PatM] -> LR a -> LR a
assumePatterns pats m = foldr assumePattern m pats

assumeTyPatM :: TyPatM -> LR a -> LR a
assumeTyPatM (TyPatM v ty) m = assume v (ValRT ::: ty) m

assumeTyPatMs :: [TyPatM] -> LR a -> LR a
assumeTyPatMs typats m = foldr assumeTyPatM m typats

-- | Add the function definition types to the environment
assumeDefs :: DefGroup (Def Mem) -> LR a -> LR a
assumeDefs defs m = foldr assumeDef m (defGroupMembers defs)

assumeDef :: Def Mem -> LR a -> LR a
assumeDef (Def v _ f) m = assume v (BoxRT ::: functionType f) m

-- | Print the known values on entry to the computation.
dumpKnownValues :: LR a -> LR a
dumpKnownValues m = LR $ \env ->
  let kv_doc = hang (text "dumpKnownValues") 2 $
               vcat [hang (text (show n)) 8 (pprKnownValue kv)
                    | (n, kv) <- IntMap.toList $ lrKnownValues env]
  in traceShow kv_doc $ runLR m env

-- | Try to construct the value of an expression, if it's easy to get.
--
--   This is called if we've already simplified an expression and thrown
--   away its value, and now we want to get it back.
makeExpValue :: ExpM -> LR MaybeValue
makeExpValue (ExpM expression) =
  case expression
  of VarE inf v -> do
       mvalue <- lookupKnownValue v
       return $ mvalue `mplus` Just (VarValue inf v)
     LitE inf l -> return $ Just $ LitValue inf l
     _ -> return Nothing

-- | Run type inferernce on an expression
rwInferExpType :: ExpM -> LR ReturnType
rwInferExpType expression = LR $ \env -> do
  inferExpType (lrIdSupply env) (lrTypeEnv env) expression

-------------------------------------------------------------------------------
-- Inlining

-- | Decide whether to inline the expression, which is the RHS of an
--   assignment, /before/ simplifying it.  If inlining is indicated, it
--   must be possible to replace all occurrences of the assigned variable
--   with the inlined value; to ensure this, reference values are never
--   pre-inlined.  Pre-inlining is performed only if it does not duplicate
--   code or work.
--
--   If the expression should be inlined, return a 'KnownValue' holding
--   the equivalent value.  Non-writer expressions become an
--   'InlinedValue'.  Writer expressions become a 'DataValue' containing
--   'InlinedValue's.
worthPreInlining :: TypeEnv -> Dmd -> ExpM -> Maybe KnownValue
worthPreInlining tenv dmd expr =
  let should_inline =
        case multiplicity dmd
        of OnceSafe -> inlckTrue
           ManySafe -> inlckTrivial
           OnceUnsafe -> inlckTrivial `inlckOr` inlckFunction
           _ -> inlckFalse
  in if should_inline tenv dmd expr
     then Just (InlinedValue expr)
     else Nothing

{- Value inlining (below) is disabled; it currently
-- interacts poorly with other optimizations.

-- | Decide whether to inline the expression, which is the RHS of an
--   assignment, /after/ simplifying it.  The assignment is not deleted.
--   If inlining makes the assignment dead (we try to ensure that it does),
--   it will be deleted by dead code elimination.
--
--   The expression is a value, boxed, or writer expression.
--
--   If the expression should be inlined, return a 'KnownValue' holding
--   the equivalent value.  Non-writer expressions become an
--   'InlinedValue'.  Writer expressions become a 'DataValue' containing
--   'InlinedValue's.
worthPostInlining :: TypeEnv -> Bool -> Dmd -> ExpM -> Maybe KnownValue
worthPostInlining tenv is_writer dmd expr =
  let should_inline =
        case multiplicity dmd
        of OnceSafe 
             | is_writer -> demanded_safe
             | otherwise -> inlckTrue
           ManySafe ->
             -- Inlining does not duplicate work, but may duplicate code.
             -- Inline as long as code duplicatation is small and bounded.
             data_only
           OnceUnsafe ->
             -- Inlining does not duplicate code, but may duplicate work.
             -- Inline as long as work duplication is small and bounded.
             data_and_functions
           ManyUnsafe -> 
             -- Inline as long as code and work duplication are both 
             -- small and bounded.
             demanded_data_only
           _ -> inlckFalse
  in if should_inline tenv dmd expr
     then data_value is_writer expr
     else Nothing
  where
    -- The expression will be inlined; convert it into a known value.
    -- Non-writer fields are simply inlined.
    data_value False expr = Just $ InlinedValue expr
    
    -- Writer fields are converted to readable data constructor values
    data_value True expr =
      case unpackVarAppM expr
      of Just (op, ty_args, args)
           | op `isPyonBuiltin` the_store ->
               -- Behave like 'rwStoreApp'.
               -- Allow the store to cancel with a later load.
               let [source] = args
               in Just $ complexKnownValue $
                  WriterValue $ complexKnownValue $
                  StoredValue Value $ InlinedValue source

           | op `isPyonBuiltin` the_storeBox ->
               -- Behave like 'rwStoreBoxApp'.
               -- Allow the store to cancel with a later load.
               let [source] = args
               in Just $ complexKnownValue $
                  WriterValue $ complexKnownValue $
                  StoredValue Boxed $ InlinedValue source

           | op `isPyonBuiltin` the_copy ->
               -- When using the value, read the source value directly
               let [_, source] = args
               in Just $ complexKnownValue $ WriterValue $ InlinedValue source
           | Just dcon <- lookupDataCon op tenv ->
               let (field_types, _) =
                     instantiateDataConTypeWithExistentials dcon ty_args
                   
                   Just tycon = lookupDataType (dataConTyCon dcon) tenv

                   is_writer_field (ValRT ::: _) = False
                   is_writer_field (BoxRT ::: _) = False
                   is_writer_field (ReadRT ::: _) = True

                   fields = [data_value (is_writer_field fld) arg
                            | (fld, arg) <- zip field_types args]
               in if length args /= length field_types
                  then internalError "worthPostInlining"
                  else dataConValue defaultExpInfo tycon dcon
                       (map TypM ty_args) fields
         _ -> Nothing

    demanded_safe =
      inlckTrivial `inlckOr`
      inlckFunction `inlckOr`
      inlckConstructor demanded_safe `inlckOr`
      inlckDataMovement inlckTrue demanded_safe
    
    data_only =
      inlckTrivial `inlckOr` inlckConstructor data_only
    
    data_and_functions =
      inlckTrivial `inlckOr`
      inlckFunction `inlckOr`
      inlckConstructor data_and_functions
    
    demanded_data_only =
      inlckTrivial `inlckOr`
      inlckDemanded `inlckAnd` demanded_constructor
      where
        demanded_constructor =
          inlckConstructor demanded_data_only `inlckOr`
          inlckDataMovement demanded_data_only demanded_data_only

-- | Decide whether a local variable assignment is worth inlining.
--   The expression initializes the local variable.
--   We can only handle data constructor expressions; refuse to inline other
--   expressions.  Convert the expression
--   to a writer by removing the destination argument, then call
--   'worthPostInlining'.
worthPostInliningLocal tenv dmd lhs_var rhs_value =
  case unpackDataConAppM tenv rhs_value
  of Just (data_con, ty_args, args) 
       | null args -> err
       | otherwise ->
           let args' = init args
               destination_arg = last args
           in case destination_arg
              of ExpM (VarE _ v) | v == lhs_var ->
                   -- The expected pattern has been matched.  Rebuild the
                   -- expression sans its last argument.
                   let op = ExpM $ VarE defaultExpInfo (dataConCon data_con)
                       writer_exp =
                         ExpM $ AppE defaultExpInfo op (map TypM ty_args) args'
                   in worthPostInlining tenv True dmd writer_exp
                 _ -> err

     -- We can't inline other expressions
     _ -> Nothing
  where
    err = internalError "worthPostInliningLocal: Unexpected expression"
-}
  
-- | A test performed to decide whether to inline an expression
type InlineCheck = TypeEnv -> Dmd -> ExpM -> Bool

inlckTrue, inlckFalse :: InlineCheck
inlckTrue _ _ _  = True
inlckFalse _ _ _ = False

inlckOr :: InlineCheck -> InlineCheck -> InlineCheck
infixr 2 `inlckOr`
inlckOr a b tenv dmd e = a tenv dmd e || b tenv dmd e

inlckAnd :: InlineCheck -> InlineCheck -> InlineCheck
infixr 3 `inlckAnd`
inlckAnd a b tenv dmd e = a tenv dmd e && b tenv dmd e

-- | Is the expression trivial?
inlckTrivial :: InlineCheck
inlckTrivial _ _ e = isTrivialExp e

-- | Is the expression a lambda function?
inlckFunction :: InlineCheck
inlckFunction _ _ (ExpM (LamE {})) = True
inlckFunction _ _ _ = False

-- | Is the expression a data constructor application?
--
--   If so, apply the given check to its fields.
inlckConstructor :: InlineCheck -> InlineCheck
inlckConstructor ck tenv dmd expression =
  case unpackDataConAppM tenv expression
  of Just (dcon, _, args) ->
       -- This is a data constructor application.
       -- Test its fields.
       let field_demands =
             case specificity dmd
             of Decond _ _ _ spcs -> map (Dmd (multiplicity dmd)) spcs
                _ -> replicate (length args) $ Dmd (multiplicity dmd) Used
       in and $ zipWith (ck tenv) field_demands args
     Nothing -> False

-- | Is the expression demanded at least as much as being inspected?
--
--   If it's demanded, then the head of the expression will probably be
--   eliminated after it's inlined.
inlckDemanded :: InlineCheck
inlckDemanded _ dmd _ =
  case specificity dmd
  of Decond {} -> True
     Inspected -> True
     _         -> False

-- | Is the expression a data movement expression?
--
--   If so, check its arguments.
inlckDataMovement :: InlineCheck -- ^ Test other arguments
                  -> InlineCheck -- ^ Test stored data argument
                  -> InlineCheck
inlckDataMovement ptr_ck data_check tenv dmd expression =
  case unpackVarAppM expression
  of Just (op, _, args)
       | op `isPyonBuiltin` the_store ->
           let [dat] = args
               dat_spc = case specificity dmd
                         of Loaded _ _ spc -> spc
                            _ -> Used
               dat_dmd = Dmd (multiplicity dmd) dat_spc
           in data_check tenv dat_dmd dat
       | op `isPyonBuiltin` the_load ->
           let [src] = args
           in ptr_ck tenv (Dmd (multiplicity dmd) Used) src
       | op `isPyonBuiltin` the_copy ->
           let [repr, src] = args
           in ptr_ck tenv (Dmd (multiplicity dmd) Used) repr &&
              ptr_ck tenv (Dmd (multiplicity dmd) Used) src
     _ -> False

-- | Given a function and its arguments, get an expresion equivalent to
--   the function applied to those arguments.
--
--   No need to simplify the expression; it will be rewritten after beta
--   reduction.
betaReduce :: (Monad m, Supplies m VarID) =>
              ExpInfo -> FunM -> [TypM] -> [ExpM] -> m ExpM
betaReduce inf (FunM fun) ty_args args
  | length ty_args /= length (funTyParams fun) =
      internalError "betaReduce: Not implemented for partial type application"
  | otherwise = do
      -- Substitute type arguments for type parameters
      let type_subst =
            substitution [(tv, t)
                         | (TyPatM tv _, TypM t) <-
                             zip (funTyParams fun) ty_args]

          -- Apply substitution to parameters and body
      (params, param_renaming) <-
        freshenPatMs $ map (substitutePatM type_subst) $ funParams fun
      let body = rename param_renaming $ substitute type_subst $ funBody fun
      let ret = rename param_renaming $ substitute type_subst $ funReturn fun
          
      -- Is the function fully applied?
      return $! case length args `compare` length params
                of LT -> undersaturated_app args params body ret
                   EQ -> saturated_app args params body
                   GT -> oversaturated_app args params body
  where
    oversaturated_app args params body =
      let applied_args = take (length params) args
          excess_args = drop (length params) args
          applied_expr = saturated_app applied_args params body
      in ExpM $ AppE inf applied_expr [] excess_args
  
    saturated_app args params body =
      -- Bind parameters to arguments
      bind_parameters params args body
    
    -- To process an undersaturated application,
    -- assign the parameters that have been applied and 
    -- create a new function that takes the remaining arguments.
    undersaturated_app args params body return =
      let applied_params = take (length args) params
          excess_params = drop (length args) params
          new_fun = FunM $ Fun { funInfo = funInfo fun
                               , funTyParams = []
                               , funParams = excess_params
                               , funBody = body
                               , funReturn = return}
      in bind_parameters applied_params args (ExpM $ LamE inf new_fun)

    bind_parameters params args body =
      foldr bind_parameter body $ zip params args
    
    bind_parameter (MemWildP {}, _) body = body
    bind_parameter (param, arg) body = ExpM $ LetE inf param arg body

-------------------------------------------------------------------------------
-- Local restructuring
    
-- Before trying to simplify an expression, we restruture it to increase the 
-- scopes of temporary variables.  Let-expressions are floated out from the
-- RHS of other let expressions and from inside function calls.

-- | Extract floatable bindings from an expression.  The floatable bindings
--   are added to the context parameter.
delveExp :: Context -> ExpM -> LR (Context, ExpM)
delveExp input_context (ExpM ex) = do
  case ex of
    LetE inf bind@(MemVarP {}) rhs body -> do
      -- First process the rhs
      (rhs_context, flattened_rhs) <- delveExp input_context rhs

      -- Float this binding
      (floated_bind, rn) <- freshenContextExp $ LetCtx inf bind flattened_rhs
      let output_context = contextItem floated_bind : rhs_context
          rn_body = rename rn body

      return (output_context, rn_body)

    LetE inf bind@(LocalVarP {}) rhs body -> do
      -- Don't float this let-binding.
      -- Float let-bindings out of the RHS,
      -- unless they mention the bound variable.
      (rhs_context, flattened_rhs) <- delveExp input_context rhs

      -- Don't float anything that depends on the bound variable.
      -- Any dependent bindings remain inside the RHS.
      let bound_variable = patMVar' bind
          mentions_bound_variable item =
            bound_variable `Set.member` contextItemUses item
          (dep_context, indep_context) =
            splitContext mentions_bound_variable rhs_context
          rhs' = applyContext dep_context flattened_rhs

      let replaced_let = ExpM $ LetE inf bind rhs' body
      return (indep_context, replaced_let)

    CaseE {}
      | Just (ctx, case_body) <- asCaseCtx (ExpM ex) -> do
          -- Rename the context to avoid name conflicts
          (ctx', rn) <- freshenContextExp ctx
          let rn_body = rename rn case_body

          -- Float out this case context
          (body_context, flattened_body) <-
            delveExp (contextItem ctx' : input_context) rn_body

          return (body_context, flattened_body)

    AppE inf oper tyArgs args -> do
      (ctx1, oper') <- delveExp input_context oper
      (ctx2, args') <- delveExps ctx1 args
      let replaced_app = ExpM $ AppE inf oper' tyArgs args'
      return (ctx2, replaced_app)

    _ -> return (input_context, ExpM ex)

delveExps :: Context -> [ExpM] -> LR (Context, [ExpM])
delveExps ctx (exp:exps) = do
  (ctx', exp') <- delveExp ctx exp
  (ctx'', exps') <- delveExps ctx' exps
  return (ctx'', exp' : exps')

delveExps ctx [] = return (ctx, [])

restructureExp :: ExpM -> LR ExpM
restructureExp ex = do
  (ctx, ex') <- delveExp [] ex
  if null ctx then return ex' else do
    -- Use the original expression's type as the return type.  It's the same as
    -- the new expression's type.
    e_type <- rwInferExpType ex
    return $ applyContextWithType e_type ctx ex'

-------------------------------------------------------------------------------
-- Traversing code

-- | Rewrite an expression.
--
--   Return the expression's value if it can be determined.
rwExp :: ExpM -> LR (ExpM, MaybeValue)
rwExp expression = do
  -- Flatten nested let and case statements
  ex1 <- restructureExp expression

  -- Simplify subexpressions
  case fromExpM ex1 of
    VarE inf v -> rwVar ex1 inf v
    LitE inf l -> rwExpReturn (ex1, Just $ LitValue inf l)
    AppE inf op ty_args args -> rwApp inf op ty_args args
    LamE inf fun -> do
      fun' <- rwFun fun
      rwExpReturn (ExpM $ LamE inf fun', Just $ complexKnownValue $ FunValue inf fun')
    LetE inf bind val body -> rwLet inf bind val body
    LetfunE inf defs body -> rwLetrec inf defs body
    CaseE inf scrut alts -> rwCase inf scrut alts
    ExceptE _ _ -> rwExpReturn (ex1, Nothing)

-- | Rewrite a list of expressions that are in the same scope,
--   such as arguments of a function call.
rwExps :: [ExpM] -> LR ([ExpM], [MaybeValue])
rwExps es = mapAndUnzipM rwExp es

rwExpReturn (exp, val) = return (exp, val)
    
-- | Rewrite a variable expression and compute its value.
rwVar original_expression inf v = lookupKnownValue v >>= rewrite
  where
    rewrite (Just val)
        -- Replace with an inlined or trivial value
      | Just inl_value <- asInlinedValue val = rwExp inl_value

      | Just cheap_value <- asTrivialValue val =
          rwExpReturn (cheap_value, Just val)

        -- Otherwise, don't inline, but propagate the value
      | otherwise = rwExpReturn (original_expression, Just val)
    rewrite Nothing =
      -- Set up for copy propagation
      rwExpReturn (original_expression, Just $ VarValue inf v)

rwApp :: ExpInfo -> ExpM -> [TypM] -> [ExpM] -> LR (ExpM, MaybeValue)
rwApp inf op ty_args args =
  -- First try to uncurry this application
  case op
  of ExpM (AppE _ inner_op inner_ty_args inner_args)
       | null ty_args ->
           rwApp inf inner_op inner_ty_args (inner_args ++ args)
       | null inner_args ->
           rwApp inf inner_op (inner_ty_args ++ ty_args) args
     _ -> do
       (op', op_val) <- rwExp op
       rwAppWithOperator inf op' op_val ty_args args

-- | Rewrite an application, depending on what the operator is.
--   The operator has been simplified, but the arguments have not.
--
--   This function is usually called from 'rwApp'.  It calls itself 
--   recursively to flatten out curried applications.
rwAppWithOperator inf op' op_val ty_args args =
  -- First, try to uncurry this application.
  -- This happens if the operator was rewritten to an application;
  -- otherwise we would have uncurried it in 'rwApp'.
  case op'
  of ExpM (AppE _ inner_op inner_ty_args inner_args)
       | null ty_args -> do
         inner_op_value <- makeExpValue inner_op
         rwAppWithOperator inf inner_op inner_op_value inner_ty_args (inner_args ++ args)
       | null inner_args -> do
         inner_op_value <- makeExpValue inner_op
         rwAppWithOperator inf inner_op inner_op_value (inner_ty_args ++ ty_args) args
     _ ->
       -- Apply simplification tecnhiques specific to this operator
       case op_val
       of Just (ComplexValue _ (FunValue _ funm@(FunM fun))) ->
            inline_function_call funm

          -- Use special rewrite semantics for built-in functions
          Just (VarValue _ op_var)
            | op_var `isPyonBuiltin` the_store ->
              rwStoreApp inf op' ty_args args
            | op_var `isPyonBuiltin` the_storeBox ->
              rwStoreBoxApp inf op' ty_args args
            | op_var `isPyonBuiltin` the_load ->
              rwLoadApp inf op' ty_args args
            | op_var `isPyonBuiltin` the_loadBox ->
              rwLoadBoxApp inf op' ty_args args
            | op_var `isPyonBuiltin` the_copy ->
              rwCopyApp inf op' ty_args args

          Just (VarValue _ op_var) -> do
            tenv <- getTypeEnv
            ruleset <- getRewriteRules
                
            -- Try to rewrite this application
            rewritten <- liftTypeEvalM $
                         rewriteApp ruleset inf op_var ty_args args
            case rewritten of 
              Just new_expr -> rwExp new_expr
              Nothing ->
                -- Try to construct a value for this application
                case lookupDataConWithType op_var tenv  
                of Just (type_con, data_con) ->
                     data_con_app type_con data_con op'
                   Nothing ->
                     unknown_app op'

          _ -> unknown_app op'
  where
    unknown_app op' = do
      (args', _) <- rwExps args
      let new_exp = ExpM $ AppE inf op' ty_args args'
      return (new_exp, Nothing)

    data_con_app type_con data_con op' = do
      -- Try to eta-reduce writer arguments, because this increases the
      -- likelihood that we can value-propagate them
      let types = map fromTypM ty_args
          (field_types, _) =
            instantiateDataConTypeWithExistentials data_con types
          
          -- Eta-reduce writer arguments, leave other arguments alone
          extended_field_types = map Just field_types ++ repeat Nothing
          eta_reduced_args = zipWith eta_reduce_arg args extended_field_types
            where
              -- Only eta-reduce known writer arguments
              eta_reduce_arg arg (Just (ReadRT ::: _)) = eta_reduce arg
              eta_reduce_arg arg _ = arg

              eta_reduce (ExpM (LamE inf f)) =
                etaReduceSingleLambdaFunction inf f
              eta_reduce e = e

      -- Simplify arguments
      (args', arg_values) <- rwExps eta_reduced_args
      
      -- Construct a value from this expression
      let new_exp = ExpM $ AppE inf op' ty_args args'
          new_value = dataConValue inf type_con data_con ty_args arg_values
      return (new_exp, new_value)

    -- Inline the function call and continue to simplify it.
    -- The arguments will be processed after inlining.
    inline_function_call funm =
      rwExp =<< betaReduce inf funm ty_args args

-- | Attempt to statically evaluate a store operation
rwStoreApp inf op' ty_args args = do
  (args', arg_values) <- rwExps args
  let new_exp = ExpM $ AppE inf op' ty_args args'
      new_value = stored_value arg_values
  return (new_exp, new_value)
  where
    -- Keep track of what was stored in memory
    stored_value [Just stored_value, _] =
      Just $ complexKnownValue $ StoredValue Value stored_value
    stored_value [_, _] = Nothing
    stored_value [Just stored_value] =
      -- When applied to an argument, this will store a value
      Just $ complexKnownValue $
      WriterValue $ complexKnownValue $
      StoredValue Value stored_value
    stored_value [_] = Nothing
    stored_value _ =
      internalError "rwStoreApp: Wrong number of arguments in call"
      
-- | Attempt to statically evaluate a store of a boxed object
rwStoreBoxApp inf op' ty_args args = do
  (args', arg_values) <- rwExps args
  let new_exp = ExpM $ AppE inf op' ty_args args'
      new_value = stored_value arg_values
  return (new_exp, new_value)
  where
    -- Keep track of what was stored in memory
    stored_value [Just stored_value, _] =
      Just $ complexKnownValue $ StoredValue Boxed stored_value
    stored_value [_, _] = Nothing
    stored_value [Just stored_value] =
      -- When applied to an argument, this will store a value
      Just $ complexKnownValue $
      WriterValue $ complexKnownValue $
      StoredValue Boxed stored_value
    stored_value [_] = Nothing
    stored_value _ =
      internalError "rwStoreBoxApp: Wrong number of arguments in call"

-- | Attempt to statically evaluate a load
rwLoadApp inf op' ty_args args = do
  (args', arg_values) <- rwExps args
  let new_exp = ExpM $ AppE inf op' ty_args args'
  case loaded_value arg_values of
    Just (m_loaded_exp, new_value) ->
      return (fromMaybe new_exp m_loaded_exp, new_value)
    Nothing ->
      return (new_exp, Nothing)
  where
    -- Do we know what was stored here?
    loaded_value [addr_value] =
      case addr_value 
      of Just (ComplexValue _ (StoredValue Value val)) ->
           Just (asTrivialValue val, Just val)
         _ -> Nothing
    loaded_value _ =
      internalError "rwLoadApp: Wrong number of arguments in call"

-- | Attempt to statically evaluate a load of a boxed object.
--   Since we may be loading and then callign a function,
--   we have to deal with excess arguments.    
rwLoadBoxApp inf op' ty_args (addr_arg : excess_args) = do
  -- Simplify the load expression, which involves only the first argument
  (addr_arg', addr_value) <- rwExp addr_arg
  let load_exp = ExpM $ AppE inf op' ty_args [addr_arg']
      loaded_value =
        case addr_value
        of Just (ComplexValue _ (StoredValue Boxed val)) -> Just val
           _ -> Nothing
      
      -- Try to make a simplified expression
      m_loaded_exp = loaded_value >>= asTrivialValue
      simplified_exp = fromMaybe load_exp m_loaded_exp
  
  -- Process any remaining arguments
  case excess_args of
    [] -> return (simplified_exp, loaded_value)
    _ -> case m_loaded_exp
         of Nothing -> do
              -- Cannot simplify this expression further.
              -- Process the other subexpressions.
              (args', _) <- rwExps excess_args
              let new_exp = ExpM $ AppE inf simplified_exp [] args'
              return (new_exp, Nothing)
            Just loaded_exp ->
              -- We have eliminated this load expression.  Try simplifying
              -- the application that we got as a result.
              rwAppWithOperator inf loaded_exp loaded_value [] excess_args

-- | Attempt to statically evaluate a copy
rwCopyApp inf op' ty_args args = do
  (args', arg_values) <- rwExps args
  let new_exp = copy_expression args' arg_values
      new_value = copied_value arg_values
  return (new_exp, new_value)
  where
    -- Do we know what was stored here?
    copied_value [_, Just src_val, Just dst_val] =
      -- Reference the source value instead of the destination value
      Just src_val
    copied_value [_, _, _] = Nothing
    copied_value [_, Just src_val] =
      Just $ complexKnownValue $ WriterValue src_val
    copied_value [_, _] = Nothing
    copied_value _ =
      internalError "rwCopyApp: Wrong number of arguments in call"
    
    -- Transform a copy into a store if the source value is known
    copy_expression (repr : src : other_args) (_ : Just src_value : _)
      | ComplexValue _ (StoredValue Value stored_value) <- src_value,
        Just stored_exp <- asTrivialValue stored_value =
          let [store_type] = ty_args
              store_op = ExpM $ VarE inf (pyonBuiltin the_store)
          in ExpM $ AppE inf store_op [store_type] (stored_exp : other_args)
    
      | ComplexValue _ (StoredValue Boxed stored_value) <- src_value,
        Just stored_exp <- asTrivialValue stored_value =
          let [store_type] = ty_args
              store_op = ExpM $ VarE inf (pyonBuiltin the_storeBox)
          in ExpM $ AppE inf store_op [store_type] (stored_exp : other_args)

    -- Otherwise return a copy expression
    copy_expression args _ = ExpM $ AppE inf op' ty_args args
      

rwLet inf bind val body =       
  case bind
  of MemVarP bind_var bind_rtype uses -> do
       tenv <- getTypeEnv
       case worthPreInlining tenv uses val of
         Just val -> do
           -- The variable is used exactly once; inline it.
           (body', body_val) <-
             assumePattern bind $ withKnownValue bind_var val $ rwExp body
           let ret_val = mask_local_variable bind_var body_val
           rwExpReturn (body', ret_val)

         Nothing -> do
           (val', val_value) <- rwExp val

           -- If the RHS expression raises an exception, then the entire
           -- let-expression raises an exception.
           glom_exceptions (assumePattern bind) val' $ do
             -- Inline the RHS expression, if desirable.  If
             -- inlining is not indicated, then propagate its known
             -- value.
             let local_val_value =
                   fmap (setTrivialValue bind_var) $ val_value

             -- Add local variable to the environment and rewrite the body
             (body', body_val) <-
               assumePattern bind $
               withMaybeValue bind_var local_val_value $
               rwExp body
       
             let ret_val = mask_local_variable bind_var body_val
             rwExpReturn (ExpM $ LetE inf bind val' body', ret_val)

     LocalVarP bind_var bind_type dict uses -> do
       tenv <- getTypeEnv
       (dict', _) <- rwExp dict

       -- Add the variable to the environment while rewriting the rhs
       (val', val_value) <-
         assume bind_var (OutRT ::: bind_type) $ rwExp val
       
       -- If the RHS expression raises an exception, then the entire
       -- let-expression raises an exception.
       glom_exceptions (assume bind_var (ReadRT ::: bind_type)) val' $ do
         -- Inline the RHS expression, if desirable.  If inlining is not  
         -- indicated, then propagate its known value.
         let local_val_value =
               fmap (setTrivialValue bind_var) $ val_value

         -- Add the local variable to the environment while rewriting the body
         (body', body_val) <-
           assume bind_var (ReadRT ::: bind_type) $
           withMaybeValue bind_var local_val_value $
           rwExp body
           
         let ret_val = mask_local_variable bind_var body_val
         let ret_exp =
               ExpM $ LetE inf (LocalVarP bind_var bind_type dict' uses) val' body'
         rwExpReturn (ret_exp, ret_val)

     MemWildP {} -> internalError "rwLet"
  where
    -- The computed value for this let expression cannot mention the locally 
    -- defined variable.  If it's in the body's
    -- value, we have to forget about it.
    mask_local_variable bind_var ret_val =
      forgetVariables (Set.singleton bind_var) =<< ret_val

    -- If the given value is an exception-raising expression, then we should
    -- convert the entire let-expression to an exception-raising expression
    -- with the same type as the body expression.
    glom_exceptions assume_pattern rewritten_rhs normal_case =
      case rewritten_rhs
      of ExpM (ExceptE exc_inf _) -> do
           return_type <- assume_pattern $ rwInferExpType body
           return (ExpM $ ExceptE exc_inf return_type, Nothing)
         _ -> normal_case       -- Otherwise, continue as normal

{-
rwLetBinding inf bind rhs mk_body =
  case bind
  of MemVarP bind_var bind_rtype uses 
       | OnceSafe <- multiplicity uses ->
           -- Inline this binding unconditionally.  Don't add the bound
           -- variable to the type environment.
           withMaybeValue bind_var (Just $ InlinedValue rhs) mk_body
       | Decond (Just con) spc <- specificity uses -> do
           tenv <- getTypeEnv
           case unpackDataConApp tenv con rhs of
             Just (ty_args, args) -> rwFieldBindings 
               
         deconDataConstructor con 
           -- Deconstruct this binding if possible
         case 

-- | Attempt to deconstruct a let binding.
--   If we've determined that the bound value is
--   /only/ deconstructed, then try to individually bind the fields to local
--   variables.

deconLetBinding :: Var          -- ^ bound variable
                -> Maybe Var    -- ^ constructor
                -> [Specificity] -- ^ demands on fields
                -> ExpM          -- ^ expression whose result is bound
                -> LR ExpM       -- ^ body computation
                -> LR ExpM       -- ^ simplifier of the let expression
deconLetBinding pat_var mcon field_demands rhs do_body =
  case rhs
  of ExpM (AppE _ (ExpM (VarE _ op_var)) ty_args args)
       | mcon == Just op_var -> do
           tenv <- getTypeEnv
           case lookupDataConWithType op_var tenv of
             Just dcon -> undefined
-}               

rwLetrec inf defs body = withDefs defs $ \defs' -> do
  (body', body_value) <- rwExp body
      
  let local_vars = Set.fromList $ map definiendum $ defGroupMembers defs'
      ret_value = forgetVariables local_vars =<< body_value
  rwExpReturn (ExpM $ LetfunE inf defs' body', ret_value)

rwCase inf scrut alts = do
  (scrut', scrut_val) <- rwExp scrut
  
  tenv <- getTypeEnv
  case unpackDataConAppM tenv scrut' of
    Just (data_con, ty_args, args) -> do
      -- Eliminate case-of-constructor expressions using the actual
      -- argument values.  We can eliminate case statements this way
      -- even when we can't compute known values for the fields.
      let altm = find_alternative $ dataConCon data_con
          ex_args = map TypM $
                    drop (length $ dataConPatternParams data_con) ty_args
      m_elim <- elimCaseAlternative True inf altm ex_args (map Just args)
      case m_elim of
        Just eliminated_case -> rwExp eliminated_case
        Nothing  -> no_eliminate scrut' Nothing [altm]
    _ -> case scrut_val
         of Just (ComplexValue _ (DataValue _ con _ ex_args margs)) -> do
              case_of_known_value scrut' con ex_args margs
            Just (ComplexValue _ (StoredValue Referenced (ComplexValue _ (DataValue _ con _ ex_args margs)))) -> do
              case_of_known_value scrut' con ex_args margs              
            _ -> no_eliminate scrut' Nothing alts
  where
    -- Find the alternative matching constructor @con@
    find_alternative con =
      case find ((con ==) . altConstructor . fromAltM) alts
      of Just alt -> alt
         Nothing -> internalError "rwCase: Missing alternative"

    case_of_known_value scrut' con ex_args margs = do
      -- Case of known value.
      -- Select the appropriate alternative and discard others.
      -- If possible, eliminate the expression.
      let altm = find_alternative con
          arg_vals = map (>>= asTrivialValue) margs
      m_elim <- elimCaseAlternative False inf altm ex_args arg_vals
      case m_elim of
        Just eliminated_case -> rwExp eliminated_case
        Nothing -> no_eliminate scrut' (Just (ex_args, margs)) [altm]

    -- Cannot eliminate this case statement.  Possibly eliminated
    -- some case alternatives.  If we know the values of some fields,
    -- we can use that to simplify the body of the case statement.
    no_eliminate scrut' m_arg_values reduced_alts = do
      alts' <- mapM (rwAlt scrutinee_var m_arg_values) reduced_alts
      rwExpReturn (ExpM $ CaseE inf scrut' alts', Nothing)
      where
        scrutinee_var =
          case scrut'
          of ExpM (VarE _ scrut_var) -> Just scrut_var
             _ -> Nothing

-- | Eliminate a case alternative, given the values of existential types and
--   some of the fields.  If some needed fields are not given, elimination
--   will fail.  Return the eliminated expression if elimination succeeded,
--   @Nothing@ otherwise.
--
--   If @from_writer@ is 'True', then write references may be
--   given for the writable case fields, and they should write to local
--   variables.  Otherwise, read references may be given for those fields,
--   and they should be assigned to new variables.
elimCaseAlternative :: Bool -> ExpInfo -> AltM -> [TypM] -> [Maybe ExpM]
                    -> LR (Maybe ExpM)
elimCaseAlternative from_writer inf (AltM alt) ex_args args
  | length (altExTypes alt) /= length ex_args =
      internalError "rwCase: Wrong number of type parameters"
  | length (altParams alt) /= length args =
      internalError "rwCase: Wrong number of fields"
  | otherwise = runMaybeT $ do
      let -- Substitute known types for the existential type variables
          ex_type_subst =
            substitution $
            zip [v | TyPatM v _ <- altExTypes alt] $ map fromTypM ex_args

          patterns = map (substitutePatM ex_type_subst) (altParams alt)
          subst_body = substitute ex_type_subst (altBody alt)

      -- Identify (pattern, value) pairs that should be bound by 
      -- let expressions
      m_bindings <- zipWithM bind_field patterns args
      let bindings = catMaybes m_bindings
          new_exp = foldr make_binding subst_body bindings
      return new_exp
  where
    -- Construct a let-binding from the values returned by bind_field
    -- and a body expression
    make_binding (MemWildP {}, _) body = body
    make_binding (pat, rhs) body = ExpM $ LetE inf pat rhs body

    -- Attempt to bind a value to a data field.
    -- Return Nothing if a binding is required but cannot be built.
    -- Return (Just Nothing) if no binding is required.
    -- Return (Just (Just (p, v))) to produce binding (p, v).
    bind_field :: PatM -> Maybe ExpM -> MaybeT LR (Maybe (PatM, ExpM))
    bind_field (MemWildP {}) _ =
      return Nothing

    bind_field pat@(MemVarP {}) arg
      | okay_for_value_binding = do
          arg_exp <- MaybeT $ return arg
          return $ Just (pat, arg_exp)

      | from_writer && okay_for_reference_binding = do
          -- Bind this expression to a local variable.  We can reuse the
          -- same variable that we were given.
          -- The expression is a writer function; apply it to the
          -- local variable so that it will write it.
          arg_exp <- MaybeT $ return arg
          let out_exp = ExpM $ VarE defaultExpInfo (patMVar' pat)
              initializer_exp = ExpM $ AppE defaultExpInfo arg_exp [] [out_exp]
          
          -- Look up the representation dictionary for this type
          dict_exp <- withReprDict (patMType pat) return

          let binder = localVarP (patMVar' pat) (patMType pat) dict_exp
          return $ Just (binder, initializer_exp)

      | not from_writer && okay_for_reference_binding = do
          -- Assign this expression to a local variable.
          arg_exp <- MaybeT $ return arg
          return $ Just (pat, arg_exp)

      | otherwise = mzero   -- Cannot bind this pattern
      where
        -- We can only bind value and boxed parameters this way
        okay_for_value_binding =
          case patMRepr pat
          of ValPT _ -> True
             BoxPT -> True
             _ -> False

        okay_for_reference_binding =
          case patMRepr pat of {ReadPT -> True; _ -> False}

    bind_field _ _ = internalError "rwCase: Unexpected pattern"

rwAlt :: Maybe Var -> Maybe ([TypM], [MaybeValue]) -> AltM -> LR AltM
rwAlt scr m_values (AltM (Alt con tyArgs exTypes params body)) = do
  -- If we're going to record a known value for the scrutinee, 
  -- convert wildcard to non-wildcard patterns.  This increases the
  -- usefulness of recording known values.
  labeled_params <-
    if isJust scr
    then mapM labelParameter params
    else return params

  -- Get the known values of the fields.  If values are given for the fields,
  -- the number of fields must match.  If there are existential variables,
  -- we must rename them.
  let values = 
        case m_values
        of Just (ex_args, given_values)
             | length given_values /= length params ||
               length ex_args /= length exTypes ->
                 internalError "rwAlt"
             | not $ null exTypes ->
                 -- Not implemented.
                 -- To implement this, we need to unify existential
                 -- variable names appearing in the values with
                 -- existential variable names appearing in the
                 -- pattern.
                 repeat Nothing
             | otherwise ->
                 given_values
           _ -> repeat Nothing

  assume_params (zip values labeled_params) $ do
    (body', _) <- rwExp body
    return $ AltM $ Alt con tyArgs exTypes labeled_params body'
  where
    assume_params labeled_params m = do
      tenv <- getTypeEnv
      let with_known_value = assume_scrutinee tenv labeled_params m
          with_params = assume_parameters labeled_params with_known_value
          with_ty_params = foldr assumeTyPatM with_params exTypes
      with_ty_params
      
    assume_parameters labeled_params m = foldr assume_param m labeled_params
    
    -- Add a parameter and its value to the environment
    assume_param (maybe_value, param) m =
      assumePattern param $ withMaybeValue (patMVar' param) maybe_value m
    
    -- If the scrutinee is a variable, add its known value to the environment.
    -- It will be used if the variable is inspected again. 
    assume_scrutinee tenv labeled_params m =
      case scr
      of Just scrutinee_var ->
           let ex_args = [v | TyPatM v _ <- exTypes]
               arg_values = map mk_arg labeled_params
               Just (data_type, dcon_type) = lookupDataConWithType con tenv
               data_value = patternValue defaultExpInfo data_type dcon_type tyArgs ex_args arg_values
           in withMaybeValue scrutinee_var data_value m
         Nothing -> m
      where
        mk_arg (maybe_val, pat) =
          case patMVar pat
          of Just var ->
               case maybe_val
               of Just val -> Just (setTrivialValue var val)
                  Nothing  -> Just (VarValue defaultExpInfo var)
             Nothing ->
               -- It would be safe to return Nothing here.
               -- However, we tried to give every parameter a variable name,
               -- so this shouldn't be Nothing.
               internalError "rwAlt"

-- | Ensure that the parameter binds a variable.
labelParameter param = 
  case param
  of MemVarP {} -> return param
     LocalVarP {} -> internalError "labelParameter: Unexpected pattern"
     MemWildP pty -> do
       pvar <- newAnonymousVar ObjectLevel
       return (memVarP pvar pty)

rwFun :: FunM -> LR FunM
rwFun (FunM f) =
  assumeTyPatMs (funTyParams f) $
  assumePatterns (funParams f) $ do
    (body', _) <- rwExp (funBody f)
    return $ FunM $ f {funBody = body'}

rwDef :: Def Mem -> LR (Def Mem)
rwDef def = mapMDefiniens rwFun def

rwExport :: Export Mem -> LR (Export Mem)
rwExport (Export pos spec f) = do
  f' <- rwFun f
  return (Export pos spec f')

-- | Rewrite a definition group.  Then, add the defined functions to the
--   environment and rewrite something else.
withDefs :: DefGroup (Def Mem) -> (DefGroup (Def Mem) -> LR a) -> LR a
withDefs (NonRec def) k = do
  def' <- rwDef def
  assumeDef def' $ withDefValue def' $ k (NonRec def')

withDefs defgroup@(Rec defs) k = assumeDefs defgroup $ do
  -- Don't inline recursive functions in general.  However, we _do_ want to
  -- inline wrapper functions into non-wrapper functions, even in recursive
  -- definition groups.  So process the wrapper functions first, followed by
  -- the other functions.
  let (wrappers, others) = partition defIsWrapper defs
  wrappers' <- mapM rwDef wrappers
  with_wrappers wrappers' $ do
    others' <- mapM rwDef others
    let defgroup' = Rec (wrappers' ++ others')
    withDefValues defgroup' $ k defgroup'
  where
    with_wrappers wrs m = foldr withDefValue m wrs

rwModule :: Module Mem -> LR (Module Mem)
rwModule (Module mod_name defss exports) = rw_top_level id defss
  where
    -- First, rewrite the top-level definitions.
    -- Add defintion groups to the environment as we go along.
    rw_top_level defss' (defs:defss) =
      withDefs defs $ \defs' -> rw_top_level (defss' . (defs' :)) defss
    
    -- Then rewrite the exported functions
    rw_top_level defss' [] = do
      exports' <- mapM rwExport exports
      return $ Module mod_name (defss' []) exports'

rewriteLocalExpr :: RewriteRuleSet -> Module Mem -> IO (Module Mem)
rewriteLocalExpr ruleset mod =
  withTheNewVarIdentSupply $ \var_supply -> do
    tenv <- readInitGlobalVarIO the_memTypes
    (denv, ienv) <- runFreshVarM var_supply createDictEnv
    
    -- Take known data constructors from the type environment
    let global_known_values = initializeKnownValues tenv
    
    -- For each variable rewrite rule, create a known value that will be 
    -- inlined in place of the variable.
    let known_values = foldr insert_rewrite_rule global_known_values $
                       getVariableReplacements ruleset
          where
            insert_rewrite_rule (v, e) m =
              IntMap.insert (fromIdent $ varID v) (InlinedValue e) m

    let env = LREnv { lrIdSupply = var_supply
                    , lrRewriteRules = ruleset
                    , lrKnownValues = known_values
                    , lrTypeEnv = tenv
                    , lrDictEnv = denv
                    , lrIntEnv = ienv
                    }
    runLR (rwModule mod) env

rewriteWithGeneralRules, rewriteWithParallelRules, rewriteWithSequentialRules
  :: Module Mem -> IO (Module Mem)

rewriteWithGeneralRules = rewriteLocalExpr generalRewrites

rewriteWithParallelRules = rewriteLocalExpr rules 
  where
    rules = combineRuleSets [generalRewrites, parallelizingRewrites]

rewriteWithSequentialRules = rewriteLocalExpr rules 
  where
    rules = combineRuleSets [generalRewrites, sequentializingRewrites]
