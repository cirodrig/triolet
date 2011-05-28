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
import System.IO

import Builtins.Builtins
import SystemF.Build
import SystemF.Demand
import SystemF.DemandAnalysis
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

  assume v rt m = LR $ \env ->
    let env' = env {lrTypeEnv = insertType v rt $ lrTypeEnv env}
    in runLR m env'

instance EvalMonad LR where
  liftTypeEvalM m = LR $ \env -> do
    runTypeEvalM m (lrIdSupply env) (lrTypeEnv env)



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

-- | Add a pattern-bound variable to the environment.  
--   This adds the variable's type to the environment and
--   its dictionary information if it is a dictionary.
--   The pattern must not be a local variable pattern.
assumePattern :: PatM -> LR a -> LR a
assumePattern pat m =
  saveReprDictPattern pat $ assumeBinder (patMBinder pat) m

assumePatterns :: [PatM] -> LR a -> LR a
assumePatterns pats m = foldr assumePattern m pats

assumeTyPatM :: TyPatM -> LR a -> LR a
assumeTyPatM (TyPatM b) m = assumeBinder b m

assumeTyPatMs :: [TyPatM] -> LR a -> LR a
assumeTyPatMs typats m = foldr assumeTyPatM m typats

-- | Add the function definition types to the environment
assumeDefs :: DefGroup (Def Mem) -> LR a -> LR a
assumeDefs defs m = foldr assumeDef m (defGroupMembers defs)

assumeDef :: Def Mem -> LR a -> LR a
assumeDef (Def v _ f) m = assume v (functionType f) m

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
rwInferExpType :: ExpM -> LR Type
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
  of Just (dcon, _, _, args) ->
       -- This is a data constructor application.
       -- Test its fields.
       let field_demands =
             case specificity dmd
             of Decond _ spcs -> map (Dmd (multiplicity dmd)) spcs
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
betaReduce :: EvalMonad m =>
              ExpInfo -> FunM -> [TypM] -> [ExpM] -> m ExpM
betaReduce inf (FunM fun) ty_args args
  | length ty_args /= length (funTyParams fun) =
      internalError "betaReduce: Not implemented for partial type application"
  | otherwise = do
      -- Substitute type arguments for type parameters
      let type_subst =
            substitution [(tv, t)
                         | (TyPatM (tv ::: _), TypM t) <-
                             zip (funTyParams fun) ty_args]

      -- Apply substitution to parameters and body
      substitutePatMs type_subst (funParams fun) $ \subst params -> do
        body <- substitute subst $ funBody fun
        ret <- substitute subst $ funReturn fun
          
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
    
    bind_parameter (param, arg) body 
      | isDeadPattern param = body
      | otherwise = ExpM $ LetE inf param arg body

-------------------------------------------------------------------------------
-- Local restructuring
    
-- Before trying to simplify an expression, we restruture it to increase the 
-- scopes of temporary variables.  Let-expressions are floated out from the
-- RHS of other let expressions and from inside function calls.

-- | Flatten an expression until it reaches a fixed point or until the
--   expression satisfies the given test.
--
--   Unlike 'flattenExp', the RHS and body of a let expression will be
--   flattened.  In 'flattenExp' only the RHS is flattened.
--
--   For example
--
-- > let x = (let y = A in let z = B in C) in D
--
--   becomes
--
-- > let x = C in D   [let z = B, let y = A]

recFlattenExp :: ExpM -> LR (Context, ExpM)
recFlattenExp e = flattenExp e >>= continue
  where
    continue ret@([], e') = return ret
    continue (ctx1,   e') = do
      (ctx2, e'') <- assumeContext ctx1 $ recFlattenExp e'
      return (ctx2 ++ ctx1, e'')

-- | Flatten an expression.  Local let-bindings and case-bindings are 
--   floated outward.
flattenExp :: ExpM -> LR (Context, ExpM)
flattenExp (ExpM expression) =
  case expression
  of LetE inf pat rhs body -> flattenLetExp inf pat rhs body
     CaseE inf scr alts -> flattenCaseExp inf scr alts
     AppE inf op ty_args args -> flattenAppExp inf op ty_args args
     _ -> return ([], ExpM expression)
  where
    debug :: LR (Context, ExpM) -> LR (Context, ExpM)
    debug m = do
      ret@(c, e) <- m
      traceShow (text "flattenExp" <+> pprExp (applyContext c e)) $ return ret

flattenExps :: [ExpM] -> LR (Context, [ExpM])
flattenExps es = do (ctxs, es') <- mapAndUnzipM flattenExp es
                    return (concat ctxs, es')

flattenLetExp inf pat rhs body = do
  -- Flatten the RHS.  Since the body of the RHS will be the new RHS,
  -- make sure it's completely flattened.
  (rhs_context, flat_rhs) <- recFlattenExp rhs

  -- Float this binding
  (floated, rn) <- freshenContextExp $ LetCtx inf pat flat_rhs

  let output_context = contextItem floated : rhs_context
      rn_body = rename rn body
  return (output_context, rn_body)

flattenCaseExp inf scr alts = do
  -- Perform floating in the scrutinee
  (float_scr_ctx, floated_scr) <- do
    -- First flatten the scrutinee
    (scr_ctx, flat_scr) <- recFlattenExp scr
    
    -- Bind the scrutinee to a new variable and float the binding outward,
    -- unless we have a reason to leave the scrutinee in place
    try_to_float_scrutinee scr_ctx flat_scr

  let simplified_case = ExpM $ CaseE inf floated_scr alts

  -- Is this case binding suitable for floating?
  case asCaseCtx simplified_case of
    Nothing ->
      return (float_scr_ctx, simplified_case)

    Just (case_ctx, case_body) -> do
      -- Float the case binding.  Rename and return the body.
      (rn_case_ctx, rn) <- freshenContextExp case_ctx
      let context = contextItem rn_case_ctx : float_scr_ctx
      return (context, rename rn case_body)
  where
    -- If it's a good idea to float the scrutinee, then float the scrutinee.
    -- Return the context and scrutinee after floating has been performed.
    try_to_float_scrutinee scr_ctx flattened_scr = do
      tenv <- getTypeEnv
      if isTrivialExp flattened_scr || isDataConAppM tenv flattened_scr
        then return (scr_ctx, flattened_scr)
        else float_scrutinee scr_ctx flattened_scr

    -- Scrutinee should be floated
    float_scrutinee scr_ctx flattened_scr = assumeContext scr_ctx $ do
      -- Create a new variable that will bind the scrutinee
      scr_var <- newAnonymousVar ObjectLevel
      scr_type <- rwInferExpType flattened_scr

      -- Construct demand information for the new scrutinee variable.
      -- The scrutinee variable is used exactly once, in place of the
      -- original scrutinee expression.  Demand information can be
      -- reconstructed from the bindings in the case statement.
      let demand = Dmd OnceSafe (altListSpecificity alts)
          binder = setPatMDmd demand $ patM (scr_var ::: scr_type)
      return (contextItem (LetCtx inf binder flattened_scr) : scr_ctx,
              ExpM $ VarE inf scr_var)


flattenAppExp inf op ty_args args = do
  (ctx1, oper') <- flattenExp op
  (ctx2, args') <- flattenExps args
  let replaced_app = ExpM $ AppE inf oper' ty_args args'
  return (ctx2 ++ ctx1, replaced_app)

restructureExp :: ExpM -> LR ExpM
restructureExp ex = do
  (ctx, ex') <- flattenExp ex
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
rwExp expression = debug "rwExp" expression $ do
  -- Flatten nested let and case statements
  ex1 <- restructureExp expression

  -- Simplify subexpressions
  case fromExpM ex1 of
    VarE inf v -> rwVar ex1 inf v
    LitE inf l -> rwExpReturn (ex1, Just $ LitValue inf l)
    UTupleE inf args -> rwUTuple inf args
    AppE inf op ty_args args -> rwApp inf op ty_args args
    LamE inf fun -> do
      fun' <- rwFun fun
      rwExpReturn (ExpM $ LamE inf fun', Just $ complexKnownValue $ FunValue inf fun')
    LetE inf bind val body -> rwLet inf bind val body
    LetfunE inf defs body -> rwLetrec inf defs body
    CaseE inf scrut alts -> rwCase inf scrut alts
    ExceptE _ _ -> rwExpReturn (ex1, Nothing)
  where
    debug l e m = traceShow (text l <+> (pprExp e)) m
    {-
    debug m = do
      ret@(e, _) <- m
      traceShow (text "rwExp" <+> (pprExp expression $$ text "----" $$ pprExp e)) $ return ret
    -}

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
      | Just inl_value <- asInlinedValue val =
          rwExp inl_value

      | Just cheap_value <- asTrivialValue val =
          rwExpReturn (cheap_value, Just val)

        -- Otherwise, don't inline, but propagate the value
      | otherwise = rwExpReturn (original_expression, Just val)
    rewrite Nothing =
      -- Set up for copy propagation
      rwExpReturn (original_expression, Just $ VarValue inf v)

rwUTuple inf args = do
  (args', arg_values) <- mapAndUnzipM rwExp args
  
  let ret_value = tupleConValue inf arg_values
      ret_exp = ExpM $ UTupleE inf args'
  return (ret_exp, ret_value)

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
            | op_var `isPyonBuiltin` the_copy ->
                case ty_args
                of [ty] -> rwCopyApp inf op' ty args

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
      tenv <- getTypeEnv

      -- Try to eta-reduce writer arguments, because this increases the
      -- likelihood that we can value-propagate them
      (field_types, _) <-
        instantiateDataConTypeWithExistentials data_con (map fromTypM ty_args)
          
      -- Eta-reduce writer arguments, leave other arguments alone
      let extended_field_kinds =
            map Just (dataConFieldKinds tenv data_con) ++ repeat Nothing
          eta_reduced_args = zipWith eta_reduce_arg args extended_field_kinds
            where
              -- Only eta-reduce known writer arguments
              eta_reduce_arg arg (Just BareK) = eta_reduce arg
              eta_reduce_arg arg _ = arg

              eta_reduce (ExpM (LamE inf f)) =
                etaReduceSingleLambdaFunction inf f
              eta_reduce e = e

      -- Simplify arguments
      (args', arg_values) <- rwExps eta_reduced_args
      
      -- Construct a value from this expression
      let new_exp = ExpM $ AppE inf op' ty_args args'
          new_value = dataConValue inf tenv type_con data_con ty_args arg_values
      return (new_exp, new_value)

    -- Inline the function call and continue to simplify it.
    -- The arguments will be processed after inlining.
    inline_function_call funm =
      rwExp =<< betaReduce inf funm ty_args args

-- | Attempt to statically evaluate a copy
rwCopyApp inf copy_op ty args = do
  whnf_type <- reduceToWhnf (fromTypM ty)
  case fromVarApp whnf_type of
    Just (op, [val_type])
      | op `isPyonBuiltin` the_Stored ->
          case args
          of [repr, src] ->
               copyStoredValue inf val_type repr src
             _ ->
               internalError "rwCopyApp: Unexpected number of arguments"
    _ -> do
      (args', arg_values) <- rwExps args
  
      let new_exp = copy_expression args' arg_values
          new_value = copied_value arg_values
      return (new_exp, new_value)
  where
    -- Do we know what was stored here?
    copied_value [_, Just src_val, Just dst_val] =
      -- Reference the source value instead of the destination value
      Nothing
    copied_value [_, _, _] = Nothing
    copied_value [_, Just src_val] =
      Just $ complexKnownValue $ WriterValue src_val
    copied_value [_, _] = Nothing
    copied_value _ =
      internalError "rwCopyApp: Wrong number of arguments in call"
    
    -- Transform a copy into a store if the source value is known
    {-
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
    -}

    -- Otherwise return a copy expression
    copy_expression args _ = ExpM $ AppE inf copy_op [ty] args
      
-- | Rewrite a copy of a Stored value to a deconstruct and construct operation
copyStoredValue inf val_type repr arg = do
  tmpvar <- newAnonymousVar ObjectLevel
  let stored_op = ExpM $ VarE defaultExpInfo (pyonBuiltin the_stored)
      make_value = ExpM $ AppE inf stored_op [TypM val_type]
                   [ExpM $ VarE inf tmpvar]
      alt = AltM $ DeCon { altConstructor = pyonBuiltin the_stored
                         , altTyArgs = [TypM val_type]
                         , altExTypes = []
                         , altParams = [setPatMDmd (Dmd OnceSafe Used) $
                                        patM (tmpvar ::: val_type)]
                         , altBody = make_value}
      new_expr = ExpM $ CaseE inf arg [alt]
  rwExp new_expr

rwLet inf bind@(PatM (bind_var ::: bind_rtype) _) val body = do
  tenv <- getTypeEnv
  case worthPreInlining tenv (patMDmd bind) val of
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

rwLetrec inf defs body = withDefs defs $ \defs' -> do
  (body', body_value) <- rwExp body
      
  let local_vars = Set.fromList $ map definiendum $ defGroupMembers defs'
      ret_value = forgetVariables local_vars =<< body_value
  rwExpReturn (ExpM $ LetfunE inf defs' body', ret_value)

rwCase inf scrut alts = do
  tenv <- getTypeEnv
  rwCase1 tenv inf scrut alts

-- Special-case handling of the 'boxed' constructor.  This constructor cannot
-- be eliminated.  Instead, its value is propagated, and we hope that the case
-- statement becomes dead code.
rwCase1 _ inf scrut alts
  | [alt@(AltM (DeCon {altConstructor = con}))] <- alts,
    con `isPyonBuiltin` the_boxed = do
      -- Rewrite the scrutinee
      (scrut', scrut_val) <- rwExp scrut

      -- Rewrite the case alternative
      let scrutinee_var =
            case scrut'
            of ExpM (VarE _ scrut_var) -> Just scrut_var
               _ -> Nothing
      let field_val =
            case scrut_val
            of Just (ComplexValue _ (DataValue { dataValueType = ConValueType c _ _
                                               , dataFields = [f]}))
                 | c `isPyonBuiltin` the_boxed -> f
               _ -> Nothing

      alt' <- rwAlt scrutinee_var (Just ([], [field_val])) alt

      -- Rebuild a new case expression
      return (ExpM $ CaseE inf scrut' [alt'], Nothing)

-- If this is a case of data constructor, we can unpack the case expression
-- before processing the scrutinee.
rwCase1 tenv inf scrut alts
  | Just (dcon, ty_args, ex_args, args) <- unpackDataConAppM tenv scrut =
      let alt = findAlternative alts $ dataConCon dcon
      in eliminateCaseWithExp tenv dcon (map TypM ex_args) args alt

-- Simplify the scrutinee, then try to simplify the case statement.
rwCase1 tenv inf scrut alts = do
  -- Simplify scrutinee
  (scrut', scrut_val) <- rwExp scrut
  let (arg_con, arg_ex_types, arg_values) = unpack_scrut_val scrut_val

  -- Try to deconstruct the new scrutinee
  case unpackDataConAppM tenv scrut' of
    Just (data_con, ty_args, ex_args, args) 
      | isJust arg_con && arg_con /= Just (dataConCon data_con) ->
          internalError "rwCase: Inconsistent constructor value"
      | otherwise ->
          let args_and_values = zip args arg_values
              alt = findAlternative alts $ dataConCon data_con
          in eliminateCaseWithSimplifiedExp
             tenv data_con (map TypM ex_args) args_and_values alt
    _ ->
      -- Can't deconstruct.  Propagate values and rebuild the case statement.
      rebuild_case scrut' arg_con arg_ex_types arg_values 
  where
    -- Given the value of the scrutinee, try to get the fields' values
    unpack_scrut_val (Just (ComplexValue _ (DataValue _ (ConValueType con _ ex_ts) vs))) =
      (Just con, Just ex_ts, vs)
    
    unpack_scrut_val _ =
      (Nothing, Nothing, repeat Nothing)
    
    rebuild_case scrut' arg_con arg_ex_types arg_values = do
      let new_alts =
            -- If the scrutinee has a known constructor,
            -- drop non-matching case alternatives
            case arg_con
            of Nothing -> alts
               Just c  -> [findAlternative alts c]
          scrut_var =
            -- If the scrutinee is a variable, it will be assigned a known
            -- value while processing each alternative
            case scrut'
            of ExpM (VarE _ v) -> Just v
               _               -> Nothing
          known_values =
            case arg_ex_types
            of Nothing -> Nothing
               Just [] -> Just ([], arg_values)

               -- The case alternative will bind existential types to
               -- fresh variables.  If there are existential types, then field
               -- values cannot be propagated because they'll have their
               -- original types, not the fresh type names.
               Just _  -> Nothing
      alts' <- mapM (rwAlt scrut_var known_values) new_alts
      rwExpReturn (ExpM $ CaseE inf scrut' alts', Nothing)

-- | Find the alternative matching constructor @con@
findAlternative :: [AltM] -> Var -> AltM
findAlternative alts con =
  case find ((con ==) . altConstructor . fromAltM) alts
  of Just alt -> alt
     Nothing -> internalError "rwCase: Missing alternative"

-- | Given the parts of a data constructor application and a list of case
--   alternatives, eliminate the case statement.
--
--   This creates a new expression, then simplifies it.
eliminateCaseWithExp :: TypeEnv
                     -> DataConType
                     -> [TypM]
                     -> [ExpM]
                     -> AltM
                     -> LR (ExpM, MaybeValue)
eliminateCaseWithExp
  tenv dcon_type ex_args initializers (AltM alt)
  | length (getAltExTypes alt) /= length ex_args =
      internalError "rwCase: Wrong number of type parameters"
  | length (altParams alt) /= length initializers =
      internalError "rwCase: Wrong number of fields"
  | otherwise =
      -- Substitute known types for the existential type variables
      substitutePatMs ex_type_subst (altParams alt) $ \subst params -> do
        body <- substitute subst (altBody alt)

        binders <-
          let field_kinds = dataConFieldKinds tenv dcon_type
          in sequence [makeCaseInitializerBinding k p i 
                      | (k, p, i) <- zip3 field_kinds params initializers]

        -- Continue simplifying the new expression
        rwExp $ applyCaseElimBindings binders body
  where
    ex_type_subst =
      substitution [(v, ex_type)
                   | (TyPatM (v ::: _), TypM ex_type) <-
                       zip (getAltExTypes alt) ex_args]

eliminateCaseWithSimplifiedExp :: TypeEnv
                               -> DataConType
                               -> [TypM]
                               -> [(ExpM, MaybeValue)]
                               -> AltM
                               -> LR (ExpM, MaybeValue)
eliminateCaseWithSimplifiedExp
  tenv dcon_type ex_args initializers (AltM alt)
  | length (getAltExTypes alt) /= length ex_args =
      internalError "rwCase: Wrong number of type parameters"
  | length (altParams alt) /= length initializers =
      internalError "rwCase: Wrong number of fields"
  | otherwise =
      -- Substitute known types for the existential type variables
      substitutePatMs ex_type_subst (altParams alt) $ \subst params -> do
        body <- substitute subst (altBody alt)

        binders <-
          let field_kinds = dataConFieldKinds tenv dcon_type
          in sequence [makeCaseInitializerBinding k p i 
                      | (k, p, (i, _)) <- zip3 field_kinds params initializers]

        let values = [(patMVar p, mv)
                     | (p, (_, mv)) <- zip params initializers]

        -- Add known values to the environment.  Simplify the body expression.
        (body', _) <-
          assumePatterns params $ with_values values $ rwExp body
        
        -- Bind local variables 
        return (applyCaseElimBindings binders body', Nothing)
  where
    with_values vs e = foldr (uncurry withMaybeValue) e vs
    ex_type_subst =
      substitution [(v, ex_type)
                   | (TyPatM (v ::: _), TypM ex_type) <-
                       zip (getAltExTypes alt) ex_args]

newtype CaseElimBinding = CaseElimBinding (ExpM -> ExpM)

applyCaseElimBindings :: [CaseElimBinding] -> ExpM -> ExpM
applyCaseElimBindings bs e = foldr apply_binding e bs
  where
    apply_binding (CaseElimBinding f) e = f e

makeCaseInitializerBinding :: BaseKind -> PatM -> ExpM -> LR CaseElimBinding
makeCaseInitializerBinding BareK param initializer = do
  tmpvar <- newAnonymousVar ObjectLevel
  return $ write_box tmpvar
  where
    -- Write into a box, then read the box's contents
    write_box tmpvar = CaseElimBinding $ \body ->
      letViaBoxed (patMBinder param) initializer body

makeCaseInitializerBinding _ param initializer = return let_binding
  where
    let_binding = CaseElimBinding $ \body ->
      ExpM $ LetE defaultExpInfo param initializer body

rwAlt :: Maybe Var -> Maybe ([TypM], [MaybeValue]) -> AltM -> LR AltM
rwAlt scr m_values (AltM alt) = 
  case alt
  of DeCon con tyArgs exTypes params body -> do
       -- DEBUG: Print known values
       -- liftIO $ print $ text "rwAlt" <+>
       --                  maybe empty (vcat . map pprMaybeValue . snd) m_values
       
       -- If the scrutinee is a variable,
       -- add its known value to the environment
       tenv <- getTypeEnv
       let ex_args = [v | TyPatM (v ::: _) <- exTypes]
           arg_values = zipWith mk_arg values params
           Just (data_type, dcon_type) = lookupDataConWithType con tenv
           data_value =
             patternValue defaultExpInfo tenv data_type dcon_type tyArgs ex_args arg_values
           
           assume_scrutinee m =
             case scr
             of Just scrutinee_var -> withMaybeValue scrutinee_var data_value m
                Nothing -> m

       assume_scrutinee $ assume_params exTypes (zip values params) $ do
         (body', _) <- rwExp body
         return $ AltM $ DeCon con tyArgs exTypes params body'

     DeTuple params body -> do
       -- If the scrutinee is a variable, add its known value to the environment
       let arg_values = zipWith mk_arg values params
           data_value = tuplePatternValue defaultExpInfo arg_values
           assume_scrutinee m =
             case scr
             of Just scrutinee_var -> withMaybeValue scrutinee_var data_value m
                Nothing -> m
       assume_scrutinee $ assume_params [] (zip values params) $ do
         (body', _) <- rwExp body
         return $ AltM $ DeTuple params body'
  where
    -- Get the known values of the fields
    values = 
      case m_values
      of Just (ex_args, given_values)
           | not $ null ex_args ->
               -- Not implemented.
               -- To implement this, we need to unify existential
               -- variable names appearing in the values with
               -- existential variable names appearing in the
               -- pattern.
               repeat Nothing
           | otherwise ->
               given_values
         _ -> repeat Nothing

    -- Add existential types, paramters, and known values to the environment
    assume_params ex_types params_and_values m = do
      tenv <- getTypeEnv
      let with_params = assume_parameters params_and_values m
          with_ty_params = foldr assumeTyPatM with_params ex_types
      with_ty_params
      
    assume_parameters labeled_params m = foldr assume_param m labeled_params
    
    -- Add a parameter and its value to the environment
    assume_param (maybe_value, param) m =
      assumePattern param $ withMaybeValue (patMVar param) maybe_value m
    
    -- Create a KnownValue argument for a data field.  Use the previous known
    -- value if available, or the variable that the field is bound to otherwise
    mk_arg maybe_val pat =
      case maybe_val
      of Just val -> Just (setTrivialValue (patMVar pat) val)
         Nothing  -> Just (VarValue defaultExpInfo $ patMVar pat)

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
