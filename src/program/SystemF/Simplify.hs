{-| The simplifier.

The simplifier makes a forward sweep through a program, more or less in
execution order, and tries to statically evaluate what it can.

This sweep performs copy propagation, constant propagation,
beta reduction (includes inlining), case-of-known-value elimination,
and some local expression reordering.
-}

{-# LANGUAGE TypeSynonymInstances, FlexibleContexts, Rank2Types #-}
module SystemF.Simplify (rewriteLocalExpr)
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
import SystemF.Floating
import SystemF.MemoryIR
import SystemF.Syntax
import SystemF.Rename
import SystemF.Rewrite
import SystemF.TypecheckMem(functionType)
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

    -- | Information about the values stored in variables
  , lrKnownValues :: IntMap.IntMap KnownValue
    
    -- | Types of variables
  , lrTypeEnv :: TypeEnv
    
  , lrDictEnv :: MkDictEnv
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

instance ReprDictMonad LR where
  withVarIDs f = LR $ \env -> runLR (f $ lrIdSupply env) env
  withTypeEnv f = LR $ \env -> runLR (f $ lrTypeEnv env) env
  withDictEnv f = LR $ \env -> runLR (f $ lrDictEnv env) env
  localDictEnv f m = LR $ \env ->
    let env' = env {lrDictEnv = f $ lrDictEnv env}
    in runLR m env'

liftFreshVarM :: FreshVarM a -> LR a
liftFreshVarM m = LR $ \env -> do
  runFreshVarM (lrIdSupply env) m

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

-- | Add a variable's value to the environment, if known
withMaybeValue :: Var -> MaybeValue -> LR a -> LR a
withMaybeValue _ Nothing m = m
withMaybeValue v (Just val) m = withKnownValue v val m

-- | Add a function definition's value to the environment
withDefValue :: Def Mem -> LR a -> LR a
withDefValue (Def v f) m =
  let fun_info = funInfo $ fromFunM f
  in withKnownValue v (ComplexValue (Just v) Nothing $ FunValue fun_info f) m

-- | Add a function definition to the environment, but don't inline it
withUninlinedDefValue :: Def Mem -> LR a -> LR a
withUninlinedDefValue (Def v f) m =
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
assumeDef (Def v f) m = assume v (BoxRT ::: functionType f) m

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

-------------------------------------------------------------------------------
-- Inlining

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
      -- Float let-bindings out of the RHS.  Don't float this let-binding.
      (rhs_context, flattened_rhs) <- delveExp input_context rhs
      
      let replaced_let = ExpM $ LetE inf bind flattened_rhs body
      return (rhs_context, replaced_let)
      

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
  return $ applyContext ctx ex'

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

-- | Rewrite a list of expressions that are in the same scope,
--   such as arguments of a function call.
rwExps :: [ExpM] -> LR ([ExpM], [MaybeValue])
rwExps es = mapAndUnzipM rwExp es

rwExpReturn (exp, val) = return (exp, val)
    
-- | Rewrite a variable expression and compute its value.
rwVar original_expression inf v =
  rwExpReturn . rewrite =<< lookupKnownValue v
  where
    rewrite (Just val)
        -- Replace with an inlined or trivial value
      | Just (inl_value, val') <- asInlinedValue val = (inl_value, Just val')
      
      | Just cheap_value <- asTrivialValue val = (cheap_value, Just val)

        -- Otherwise, don't inline, but propagate the value
      | otherwise = (original_expression, Just val)
    rewrite Nothing =
      -- Set up for copy propagation
      (original_expression, Just $ VarValue inf v)

rwApp :: ExpInfo -> ExpM -> [TypM] -> [ExpM] -> LR (ExpM, MaybeValue)
rwApp inf op ty_args args = do
  (op', op_val) <- rwExp op
  rwAppWithOperator inf op' op_val ty_args args

-- | Rewrite an application, depending on what the operator is.
--   The operator has been simplified, but the arguments have not.
--
--   This function is usually called from 'rwApp'.  It calls itself 
--   recursively to flatten out curried applications.
rwAppWithOperator inf op' op_val ty_args args =
  -- First, try to uncurry this application
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
       of Just (ComplexValue _ _ (FunValue _ funm@(FunM fun))) ->
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
                
            -- Try to rewrite this application
            rewritten <- liftFreshVarM $
                         rewriteApp tenv inf op_var ty_args args
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
      (args', arg_values) <- rwExps args
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
    stored_value [_, Just stored_value, _] =
      Just $ complexKnownValue $ StoredValue Value stored_value
    stored_value [_, _, _] = Nothing
    stored_value [_, Just stored_value] =
      -- When applied to an argument, this will store a value
      Just $ complexKnownValue $
      WriterValue $ complexKnownValue $
      StoredValue Value stored_value
    stored_value [_, _] = Nothing
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
    loaded_value [_, addr_value] =
      case addr_value 
      of Just (ComplexValue _ _ (StoredValue Value val)) ->
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
        of Just (ComplexValue _ _ (StoredValue Boxed val)) -> Just val
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
  let new_exp = ExpM $ AppE inf op' ty_args args'
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

rwLet inf bind val body =       
  case bind
  of MemVarP bind_var bind_rtype uses -> do
       (val', val_value) <- rwExp val
       
       -- If the variable is used exactly once, then inline it.
       -- Otherwise, propagate the variable's known value.
       let local_val_value =
             case patMUses bind
             of One -> Just $ setInlinedValue bind_var val' val_value
                Many -> fmap (setTrivialValue bind_var) val_value

       -- Add the local variable to the environment while rewriting the body
       (body', body_val) <-
         assumePattern bind $
         withMaybeValue bind_var local_val_value $
         rwExp body
       
       let ret_val = mask_local_variable bind_var body_val
       rwExpReturn (ExpM $ LetE inf bind val' body', ret_val)

     LocalVarP bind_var bind_type dict uses -> do
       (dict', _) <- rwExp dict

       -- Add the variable to the environment while rewriting the rhs
       (val', val_value) <-
         assume bind_var (OutRT ::: bind_type) $ rwExp val

       -- Add the local variable to the environment while rewriting the body
       (body', body_val) <-
         assume bind_var (ReadRT ::: bind_type) $
         withMaybeValue bind_var val_value $
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

rwLetrec inf defs body = withDefs defs $ \defs' -> do
  (body', body_value) <- rwExp body
      
  let local_vars = Set.fromList [v | Def v _ <- defGroupMembers defs']
      ret_value = forgetVariables local_vars =<< body_value
  rwExpReturn (ExpM $ LetfunE inf defs' body', ret_value)

rwCase inf scrut alts = do
  (scrut', scrut_val) <- rwExp scrut
  
  tenv <- getTypeEnv
  case scrut' of
    ExpM (AppE _ (ExpM (VarE _ op_var)) ty_args args)
      | Just (type_con, data_con) <- lookupDataConWithType op_var tenv -> do
          -- Eliminate case-of-constructor expressions using the actual
          -- argument values.  We can eliminate case statements this way
          -- even when we can't compute known values for the fields.
          let altm = find_alternative op_var
              ex_args = drop (length $ dataConPatternParams data_con) ty_args
          m_elim <- elimCaseAlternative True inf altm ex_args (map Just args)
          case m_elim of
            Just eliminated_case -> rwExp eliminated_case
            Nothing  -> no_eliminate scrut' [altm]
    _ -> case scrut_val
         of Just (ComplexValue _ _ (DataValue _ con _ ex_args margs)) -> do
              -- Case of known value.
              -- Select the appropriate alternative and discard others.
              -- If possible, eliminate the expression.
              let altm = find_alternative con
                  arg_vals = map (>>= asTrivialValue) margs
              m_elim <- elimCaseAlternative False inf altm ex_args arg_vals
              case m_elim of
                Just eliminated_case -> rwExp eliminated_case
                Nothing -> no_eliminate scrut' [altm]
            _ -> no_eliminate scrut' alts
  where
    -- Find the alternative matching constructor @con@
    find_alternative con =
      case find ((con ==) . altConstructor . fromAltM) alts
      of Just alt -> alt
         Nothing -> internalError "rwCase: Missing alternative"

    -- Cannot eliminate this case statement.  Possibly eliminated
    -- some case alternatives.
    no_eliminate scrut' reduced_alts = do
      alts' <- mapM (rwAlt scrutinee_var) reduced_alts
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
--   If @bind_reference_values@ is 'True', then write references may be
--   given for the writable case fields, and they should be bound to local
--   variables.  Otherwise, those fields won't be bound.
elimCaseAlternative :: Bool -> ExpInfo -> AltM -> [TypM] -> [Maybe ExpM]
                    -> LR (Maybe ExpM)
elimCaseAlternative bind_reference_values inf (AltM alt) ex_args args
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
      | okay_for_reference_binding = do
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
      | otherwise = mzero   -- Cannot bind this pattern
      where
        -- We can only bind value and boxed parameters this way
        okay_for_value_binding =
          case patMRepr pat
          of ValPT _ -> True
             BoxPT -> True
             _ -> False

        okay_for_reference_binding =
          bind_reference_values &&
          case patMRepr pat of {ReadPT -> True; _ -> False}

    bind_field _ _ = internalError "rwCase: Unexpected pattern"

rwAlt :: Maybe Var -> AltM -> LR AltM
rwAlt scr (AltM (Alt con tyArgs exTypes params body)) = do
  -- If we're going to record a known value for the scrutinee, 
  -- convert wildcard to non-wildcard patterns.  This increases the
  -- usefulness of recording known values.
  labeled_params <-
    if isJust scr
    then mapM labelParameter params
    else return params

  assume_params labeled_params $ do
    (body', _) <- rwExp body
    return $ AltM $ Alt con tyArgs exTypes labeled_params body'
  where
    assume_params labeled_params m = do
      tenv <- getTypeEnv
      let with_known_value = assume_scrutinee tenv labeled_params m
          with_params = assumePatterns labeled_params with_known_value
          with_ty_params = foldr assumeTyPatM with_params exTypes
      with_ty_params
    
    -- If the scrutinee is a variable, add its known value to the environment.
    -- It will be used if the variable is inspected again. 
    assume_scrutinee tenv labeled_params m =
      case scr
      of Just scrutinee_var ->
           let ex_args = [v | TyPatM v _ <- exTypes]
               arg_values = map (mk_arg . patMVar) labeled_params
               Just (data_type, dcon_type) = lookupDataConWithType con tenv
               data_value = patternValue defaultExpInfo data_type dcon_type tyArgs ex_args arg_values
           in withMaybeValue scrutinee_var data_value m
         Nothing -> m
      where
        mk_arg (Just var) = Just (VarValue defaultExpInfo var)
        mk_arg Nothing =
          -- It would be safe to return Nothing here.
          -- However, we tried to give every parameter a variable name,
          -- so this shouldn't be Nothing.
          internalError "rwAlt"

-- | Ensure that the parameter binds a variable.
labelParameter param = 
  case param
  of MemVarP {} -> return param
     LocalVarP {} -> return param
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
rwDef (Def v f) = do
  f' <- rwFun f
  return (Def v f')

rwExport :: Export Mem -> LR (Export Mem)
rwExport (Export pos spec f) = do
  f' <- rwFun f
  return (Export pos spec f')

-- | Rewrite a definition group.  Then, add the defined functions to the
--   environment and rewrite something else.
withDefs :: DefGroup (Def Mem) -> (DefGroup (Def Mem) -> LR a) -> LR a
withDefs defs k = assumeDefs defs $ do
  -- Don't add values to the environment -- we don't want recursive inlining
  defs' <- mapM rwDef defs
  withDefValues defs' $ k defs'

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

rewriteLocalExpr :: Module Mem -> IO (Module Mem)
rewriteLocalExpr mod = do
  withTheNewVarIdentSupply $ \var_supply -> do
    tenv <- readInitGlobalVarIO the_memTypes
    denv <- runFreshVarM var_supply createDictEnv
    let global_known_values = initializeKnownValues tenv
    let env = LREnv { lrIdSupply = var_supply
                    , lrKnownValues = global_known_values
                    , lrTypeEnv = tenv
                    , lrDictEnv = denv
                    }
    runLR (rwModule mod) env


