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
  }

newtype LR a = LR {runLR :: LREnv -> IO a}

instance Monad LR where
  return x = LR (\_ -> return x)
  m >>= k = LR $ \env -> do
    x <- runLR m env
    runLR (k x) env
    
instance Supplies LR VarID where
  fresh = LR (\env -> supplyValue (lrIdSupply env))
  supplyToST = undefined

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
  in withKnownValue v (ComplexValue (Just v) $ FunValue fun_info f) m

withDefValues :: DefGroup (Def Mem) -> LR a -> LR a
withDefValues defs m = foldr withDefValue m $ defGroupMembers defs

-- | Get the current type environment
getTypeEnv :: LR TypeEnv
getTypeEnv = LR $ \env -> return (lrTypeEnv env)

-- | Add a variable's type to the environment 
assume :: Var -> ReturnType -> LR a -> LR a
assume v rt m = LR $ \env ->
  let env' = env {lrTypeEnv = insertType v rt $ lrTypeEnv env}
  in runLR m env'

-- | Add a variable's type to the environment 
assumeParamType :: Var -> ParamType -> LR a -> LR a
assumeParamType v (prepr ::: ptype) m =
  assume v (paramReprToReturnRepr prepr ::: ptype) m

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


-------------------------------------------------------------------------------
-- Known values

{-
-- | A value that is known (or partially known) at compile time.
--
--   This is used for various kinds of compile-time partial evaluation:
--   inlining, constant propagation, copy propagation, and case of
--   known value elimination.
--
--   The 'cheapValue', if available, is a value that should be inlined
--   even if it doesn't enable any optimizations.
data KnownValue =
    -- | A function, which may be inlined where it is used.
    FunValue
    { knownInfo :: ExpInfo
    , _cheapValue :: !(Maybe ExpM)
    , knownFun  :: !FunM
    }

    -- | A fully applied data constructor.
    --
    --   In the case of reference objects, the fully applied constructor is
    --   a single-argument function that writes into its argument.
  | DataValue
    { knownInfo    :: ExpInfo 
    , _cheapValue :: !(Maybe ExpM)
    , knownDataCon :: !Var 
      -- | Representation of the constructed value, as it would be seen when
      --   inspected by a case statement.
    , knownRepr    :: !ReturnRepr
      -- | Type arguments, which should match a case alternative's
      --   'altTyArgs'.
    , knownTyArgs  :: [TypM] 
      -- | Existential types, one for each pattern in a
      --   case alternative's 'altExTypes'
    , knownExTypes :: [TypM] 
      -- | Data fields, one for each pattenr in a case
      -- alternative's 'altParams'
    , knownFields  :: [MaybeValue]
    }
    
    -- | A literal value.
  | LitValue
    { knownInfo :: ExpInfo
    , knownLit  :: Lit
    }
    
    -- | A variable reference, where nothing 
    --   further is known about what's assigned to the variable.  This is
    --   also used for data constructors that have not been applied to
    --   arguments.
    --
    --   Nullary data constructors are not described by a 'VarValue',
    --   but rather by a 'DataValue'.
  | VarValue
    { knownInfo :: ExpInfo
    , knownVar  :: !Var
    }
    
    -- | A heap state value.  Only side-effecting expressions return these.
  | KnownHeapState !HeapState
 
-- | A known state of the contents of memory
data HeapState =
  -- | A known value is stored in a known address
  StoredValue !KnownValue !Var

type MaybeValue = Maybe KnownValue

cheapValue :: KnownValue -> Maybe ExpM
cheapValue (FunValue {_cheapValue = v}) = v
cheapValue (DataValue {_cheapValue = v}) = v
cheapValue (LitValue inf l) = Just (ExpM $ LitE inf l)
cheapValue (VarValue inf v) = Just (ExpM $ VarE inf v)
cheapValue (KnownHeapState _) = Nothing

-- | Set the cheap value of a 'KnownValue', but only if it isn't already
--   assigned.
--
--   This is used on values that are assigned to let-expressions.
weakAssignCheapValue :: ExpM -> KnownValue -> KnownValue
weakAssignCheapValue new_value kv
  | isJust $ cheapValue kv = kv
  | otherwise =
      case kv
      of KnownHeapState _ -> kv -- Can't assign this a value
         _ -> kv {_cheapValue = Just new_value}

weakAssignCheapVarValue :: ExpInfo -> Var -> KnownValue -> KnownValue
weakAssignCheapVarValue inf v kv =
  weakAssignCheapValue (ExpM (VarE inf v)) kv

pprKnownValue :: KnownValue -> Doc
pprKnownValue kv =
  case kv
  of FunValue _ m_cheap_value f ->
       with_cheap_value m_cheap_value $ pprFun f
     DataValue _ m_cheap_value con _ ty_args ex_types fields ->
       let type_docs =
             map (text "@" <>) $ map (pprType . fromTypM) (ty_args ++ ex_types)
           field_docs = map pprMaybeValue fields
           data_doc =
             pprVar con <>
             parens (sep $ punctuate (text ",") $ type_docs ++ field_docs)
       in with_cheap_value m_cheap_value data_doc
     VarValue _ v -> pprVar v
     LitValue _ l -> pprLit l
     KnownHeapState _ -> text "(heap)"
  where
    with_cheap_value Nothing doc = doc
    with_cheap_value (Just e) doc =
      parens $ hang ((pprExp e) <+> text "=") 2 doc
     
pprMaybeValue :: MaybeValue -> Doc
pprMaybeValue Nothing = text "(?)"
pprMaybeValue (Just kv) = pprKnownValue kv

-- | Is the variable mentioned in the value?
--
--   Does not check data constructors.
knownValueMentions :: KnownValue -> Var -> Bool
knownValueMentions kv search_v =
  case kv
  of VarValue _ v -> v == search_v
     LitValue _ _ -> False
     FunValue _ cheap_value f ->
       search_v `Set.member` freeVariables cheap_value ||
       search_v `Set.member` freeVariables f
     DataValue _ cheap_value _ _ ty_args ex_types args ->
       search_v `Set.member` freeVariables cheap_value ||
       any (`typeMentions` search_v) (map fromTypM ty_args) ||
       any (`typeMentions` search_v) (map fromTypM ex_types) ||
       any (`maybeValueMentions` search_v) args
     KnownHeapState st ->
       heapStateMentions st search_v

-- | Is any of the variables mentioned in the value?
--
--   Does not check data constructors.
knownValueMentionsAny :: KnownValue -> Set.Set Var -> Bool
knownValueMentionsAny kv search_vs =
  case kv
  of VarValue _ v -> v `Set.member` search_vs
     LitValue _ _ -> False
     FunValue _ cheap_value f ->
       not (Set.null $ Set.intersection search_vs (freeVariables f)) ||
       not (Set.null $ Set.intersection search_vs (freeVariables cheap_value))
     DataValue _ cheap_value _ _ ty_args ex_types args ->
       not (Set.null $ Set.intersection search_vs (freeVariables cheap_value)) ||
       any (`typeMentionsAny` search_vs) (map fromTypM ty_args) ||
       any (`typeMentionsAny` search_vs) (map fromTypM ex_types) ||
       any (`maybeValueMentionsAny` search_vs) args
     KnownHeapState st ->
       heapStateMentionsAny st search_vs

maybeValueMentions :: MaybeValue -> Var -> Bool
maybeValueMentions Nothing _ = False
maybeValueMentions (Just kv) v = knownValueMentions kv v

maybeValueMentionsAny :: MaybeValue -> Set.Set Var -> Bool
maybeValueMentionsAny Nothing _ = False
maybeValueMentionsAny (Just kv) v = knownValueMentionsAny kv v

heapStateMentions st search_v =
  case st
  of StoredValue kv location ->
       location == search_v || kv `knownValueMentions` search_v

heapStateMentionsAny st search_vars =
  case st
  of StoredValue kv location ->
       location `Set.member` search_vars ||
       kv `knownValueMentionsAny` search_vars

-- | Given that this is the value of an expression, should we replace the  
--   expression with this value?
worthPropagating :: KnownValue -> Bool
worthPropagating kv = 
  case kv
  of FunValue {} -> True -- Always inline functions
     DataValue {knownFields = args} -> null args -- Inline nullary data values
     LitValue {} -> True
     VarValue {} -> True
     KnownHeapState {} -> False

-- | Convert a known value to an expression.  It's an error if the known
--   value cannot be converted (e.g. it's a data constructor with some
--   unknown fields).
knownValueExp :: KnownValue -> Maybe ExpM
knownValueExp kv = 
  case kv
  of VarValue inf v -> Just $ ExpM $ VarE inf v
     LitValue inf l -> Just $ ExpM $ LitE inf l
     FunValue _ (Just cheap_value) _ -> Just cheap_value
     FunValue inf Nothing f -> Just (ExpM $ LamE inf f)
     DataValue _ (Just cheap_value) _ _ _ _ _ -> Just cheap_value
     DataValue inf Nothing con _ ty_args ex_types args ->
       -- Get argument values.  All arguments must have a known value.
       case sequence $ map (knownValueExp =<<) args
       of Just arg_values ->
            Just $ ExpM $ AppE inf (ExpM $ VarE inf con) (ty_args ++ ex_types) arg_values
          Nothing -> Nothing
     KnownHeapState {} -> Nothing

-- | Remove references to any of the given variables in the known value
forgetVariables :: Set.Set Var -> MaybeValue -> MaybeValue
forgetVariables forget_vars mv = forget mv
  where
    forget Nothing = Nothing
    forget (Just kv) =
      case kv
      of VarValue _ v 
           | v `Set.member` forget_vars -> Nothing
           | otherwise -> Just kv
         LitValue _ _ -> Just kv
         FunValue inf cheap_value f
           | not (Set.null $ Set.intersection forget_vars (freeVariables f)) ->
               Nothing
           | otherwise ->
             let new_cheap_value =
                   if Set.null $ Set.intersection forget_vars (freeVariables cheap_value)
                   then cheap_value
                   else Nothing
             in Just $ FunValue inf new_cheap_value f

         DataValue inf m_cheap_value con repr ty_args ex_types args
           | any (`typeMentionsAny` forget_vars) (map fromTypM ty_args) ||
             any (`typeMentionsAny` forget_vars) (map fromTypM ex_types) ->
               Nothing
           | otherwise ->
               let args' = map forget args
                   m_cheap_value' =
                     if Set.null $ Set.intersection forget_vars (freeVariables m_cheap_value)
                     then m_cheap_value
                     else Nothing
               in Just $ DataValue inf m_cheap_value' con repr ty_args ex_types args'
         KnownHeapState (StoredValue stored_kv v)
           | v `Set.member` forget_vars -> Nothing
           | otherwise -> do
               stored_kv' <- forget (Just stored_kv)
               return $ KnownHeapState (StoredValue stored_kv' v)

-- | Construct a known value for a data constructor application,
--   given the arguments.  If this data constructor takes an output pointer
--   argument, that argument should /not/ be included among the parameters.
dataValue :: ExpInfo
          -> DataType           -- ^ The data type being constructed
          -> DataConType        -- ^ The data constructor being used
          -> [TypM]             -- ^ Type arguments to the constructor
          -> [MaybeValue]       -- ^ Value arguments to the constructor
          -> MaybeValue
dataValue inf d_type dcon_type ty_args args
  | length ty_args == num_expected_ty_args,
    length args == num_expected_args =
      let remembered_arg_values =
            [case fld_repr
             of ValRT -> arg_value
                BoxRT -> arg_value
                _ -> Nothing
            | (fld_repr ::: _, arg_value) <- zip field_types args]
      in Just (DataValue inf Nothing (dataConCon dcon_type)
               case_repr parametric_ty_args existential_ty_args remembered_arg_values)
  | otherwise = Nothing
  where
    (field_types, result_type) =
      instantiateDataConTypeWithExistentials dcon_type (map fromTypM ty_args)

    -- Representation of this data value when inspected by a case statement 
    case_repr =
      case dataTypeRepresentation d_type
      of Value -> ValRT
         Boxed -> BoxRT
         Referenced -> ReadRT

    dcon_num_pattern_params = length (dataConPatternParams dcon_type)

    -- The number of type arguments needed to make a fully applied
    -- data constructor
    num_expected_ty_args = dcon_num_pattern_params +
                           length (dataConPatternExTypes dcon_type)

    -- The number of value arguments needed to make a fully applied
    -- data constructor.  There's an extra argument for the output pointer
    -- if the result is a reference.
    num_expected_args = length (dataConPatternArgs dcon_type)
    
    parametric_ty_args = take dcon_num_pattern_params ty_args
    existential_ty_args = drop dcon_num_pattern_params ty_args

    -- 
  
-- | Create known values for data constructors in the global type environment.
--   In particular, nullary data constructors get a 'DataValue'.
initializeKnownValues :: TypeEnv -> IntMap.IntMap KnownValue
initializeKnownValues tenv =
  let datacons = getAllDataConstructors tenv
  in IntMap.mapMaybe make_datacon_value datacons
  where
     make_datacon_value dcon
       | null (dataConPatternParams dcon) &&
         null (dataConPatternExTypes dcon) &&
         null (dataConPatternArgs dcon) =
           let rrepr ::: _ = dataConPatternRange dcon
               con = dataConCon dcon
               cheap_expr = Just (ExpM $ VarE defaultExpInfo con)
           in Just $ DataValue defaultExpInfo cheap_expr con rrepr [] [] []
       | otherwise = Nothing
-}              
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
    
    bind_parameter (param, arg) body =
      ExpM $ LetE inf param arg body

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
      rwExpReturn (ExpM $ LamE inf fun', Just $ ComplexValue Nothing $ FunValue inf fun')
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
        -- Inline the value
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
  -- If the operator is an application and there are no type arguments,
  -- then uncurry the application
  case op'
  of ExpM (AppE _ inner_op inner_ty_args inner_args)
       | null ty_args -> do
         inner_op_value <- makeExpValue inner_op
         rwAppWithOperator inf inner_op inner_op_value inner_ty_args (inner_args ++ args)
     _ ->
       -- Apply simplification tecnhiques specific to this operator
       case op_val
       of Just (ComplexValue _ (FunValue _ funm@(FunM fun))) ->
            inline_function_call funm

          -- Some functions have special rewrite semantics
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
    loaded_value [_, Just (ComplexValue _ (StoredValue Value val))] =
        Just (asTrivialValue val, Just val)
    loaded_value [_, _] = Nothing
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
  let new_exp = ExpM $ AppE inf op' ty_args args'
      new_value = copied_value arg_values
  return (new_exp, Nothing)
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
  of MemVarP bind_var bind_rtype -> do
       (val', val_value) <- rwExp val
       
       -- The variable can be used to refer to this value
       let local_val_value =
             fmap (setTrivialValue bind_var) val_value

       -- Add the local variable to the environment while rewriting the body
       (body', body_val) <-
         assumeParamType bind_var bind_rtype $
         withMaybeValue bind_var local_val_value $
         rwExp body
       
       let ret_val = mask_local_variable bind_var body_val
       rwExpReturn (ExpM $ LetE inf bind val' body', ret_val)

     LocalVarP bind_var bind_type dict -> do
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
             ExpM $ LetE inf (LocalVarP bind_var bind_type dict') val' body'
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
  
  case scrut_val of
    Just (ComplexValue _ (DataValue _ con _ ex_args margs)) ->
      -- Case of known value.  Select the appropriate alternative and discard
      -- the others.
      case find ((con ==) . altConstructor . fromAltM) alts
      of Just altm ->
           -- Try to inline this case alternative
           case inline_alternative altm ex_args margs
           of Just eliminated_case ->
                -- Rewrite the new expression, including the body of the
                -- alternative
                rwExp eliminated_case
              Nothing -> no_eliminate scrut' [altm]
    _ -> no_eliminate scrut' alts
  where
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

    -- Try to inline a case alternative.  Succeed if all non-wildcard 
    -- variables have a known value.  Otherwise fail.
    -- This builds an expression and doesn't try to simplify it.
    inline_alternative (AltM alt) ex_args args
      | length (altExTypes alt) /= length ex_args =
          internalError "rwCase: Wrong number of type parameters"
      | length (altParams alt) /= length args =
          internalError "rwCase: Wrong number of fields"
      | otherwise =
          let -- Substitute known types for the existential type variables
              ex_type_subst =
                substitution $
                zip [v | TyPatM v _ <- altExTypes alt] $ map fromTypM ex_args

              patterns = map (substitutePatM ex_type_subst) (altParams alt)
              subst_body = substitute ex_type_subst (altBody alt)

          in -- Identify (pattern, value) pairs that should be bound by 
             -- let expressions
             case sequence $ zipWith bind_field patterns args
             of Nothing ->
                  -- Cannot create bindings because some values are unknown
                  Nothing
                Just m_bindings ->
                  let bindings = catMaybes m_bindings
                      new_exp = foldr make_binding subst_body bindings
                  in Just new_exp
      where
        make_binding (pat, rhs) body = ExpM $ LetE inf pat rhs body

        -- Attempt to bind a value to a data field.
        -- Return Nothing if a binding is required but cannot be built.
        -- Return (Just Nothing) if no binding is required.
        -- Return (Just (Just (p, v))) to produce binding (p, v).
        bind_field :: PatM -> MaybeValue -> Maybe (Maybe (PatM, ExpM))
        bind_field (MemWildP {}) _  =
          return Nothing

        bind_field pat@(MemVarP v (prepr ::: ptype)) kv
          | okay_for_binding = do
              value <- kv 
              exp <- asTrivialValue value
              return $ Just (pat, exp)
          | otherwise = Nothing   -- Cannot bind this pattern
          where
            -- We can only bind value and boxed parameters this way
            okay_for_binding =
              case prepr
              of ValPT _ -> True
                 BoxPT -> True
                 _ -> False

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
          with_params = foldr assume_param with_known_value labeled_params
          with_ty_params = foldr assume_ex_type with_params exTypes
      with_ty_params
    
    assume_ex_type (TyPatM v ty) m = assume v (ValRT ::: ty) m

    assume_param (MemVarP v pty) m = assumeParamType v pty m
    assume_param (MemWildP _) m = m
    
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
       return (MemVarP pvar pty)

rwFun :: FunM -> LR FunM
rwFun (FunM f) = do
  (body', _) <- rwExp (funBody f)
  return $ FunM $ Fun { funInfo = funInfo f
                      , funTyParams = funTyParams f
                      , funParams = funParams f
                      , funReturn = funReturn f
                      , funBody = body'}
    
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
    let global_known_values = initializeKnownValues tenv
    let env = LREnv { lrIdSupply = var_supply
                    , lrKnownValues = global_known_values
                    , lrTypeEnv = tenv
                    }
    runLR (rwModule mod) env


