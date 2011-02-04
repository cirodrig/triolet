
{-# LANGUAGE TypeSynonymInstances, FlexibleContexts, Rank2Types #-}
module SystemF.LocalExprRewrite (rewriteLocalExpr)
where

import Control.Monad
import qualified Data.IntMap as IntMap
import Data.List as List
import Data.Maybe
import Data.Monoid
import qualified Data.Set as Set
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import SystemF.Floating
import SystemF.MemoryIR
import SystemF.Syntax
import SystemF.Rename
import SystemF.TypecheckMem(functionType)
import SystemF.PrintMemoryIR

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
  withKnownValue v (FunValue (funInfo $ fromFunM f) f) m

withDefValues :: [Def Mem] -> LR a -> LR a
withDefValues defs m = foldr withDefValue m defs

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
assumeDefs :: [Def Mem] -> LR a -> LR a
assumeDefs defs m = foldr assumeDef m defs

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

-- | A value that is known (or partially known) at compile time.
--
--   This is used for various kinds of compile-time partial evaluation:
--   inlining, constant propagation, copy propagation, and case of
--   known value elimination.
data KnownValue =
    -- | A function, which may be inlined where it is used.
    FunValue
    { knownInfo :: ExpInfo 
    , knownFun  :: !FunM
    }

    -- | A fully applied data constructor.
    --
    --   In the case of reference objects, the fully applied constructor is
    --   a single-argument function that writes into its argument.
  | DataValue
    { knownInfo    :: ExpInfo 
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

type MaybeValue = Maybe KnownValue

pprKnownValue :: KnownValue -> Doc
pprKnownValue kv =
  case kv
  of FunValue _ f -> pprFun f
     DataValue _ con _ ty_args ex_types fields ->
       let type_docs =
             map (text "@" <>) $ map (pprType . fromTypM) (ty_args ++ ex_types)
           field_docs = map pprMaybeValue fields
       in pprVar con <>
          parens (sep $ punctuate (text ",") $ type_docs ++ field_docs)
     VarValue _ v -> pprVar v
     LitValue _ l -> pprLit l
     
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
     FunValue _ f -> search_v `Set.member` freeVariables f
     DataValue _ _ _ ty_args ex_types args ->
       any (`typeMentions` search_v) (map fromTypM ty_args) ||
       any (`typeMentions` search_v) (map fromTypM ex_types) ||
       any (`maybeValueMentions` search_v) args

-- | Is any of the variables mentioned in the value?
--
--   Does not check data constructors.
knownValueMentionsAny :: KnownValue -> Set.Set Var -> Bool
knownValueMentionsAny kv search_vs =
  case kv
  of VarValue _ v -> v `Set.member` search_vs
     LitValue _ _ -> False
     FunValue _ f -> not $ Set.null $
                     Set.intersection search_vs (freeVariables f)
     DataValue _ _ _ ty_args ex_types args ->
       any (`typeMentionsAny` search_vs) (map fromTypM ty_args) ||
       any (`typeMentionsAny` search_vs) (map fromTypM ex_types) ||
       any (`maybeValueMentionsAny` search_vs) args

maybeValueMentions :: MaybeValue -> Var -> Bool
maybeValueMentions Nothing _ = False
maybeValueMentions (Just kv) v = knownValueMentions kv v

maybeValueMentionsAny :: MaybeValue -> Set.Set Var -> Bool
maybeValueMentionsAny Nothing _ = False
maybeValueMentionsAny (Just kv) v = knownValueMentionsAny kv v

-- | Given that this is the value of an expression, should we replace the  
--   expression with this value?
worthInlining :: KnownValue -> Bool
worthInlining kv = 
  case kv
  of FunValue {} -> True -- Always inline functions
     DataValue {knownFields = args} -> null args -- Inline nullary data values
     LitValue {} -> True
     VarValue {} -> True

-- | Convert a known value to an expression.  It's an error if the known
--   value cannot be converted (e.g. it's a data constructor with some
--   unknown fields).
knownValueExp :: KnownValue -> Maybe ExpM
knownValueExp kv = 
  case kv
  of VarValue inf v -> Just $ ExpM $ VarE inf v
     LitValue inf l -> Just $ ExpM $ LitE inf l
     FunValue inf f -> Just $ ExpM $ LamE inf f
     DataValue inf con _ ty_args ex_types args ->
       -- Get argument values.  All arguments must have a known value.
       case sequence $ map (knownValueExp =<<) args
       of Just arg_values ->
            Just $ ExpM $ AppE inf (ExpM $ VarE inf con) (ty_args ++ ex_types) arg_values
          Nothing -> Nothing

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
         FunValue _ f
           | Set.null $ freeVariables f `Set.intersection` forget_vars ->
               Just kv
           | otherwise -> Nothing
         DataValue inf con repr ty_args ex_types args
           | any (`typeMentionsAny` forget_vars) (map fromTypM ty_args) ||
             any (`typeMentionsAny` forget_vars) (map fromTypM ex_types) ->
               Nothing
           | otherwise ->
               let args' = map forget args
               in Just $ DataValue inf con repr ty_args ex_types args'

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
      in Just (DataValue inf (dataConCon dcon_type)
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
           in Just $ DataValue defaultExpInfo con rrepr [] [] []
       | otherwise = Nothing
              
-------------------------------------------------------------------------------
-- Inlining

-- | Given a function and its arguments, get an expresion equivalent to
--   the function applied to those arguments.
betaReduce :: (Monad m, Supplies m VarID) =>
              ExpInfo -> FunM -> [TypM] -> [ExpM] -> m ExpM
betaReduce inf (FunM fun) ty_args args = do
  -- Substitute type arguments for type parameters
  let type_subst =
        substitution [(tv, t)
                     | (TyPatM tv _, TypM t) <- zip (funTyParams fun) ty_args]
        
  -- Rename parameters
  (params, param_renaming) <-
    freshenPatMs $ map (substitutePatM type_subst) $ funParams fun
  
  -- Rename function body
  let body = rename param_renaming $ substitute type_subst $ funBody fun
  
  -- Bind parameters to arguments
  return $ bind_parameters params args body
  where
    bind_parameters params args body =
      foldr bind_parameter body $ zip params args
    
    bind_parameter (param, arg) body =
      ExpM $ LetE inf param arg body

-------------------------------------------------------------------------------
-- Local restructuring

data LetPart s = LetPart { lpInfo :: ExpInfo
                         , lpBinder :: Pat s
                         , lpValue :: Exp s
                         -- Body :: Exp s
                         }
                  
type LetPartM = LetPart Mem
  
constructLet :: ExpM -> [LetPartM] -> LR ExpM
constructLet body [] = return body
constructLet body parts = do
  result <- foldM shapeLet body parts
  return result
  
  where
    shapeLet :: ExpM -> LetPartM -> LR ExpM
    shapeLet body (LetPart lpInf lpBind lpVal) =
      return $ ExpM $ LetE lpInf lpBind lpVal body

-- | Determine which parameters of an application term should be floated.
--   Returns a list containing a 'ParamType' for each argument that should be
--   floated.  The caller should check that the list length is equal to the 
--   actual number of operands in the application term.
floatedAppParameters :: DataConType -> [TypM] -> Maybe [Maybe ParamType]
floatedAppParameters dcon_type ty_args
  -- Float if all type arguments are supplied,
  -- and the representation is Value or Boxed
  | length ty_args == length (dataConPatternParams dcon_type) +
                      length (dataConPatternExTypes dcon_type) =
      let types = map fromTypM ty_args
          (field_types, _) =
            instantiateDataConTypeWithExistentials dcon_type types
      in Just $ map floatable field_types
  | otherwise = Nothing
  where
    floatable (rrepr ::: ty) =
      case rrepr
      of ValRT -> Just (ValPT Nothing ::: ty)
         BoxRT -> Just (BoxPT ::: ty)
         _ -> Nothing

delveExp :: ExpM -> LR ([LetPartM], ExpM)
delveExp (ExpM ex) = do
  case ex of
    LetE _ bind@(MemVarP {}) _ _ -> do
      freshenedEx <- freshen (ExpM ex) -- renames bind and body fields as defined in Rename.hs for non-LocalVar cases
      case fromExpM freshenedEx of
        LetE inf2 bind2@(MemVarP var ptype) val2 body2 -> do
          (letPs, replaceExp) <- delveExp val2
          let letPart = LetPart inf2 bind2 replaceExp
          return ( letPart:letPs , body2)

    AppE inf oper tyArgs args -> do
      (letParts, toReplaceArgs) <- mapAndUnzipM delveExp args
      let letParts' = concat letParts
      let replacedApp = ExpM $ AppE inf oper tyArgs toReplaceArgs
      return (letParts', replacedApp)

    _ -> return ([], ExpM ex)

{-
topExp :: ExpM -> LR ExpM
topExp (ExpM ex) = do
  case ex of
    LetE inf bind val body -> do
      body' <- {-trace "Top Checking body of a Let"-} topExp body
      (letPs, casePs, val') <- {-trace "Done with body, moving to Val"-} delveExp val
      let replaced = ExpM $ LetE inf bind val' body'
      postLet <- {-trace ("For the val on LetE:: "++(show (List.length letPs))++" lets, "++(show (List.length casePs))++" cases")-} constructLet replaced letPs
--      postCase <- constructCase postLet casePs
      return postLet
    CaseE inf scrut alts -> do scrut' <- topExp scrut
                               alts' <- mapM rwAlt alts
                               return $ ExpM $ CaseE inf scrut' alts'
    AppE inf oper tyArgs args -> do
      tupList <- mapM delveExp args
      let (letParts, caseParts, toReplaceArgs) = unzip3 tupList
      let letParts' = concat letParts
--      let caseParts' = concat caseParts
      let replacedApp = ExpM $ AppE inf oper tyArgs toReplaceArgs
      afterLetParts <- constructLet replacedApp letParts'
--      afterLetAndCaseParts <- constructCase afterLetParts caseParts'
      return afterLetParts
    LetrecE inf defs body -> do defs' <- mapM rwDef defs
                                body' <- topExp body
                                return $ ExpM $ LetrecE inf defs' body'
    LamE inf fun -> do fun' <- rwFun fun
                       return $ ExpM $ LamE inf fun'
    _ -> return $ ExpM ex -- Var and Lit
    -}
    
restructureExp :: ExpM -> LR ExpM
restructureExp ex = do
  (let_parts, ex') <- delveExp ex
  constructLet ex' let_parts

-------------------------------------------------------------------------------
-- Traversing code

data RWFloat =
  RWFloat
  { -- | Add floated variables' types and known values to the environment
    floatedContextSetup :: forall a. LR a -> LR a
    -- | The variables that are floated
  , floatedVariables :: Set.Set Var
    -- | The floated bindings
  , floatedBindings :: Context
  }

-- | @f1 `mappend` f2@ puts f1 outside f2
instance Monoid RWFloat where
  mempty = RWFloat { floatedContextSetup = id
                   , floatedVariables = Set.empty
                   , floatedBindings = []}
  f1 `mappend` f2 =
    RWFloat { floatedContextSetup = floatedContextSetup f1 .
                                    floatedContextSetup f2
            , floatedVariables = floatedVariables f1 `Set.union`
                                 floatedVariables f2
              -- Note order of floated bindings: f2 goes on the inside
            , floatedBindings = floatedBindings f2 ++ floatedBindings f1}

-- | Rewrite an expression.
--
--   Return the expression's value if it can be determined at compile time.
rwExp :: ExpM -> LR (ExpM, MaybeValue)
rwExp expression = do
  (flt, expression', mvalue) <- rwExp' expression
  
  -- If the known value mentions any floated variables, then forget it.
  -- The floated variables are no longer in scope.
  let ret_value = forgetVariables (floatedVariables flt) mvalue
  return (applyContext (floatedBindings flt) expression', ret_value)

rwExp' :: ExpM -> LR (RWFloat, ExpM, MaybeValue)
rwExp' expression = do
  -- Flatten nested let and case statements
  ex1 <- restructureExp expression

  -- Simplify subexpressions
  case fromExpM ex1 of
    VarE inf v -> rwVar ex1 inf v
    LitE inf l -> rwExpReturn (ex1, Just $ LitValue inf l)
    AppE inf op ty_args args -> rwApp inf op ty_args args
    LamE inf fun -> do
      fun' <- rwFun fun
      rwExpReturn (ExpM $ LamE inf fun', Just $ FunValue inf fun')
    LetE inf bind val body -> rwLet inf bind val body
    LetrecE inf defs body -> rwLetrec inf defs body
    CaseE inf scrut alts -> rwCase inf scrut alts

-- | Rewrite a list of expressions that are in the same scope,
--   such as arguments of a function call.
rwExps' :: [ExpM] -> LR (RWFloat, [ExpM], [MaybeValue])
rwExps' es = do
  results <- mapM rwExp' es
  case unzip3 results of
    (floats, exps, values) -> return (mconcat floats, exps, values)

rwExpReturn (exp, val) = return (mempty, exp, val)
    
-- | Rewrite a variable expression and compute its value.
rwVar original_expression inf v =
  rwExpReturn . rewrite =<< lookupKnownValue v
  where
    rewrite (Just val)
        -- Inline the value
      | worthInlining val,
        Just known_exp <- knownValueExp val = (known_exp, Just val)

        -- Otherwise, don't inline, but propagate the value
      | otherwise = (original_expression, Just val)
    rewrite Nothing =
      -- Set up for copy propagation
      (original_expression, Just $ VarValue inf v)

rwApp :: ExpInfo -> ExpM -> [TypM] -> [ExpM]
      -> LR (RWFloat, ExpM, MaybeValue)
rwApp inf op ty_args args = do       
  (float_op_bind, op', op_val) <- rwExp' op

  -- Add the operator's value to the environment while processing arguments
  (result_float, result_exp, result_val) <-
    floatedContextSetup float_op_bind $
    -- Is this a fully applied call to a known function or data constructor?
    case op_val
    of Just (FunValue _ funm@(FunM fun))
         | length (funTyParams fun) == length ty_args &&
           length (funParams fun) == length args ->
             inline_function_call funm

       Just (VarValue _ op_var) -> do
         -- Check if it's a data constructor, and if so, rewrite it
         data_con_result <- tryRwDataConApp inf op' op_var ty_args args
         case data_con_result of
           Just result -> return result
           Nothing -> unknown_app op'

       _ -> unknown_app op'
  
  -- Include the operator's floated bindings in the result
  return (float_op_bind `mappend` result_float, result_exp, result_val)
  where
    unknown_app op' = do
      (arg_floats, args', _) <- rwExps' args
      let new_exp = ExpM $ AppE inf op' ty_args args'
      return (arg_floats, new_exp, Nothing)

    -- Inline the function call and continue to simplify it.
    -- The arguments will be processed after inlining.
    inline_function_call funm =
      rwExp' =<< betaReduce inf funm ty_args args

-- | Try to rewrite a data constructor application.
--   Return the rewritten result if successful, Nothing otherwise.
tryRwDataConApp :: ExpInfo
                -> ExpM         -- ^ Data constructor expression
                -> Var          -- ^ Data constructor variable
                -> [TypM]       -- ^ Type arguments
                -> [ExpM]       -- ^ Value arguments, not simplified yet
                -> LR (Maybe (RWFloat, ExpM, MaybeValue))
tryRwDataConApp inf op op_var ty_args args = do
  tenv <- getTypeEnv
  case lookupDataConWithType op_var tenv of
    Just (con_type, dcon_type) ->
      case floatedAppParameters dcon_type ty_args
      of Just float_spec | length float_spec == length args ->
           liftM Just $
           rwDataConApp inf op con_type dcon_type float_spec ty_args args
         _ -> return Nothing
    _ -> return Nothing

-- | Rewrite a data constructor application.  Called by 'tryRwDataConApp'.
rwDataConApp :: ExpInfo
             -> ExpM            -- ^ Data constructor expression
             -> DataType        -- ^ Data type being constructed
             -> DataConType     -- ^ Data constructor used
             -> [Maybe ParamType] -- ^ Which arguments should be floated
             -> [TypM]          -- ^ Type arguments
             -> [ExpM]          -- ^ Value arguments, not simplified yet
             -> LR (RWFloat, ExpM, MaybeValue)
rwDataConApp inf op data_type dcon_type float_spec ty_args args = do
  fields <- zipWithM rw_field float_spec args
  let (floatbinds, args', arg_values) = unzip3 fields
      floatbind = mconcat floatbinds
      value = dataValue inf data_type dcon_type ty_args arg_values
      new_exp = ExpM $ AppE inf op ty_args args'
           
  return (floatbind, new_exp, value)
  where
    rw_field Nothing arg = rw_unfloated_field arg
    rw_field (Just ptype) arg = rw_floated_field ptype arg
    
    -- Rewrite and float a field.
    -- The field's value gets assigned to a new variable.
    -- Return a function that adds the new variable to the environment.
    rw_floated_field param_type arg = do
      (arg', arg_value) <- rwExp arg
      arg_var <- newAnonymousVar ObjectLevel
      let pattern = MemVarP arg_var param_type
          context = contextItem $ LetCtx inf pattern arg'
          env =
            withMaybeValue arg_var arg_value .
            assumeParamType arg_var param_type
          
          float_bind =
            RWFloat { floatedContextSetup = env
                    , floatedVariables = Set.singleton arg_var
                    , floatedBindings = [context]}
      return (float_bind, ExpM $ VarE inf arg_var, arg_value)
    
    -- Rewrite a field.  Don't float it.
    rw_unfloated_field arg = do
      (arg', arg_value) <- rwExp arg
      return (mempty, arg', arg_value)

rwLet inf bind val body =       
  case bind
  of MemVarP bind_var bind_rtype -> do
       (val', val_value) <- rwExp val

       -- Add the local variable to the environment while rewriting the body
       (body', body_val) <-
         assumeParamType bind_var bind_rtype $
         withMaybeValue bind_var val_value $
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
    mask_local_variable bind_var ret_val 
      | ret_val `maybeValueMentions` bind_var = Nothing
      | otherwise = ret_val

rwLetrec inf defs body = withDefs defs $ \defs' -> do
  (body', body_value) <- rwExp body
      
  let local_vars = Set.fromList [v | Def v _ <- defs']
      ret_value = if body_value `maybeValueMentionsAny` local_vars
                  then Nothing
                  else body_value
  rwExpReturn (ExpM $ LetrecE inf defs' body', ret_value)

rwCase inf scrut alts = do
  (scrut', scrut_val) <- rwExp scrut
  
  case scrut_val of
    Just (DataValue _ con _ _ ex_args margs) ->
      -- Case of known value.  Select the appropriate alternative and discard
      -- the others.
      case find ((con ==) . altConstructor . fromAltM) alts
      of Just altm ->
           -- Try to inline this case alternative
           case inline_alternative altm ex_args margs
           of Just eliminated_case ->
                -- Rewrite the new expression, including the body of the
                -- alternative
                rwExp' eliminated_case
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
              exp <- knownValueExp value
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
rwAlt scr (AltM (Alt const tyArgs exTypes params body)) = assume_params $ do
  -- TODO: If scrutinee variable is given, assign it a known value
  (body', _) <- rwExp body
  return $ AltM $ Alt const tyArgs exTypes params body'
  where
    assume_params m =
      foldr assume_ex_type (foldr assume_param m params) exTypes
    
    assume_ex_type (TyPatM v ty) m = assume v (ValRT ::: ty) m

    assume_param (MemVarP v pty) m = assumeParamType v pty m
    assume_param (MemWildP _) m = m

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
withDefs :: [Def Mem] -> ([Def Mem] -> LR a) -> LR a
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


