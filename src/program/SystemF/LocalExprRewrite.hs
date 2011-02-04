
{-# LANGUAGE TypeSynonymInstances, FlexibleContexts #-}
module SystemF.LocalExprRewrite (rewriteLocalExpr)
where

import Control.Monad
import qualified Data.IntMap as IntMap
import Data.List as List
import Data.Maybe
import qualified Data.Set as Set
import Debug.Trace

import SystemF.MemoryIR
import SystemF.Syntax
import SystemF.Rename
import SystemF.TypecheckMem(functionType)
import qualified SystemF.PrintMemoryIR

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
  | DataValue
    { knownInfo    :: ExpInfo 
    , knownDataCon :: !Var 
    , knownRepr    :: !ReturnRepr 
    , knownTyArgs  :: [TypM] 
    , knownArgs    :: [MaybeValue]
    }
    
    -- | A literal value.
  | LitValue
    { knownInfo :: ExpInfo
    , knownLit  :: Lit
    }
    
    -- | A variable reference.
    --
    --   This is only built for variables with unknown values.
  | VarValue
    { knownInfo :: ExpInfo
    , knownVar  :: !Var
    }

type MaybeValue = Maybe KnownValue

-- | Is the variable mentioned in the value?
knownValueMentions :: KnownValue -> Var -> Bool
knownValueMentions kv search_v =
  case kv
  of VarValue _ v -> v == search_v
     LitValue _ _ -> False
     FunValue _ f -> search_v `Set.member` freeVariables f
     DataValue _ con _ ty_args args ->
       search_v == con ||
       any (`typeMentions` search_v) (map fromTypM ty_args) ||
       any (`maybeValueMentions` search_v) args

-- | Is any of the variables mentioned in the value?
knownValueMentionsAny :: KnownValue -> Set.Set Var -> Bool
knownValueMentionsAny kv search_vs =
  case kv
  of VarValue _ v -> v `Set.member` search_vs
     LitValue _ _ -> False
     FunValue _ f -> not $ Set.null $
                     Set.intersection search_vs (freeVariables f)
     DataValue _ con _ ty_args args ->
       con `Set.member` search_vs ||
       any (`typeMentionsAny` search_vs) (map fromTypM ty_args) ||
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
     DataValue {knownArgs = args} -> null args -- Inline nullary data values
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
     DataValue inf con _ ty_args args ->
       -- Get argument values.  All arguments must have a known value.
       case sequence $ map (knownValueExp =<<) args
       of Just arg_values ->
            Just $ ExpM $ AppE inf (ExpM $ VarE inf con) ty_args arg_values
          Nothing -> Nothing

computeExpValue :: ExpM -> LR MaybeValue
computeExpValue (ExpM expression) =
  case expression
  of VarE inf v -> do
       -- If the variable's value is known, return that.  Otherwise,  
       -- propagate the variable to all its uses.
       mval <- lookupKnownValue v
       case mval of
         Just val -> return mval
         Nothing -> return $ Just (VarValue inf v)
     LitE inf l -> return $ Just (LitValue inf l)
     
     AppE inf op ty_args args -> do
       tenv <- getTypeEnv

       -- If the operator is a data constructor, get its value 
       case op of
         ExpM (VarE _ op_var)
           | Just dcon_type <- lookupDataCon op_var tenv -> do
               arg_values <- mapM computeExpValue args
               return $ dataValue inf op_var dcon_type ty_args arg_values

         _ -> return Nothing
     LamE inf f -> return $ Just (FunValue inf f)

     -- Cannot represent the value of other expressions
     _ -> return Nothing

-- | Construct a known value for a data constructor application
--
--   FIXME: We don't handle writable references properly, neither 
--   in data values, nor in fields.  Come up with a plan for this.
dataValue :: ExpInfo -> Var -> DataConType -> [TypM] -> [MaybeValue]
          -> MaybeValue
dataValue inf op_var dcon_type ty_args args
  | ok_for_inlining,
    length ty_args == (length (dataConPatternParams dcon_type) +
                       length (dataConPatternExTypes dcon_type)),
    length args == length (dataConPatternArgs dcon_type) =
      Just (DataValue inf op_var return_repr ty_args args)
  | otherwise = Nothing
  where
    return_repr = case dataConPatternRange dcon_type
                  of repr ::: _ -> repr

    ok_for_inlining = 
      case return_repr
      of ValRT -> True
         BoxRT -> True
         _ -> False
  
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
           in Just $ DataValue defaultExpInfo con rrepr [] []
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

-- | Rewrite an expression.
--   Return the expression's value if it can be determined at compile time.
rwExp :: ExpM -> LR (ExpM, MaybeValue)
rwExp expression = do
  -- Simplify this expression
  ex1 <- restructureExp expression

  -- Simplify subexpressions
  case fromExpM ex1 of
    VarE inf v -> rwVar ex1 inf v
    LitE inf l -> return (ex1, Just $ LitValue inf l)
    AppE inf op ty_args args -> rwApp inf op ty_args args
    LamE inf fun -> do
      fun' <- rwFun fun
      return (ExpM $ LamE inf fun', Just $ FunValue inf fun')
    LetE inf bind val body -> rwLet inf bind val body
    LetrecE inf defs body -> rwLetrec inf defs body
    CaseE inf scrut alts -> rwCase inf scrut alts
    
-- | Rewrite a variable expression and compute its value.
rwVar original_expression inf v =
  return . rewrite =<< lookupKnownValue v
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

rwApp inf op ty_args args = do       
  (op', op_val) <- rwExp op
  
  -- Is this a fully applied call to a known function?
  case op_val of
    Just (FunValue _ funm@(FunM fun))
      | length (funTyParams fun) == length ty_args &&
        length (funParams fun) == length args -> do
          -- Inline the function and continue to simplify it  
          rwExp =<< betaReduce inf funm ty_args args
    _ -> do
      -- Continue processing function arguments
      (args', arg_vals) <- mapAndUnzipM rwExp args
      value <- make_app_value op' arg_vals
      return (ExpM $ AppE inf op' ty_args args', value)
  where
    -- If the operator is a data constructor,
    -- then try to build a data constructor value
    make_app_value new_op arg_vals = 
      case new_op
      of ExpM (VarE _ op_var) -> do
           tenv <- getTypeEnv
           case lookupDataCon op_var tenv of
             Just dcon_type ->
               return $ dataValue inf op_var dcon_type ty_args arg_vals
             Nothing -> return Nothing
         _ -> return Nothing

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
       return (ExpM $ LetE inf bind val' body', ret_val)

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
       return (ret_exp, ret_val)
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
  return (ExpM $ LetrecE inf defs' body', ret_value)

rwCase inf scrut alts = do
  (scrut', scrut_val) <- rwExp scrut
  
  case scrut_val of {-
    -- Commented out because we don't handle WriteRT fields properly
    Just (DataValue _ con _ ty_args margs)
      | Just args <- sequence $ map (knownValueExp =<<) margs -> do
        -- Case of known value.  Replace this case statement with the
        -- appropriate alternative.
        new_expr <- inline_alternative con ty_args args
        traceShow (text "Rewrote" <+> pprExp (ExpM $ CaseE inf scrut alts) $$
                   text "to" <+> pprExp new_expr) $
          rwExp new_expr -}
    _ -> do
      let scrutinee_var =
            case scrut'
            of ExpM (VarE _ scrut_var) -> Just scrut_var
               _ -> Nothing

      -- Cannot eliminate this case statement
      alts' <- mapM (rwAlt scrutinee_var) alts
      return (ExpM $ CaseE inf scrut' alts', Nothing)
  where
    inline_alternative con ty_args args =
      case find ((con ==) . altConstructor . fromAltM) alts
      of Just (AltM alt) 
           | length (altTyArgs alt) + length (altExTypes alt) /=
             length ty_args ->
               internalError "rwCase: Wrong number of type parameters"
           | length (altParams alt) /= length args ->
               internalError "rwCase: Wrong number of fields"
           | otherwise ->
               let ex_types = drop (length $ altTyArgs alt) ty_args
               in bind_alternative
                  (altExTypes alt) ex_types
                  (altParams alt) args
                  (altBody alt)
               
           -- Bind values with let 
         Nothing -> internalError "rwCase: No matching alternative"

    bind_alternative ex_pats ex_types pats args body =
      let let_bindings = map (substitutePatM ex_type_subst) pats
          subst_body = substitute ex_type_subst body
          new_exp = foldr bind_field subst_body $ zip let_bindings args
      in return new_exp
      where
        -- Substitute known types for the existential type variables
        ex_type_subst =
            substitution $
            zip [v | TyPatM v _ <- ex_pats] $ map fromTypM ex_types
        
        -- Bind a data field to a variable
        bind_field (pattern, value) body =
          ExpM $ LetE inf pattern value body

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


