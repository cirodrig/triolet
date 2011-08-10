{-| The simplifier.

The simplifier makes a forward sweep through a program, more or less in
execution order, and tries to statically evaluate what it can.

This sweep performs copy propagation, constant propagation,
beta reduction (includes inlining), case-of-known-value elimination,
and some local expression reordering.
-}

{-# LANGUAGE TypeSynonymInstances, FlexibleContexts, Rank2Types,
    ViewPatterns #-}
module SystemF.Simplify (SimplifierPhase(..),
                         rewriteLocalExpr,
                         rewriteAtPhase)
where

import Prelude hiding(mapM)
import Control.Monad hiding(mapM)
import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import qualified Data.IntMap as IntMap
import Data.IORef
import Data.List as List
import Data.Maybe
import Data.Monoid
import qualified Data.Set as Set
import Data.Traversable(mapM)
import Debug.Trace
import Text.PrettyPrint.HughesPJ hiding(float)
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

-- | Different features of the simplifier are enabled
--   depending on the stage of compilation.
data SimplifierPhase =
    GeneralSimplifierPhase

    -- | After parallelization, the sequential phase
    --   converts loops to sequential form
  | SequentialSimplifierPhase
  
    -- | Finally, functions are inlined without regard to rewrite rules. 
  | FinalSimplifierPhase

data LREnv =
  LREnv
  { lrIdSupply :: {-# UNPACK #-}!(Supply VarID)
    
    -- | Active rewrite rules
  , lrRewriteRules :: !RewriteRuleSet

    -- | Information about the values stored in variables
  , lrKnownValues :: IntMap.IntMap AbsValue
    
    -- | Types of variables
  , lrTypeEnv :: TypeEnv
    
  , lrDictEnv :: MkDictEnv
  , lrIntEnv :: IntIndexEnv
    
    -- | Number of simplification steps to perform.  For debugging, we may
    --   stop simplification after a given number of steps.
    --
    --   If value is negative, then fuel is unlimited.  If value is zero, then
    --   further simplification is not performed.
  , lrFuel :: {-#UNPACK#-}!(IORef Int)

    -- | The current phase.  The phase is constant during a pass of the
    --   simplifier.
  , lrPhase :: !SimplifierPhase
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

getPhase :: LR SimplifierPhase
getPhase = LR $ \env -> return (lrPhase env)

lookupKnownValue :: Var -> LR MaybeValue
lookupKnownValue v = LR $ \env ->
  let val = IntMap.lookup (fromIdent $ varID v) $ lrKnownValues env
  in return val

-- | Add a variable's known value to the environment 
withKnownValue :: Var -> AbsValue -> LR a -> LR a
withKnownValue v val m = LR $ \env ->
  let insert_assignment mapping =
        IntMap.insert (fromIdent $ varID v) val mapping
      env' = env {lrKnownValues = insert_assignment $ lrKnownValues env}
  in runLR m env'
  where
    -- Debugging: Show the known value for this variable
    trace_assignment =
      traceShow (text "Simpl" <+> pprVar v <+> text "=" <+> pprAbsValue val)

-- | Add a variable's value to the environment, if known
withMaybeValue :: Var -> MaybeValue -> LR a -> LR a
withMaybeValue _ Nothing m = m
withMaybeValue v (Just val) m = withKnownValue v val m

-- | Add a function definition's value to the environment.
--
--   The function may or may not be added, depending on its attributes and
--   whether the function is part of a recursive group.
withDefValue :: Bool -> Def Mem -> LR a -> LR a
withDefValue is_rec def@(Def v _ f) m = do
  phase <- getPhase
  let fun_info = funInfo $ fromFunM f
      fun_val = setTrivialValue v $ funAV fun_info Nothing f
      can_inline = if is_rec
                   then isRecInliningCandidate phase def 
                   else isInliningCandidate phase def
  if can_inline then withKnownValue v fun_val m else m

-- | Add a function definition to the environment, but don't inline it
withUninlinedDefValue :: Def Mem -> LR a -> LR a
withUninlinedDefValue (Def v _ f) m = m

withDefValues :: Bool -> DefGroup (Def Mem) -> LR a -> LR a
withDefValues False  (NonRec def) m = withDefValue False def m

-- Nonrecursive groups are not recursive
withDefValues True   (NonRec _)   m = internalError "withDefValues"

withDefValues is_rec (Rec defs)   m = foldr (withDefValue is_rec) m defs

-- | Decide whether a function may be inlined within its own recursive
--   definition group.  The function's attributes are used for the decision.
--
--   We do not take into account here whether it's /beneficial/ to inline the
--   function.
isRecInliningCandidate :: SimplifierPhase -> Def Mem -> Bool
isRecInliningCandidate _ def =
  -- It's inlinable only if it's a wrapper function
  defIsWrapper def

-- | Decide whether a function may be inlined (outside of its own definition
--   group).  The function's attributes are used for the decision.
--
--   We do not take into account here whether it's /beneficial/ to inline the
--   function.
isInliningCandidate :: SimplifierPhase -> Def Mem -> Bool
isInliningCandidate phase def =
  let ann = defAnnInlining $ defAnnotation def
  in case phase
     of GeneralSimplifierPhase ->
          case ann
          of InlNormal     -> True 
             InlWrapper    -> True
             InlSequential -> False
             InlFinal      -> False
        SequentialSimplifierPhase ->
          case ann
          of InlNormal     -> True 
             InlWrapper    -> True
             InlSequential -> True
             InlFinal      -> False
        FinalSimplifierPhase ->
          True

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
               vcat [hang (text (show n)) 8 (pprAbsValue kv)
                    | (n, kv) <- IntMap.toList $ lrKnownValues env]
  in traceShow kv_doc $ runLR m env

-- | Check whether there is fuel available.
--   If True is returned, then it's okay to perform a task that consumes fuel.
checkFuel :: LR Bool
checkFuel = LR $ \env -> fmap (0 /=) $ readIORef $ lrFuel env

-- | Perform an action only if there is fuel remaining
ifFuel :: a -> LR a -> LR a
ifFuel default_value action = checkFuel >>= choose
  where
    choose False = return default_value
    choose True  = action

ifElseFuel :: LR a -> LR a -> LR a
ifElseFuel default_action action = checkFuel >>= choose
  where
    choose False = default_action
    choose True  = action

-- | Consume one unit of fuel.
--   Don't consume fuel if fuel is empty (0),
--   or if fuel is not in use (negative).
consumeFuel :: LR ()
consumeFuel = LR $ \env -> do
  fuel <- readIORef $ lrFuel env
  when (fuel > 0) $ writeIORef (lrFuel env) $! fuel - 1

-- | Use fuel to perform an action.  If there's no fuel remaining,
--   don't perform the action.
useFuel :: a -> LR a -> LR a
useFuel default_value action = ifFuel default_value (consumeFuel >> action)

-- | Use fuel to perform an action.  If there's no fuel remaining,
--   don't perform the action.
useFuel' :: LR a -> LR a -> LR a
useFuel' out_of_fuel action = ifElseFuel out_of_fuel (consumeFuel >> action)

-- | Try to construct the value of an expression, if it's easy to get.
--
--   This is called if we've already simplified an expression and thrown
--   away its value, and now we want to get it back.
makeExpValue :: ExpM -> LR MaybeValue
makeExpValue (ExpM expression) =
  case expression
  of VarE inf v -> do
       mvalue <- lookupKnownValue v
       return $ mvalue `mplus` Just (VarAV inf v)
     LitE inf l -> return $ Just $ LitAV inf l
     _ -> return Nothing

rewriteAppInSimplifier inf operator ty_args args = LR $ \env -> do
  rewriteApp (lrRewriteRules env) (lrIntEnv env) (lrIdSupply env) (lrTypeEnv env)
    inf operator ty_args args

-------------------------------------------------------------------------------
-- Inlining

-- | Decide whether to inline the expression, which is the RHS of an
--   assignment, /before/ simplifying it.  If inlining is indicated, it
--   must be possible to replace all occurrences of the assigned variable
--   with the inlined value; to ensure this, reference values are never
--   pre-inlined.  Pre-inlining is performed only if it does not duplicate
--   code or work.
--
--   If the expression should be inlined, return a 'AbsValue' holding
--   the equivalent value.  Non-writer expressions become an
--   'InlAV'.  Writer expressions become a 'DataAV' containing
--   'InlAV's.
worthPreInlining :: TypeEnv -> Dmd -> ExpM -> Maybe AbsValue
worthPreInlining tenv dmd expr =
  let should_inline =
        case multiplicity dmd
        of OnceSafe -> inlckTrue
           ManySafe -> inlckTrivial
           OnceUnsafe -> inlckTrivial `inlckOr` inlckFunction
           _ -> inlckFalse
  in if should_inline tenv dmd expr
     then Just (InlAV expr)
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
--   If the expression should be inlined, return a 'AbsValue' holding
--   the equivalent value.  Non-writer expressions become an
--   'InlAV'.  Writer expressions become a 'DataAV' containing
--   'InlAV's.
worthPostInlining :: TypeEnv -> Bool -> Dmd -> ExpM -> Maybe AbsValue
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
    data_value False expr = Just $ InlAV expr
    
    -- Writer fields are converted to readable data constructor values
    data_value True expr =
      case unpackVarAppM expr
      of Just (op, ty_args, args)
           | op `isPyonBuiltin` the_store ->
               -- Behave like 'rwStoreApp'.
               -- Allow the store to cancel with a later load.
               let [source] = args
               in Just $ bigAV $
                  WriterAV $ bigAV $
                  StoredValue Value $ InlAV source

           | op `isPyonBuiltin` the_storeBox ->
               -- Behave like 'rwStoreBoxApp'.
               -- Allow the store to cancel with a later load.
               let [source] = args
               in Just $ bigAV $
                  WriterAV $ bigAV $
                  StoredValue Boxed $ InlAV source

           | op `isPyonBuiltin` the_copy ->
               -- When using the value, read the source value directly
               let [_, source] = args
               in Just $ bigAV $ WriterAV $ InlAV source
           | Just (tycon, dcon) <- lookupDataConWithType op tenv ->
               let (field_types, _) =
                     instantiateDataConTypeWithExistentials dcon ty_args

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
      -- Rename bound value parameters if they conflict with names in the
      -- environment
      FunM freshened_fun <- freshenFunValueParams (FunM fun)

      -- Substitute type arguments for type parameters
      let type_subst =
            substitution [(tv, t)
                         | (TyPatM (tv ::: _), TypM t) <-
                             zip (funTyParams freshened_fun) ty_args]

      -- Apply substitution to parameters and body
      params <- substitutePatMs type_subst (funParams freshened_fun)
      let subst = type_subst
      body <- substitute subst $ funBody freshened_fun
      ret <- substitute subst $ funReturn freshened_fun
          
      -- Is the function fully applied?
      return $! case length args `compare` length params
                of LT -> undersaturated_app (funInfo freshened_fun) args params body ret
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
    undersaturated_app inf args params body return =
      let applied_params = take (length args) params
          excess_params = drop (length args) params
          new_fun = FunM $ Fun { funInfo = inf
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
-- Converting known values to expressions

-- | Attempt to construct a value from an expression.
--   Prefer to create initializer values rather than data values.
createValue :: BaseKind -> AbsValue -> LR (Maybe (ExpM, MaybeValue))
createValue kind known_value =
  -- There are two cases to deal with.  The simple case is that we can just
  -- "use the value" as if inlining it.  The complex case is when the value   
  -- is a bare value; then we want to construct a new value.
  case fromDataAV known_value
  of Just (DataValue inf ty fs)
       | kind == BareK -> do
           -- Attempt to create a new data constructor application
           data_app <- createDataConApp inf ty fs
           case data_app of
             Nothing -> try_trivial_values
             Just ret -> return (Just ret)
     _ -> try_trivial_values
  where
    -- Try to get a value out of the known value.  This code is
    -- similar to the code for simplifying a VarE term.
    try_trivial_values
      | Just e <- asTrivialValue known_value = do
          -- Copy the value
          copy_e <- copy_expression e
          let copy_v = copy_value known_value
          return $ Just (copy_e, Just copy_v)

      | Just e <- asInlinedValue known_value = liftM Just $ rwExp e

      | otherwise = return Nothing

    copy_value val =
      case kind
      of BareK -> writerAV val
         _ -> val

    copy_expression e =
      case kind
      of BareK -> mkCopyExp e
         _     -> return e

mkCopyExp e = do
  e_type <- inferExpType e
  e_dict <- getReprDict e_type
  return $ appE defaultExpInfo copy_op [TypM e_type] [e_dict, e]
  where
    copy_op = ExpM $ VarE defaultExpInfo (pyonBuiltin the_copy)

-- | Attempt to construct a data initializer expression.
--   The parameters are fields of a 'DataAV' representing a bare object.
--
--   This function handles data constructors whose result kind is \"bare\".
--   Other known values are handled by 'createValue'.
createDataConApp :: ExpInfo -> DataValueType -> [MaybeValue]
                 -> LR (Maybe (ExpM, MaybeValue))
createDataConApp inf val_type m_fields 
  | Just fields <- sequence m_fields = createDataConApp' inf val_type fields
  | otherwise = return Nothing
      
createDataConApp' :: ExpInfo -> DataValueType -> [AbsValue]
                  -> LR (Maybe (ExpM, MaybeValue))
createDataConApp' inf val_type fields = do
  tenv <- getTypeEnv
  -- Get the kind inhabited by each field.  The kind is used to decide
  -- whether to copy the field or not.
  let field_kinds =
        case val_type of
          ConValueType con _ _ ->
            case lookupDataCon con tenv
            of Just dcon_type -> dataConFieldKinds tenv dcon_type
               Nothing -> internalError "createDataConApp"
          TupleValueType field_types ->
            map (toBaseKind . typeKind tenv . fromTypM) field_types

  field_results <- zipWithM createValue field_kinds fields

  case sequence field_results of
    Just (unzip -> (field_exps, field_values)) ->
      -- Apply the data constructor
      let data_exp =
            case val_type
            of ConValueType con ty_args ex_args ->
                 let con_exp = ExpM $ VarE defaultExpInfo con
                 in appE inf con_exp (ty_args ++ ex_args) field_exps
               TupleValueType _ ->
                 ExpM $ UTupleE inf field_exps
          
          -- This is an initializer expression, so it has a writer valeu
          value = writerAV $ dataAV $ DataValue inf val_type field_values
      in return $ Just (data_exp, Just value)
    Nothing -> return Nothing
      

-------------------------------------------------------------------------------
-- Local restructuring
    
-- Before trying to simplify an expression, we restruture it to increase the 
-- scopes of temporary variables.  Let-expressions are floated out from the
-- RHS of other let expressions and from inside function calls.

-- | After restructuring, an expression is either eliminated or divested of
--   a context.  The expression is eliminated if it will raise an exception.
--   Otherwise, bindings in the expression are floated outward.
data Restructured a = Restructured Context a | Excepting

newtype Restructure a = Restructure {restructure :: LR (Restructured a)}

-- | Add some context to the result of a restructuring computation.
--   The context will go outside any context generated by @m@.
addContext ctx1 m = Restructure $ do
  r <- restructure m
  return $! case r
            of Restructured ctx2 y -> Restructured (ctx2 ++ ctx1) y
               Excepting           -> Excepting

-- | Restructuring can be interpreted as a monad.
--   Floated contexts behave like a 'MonadWriter' instance.
instance Monad Restructure where
  return x = Restructure (return (Restructured [] x))
  m >>= k = Restructure $ restructure m >>= continue
    where
      continue (Restructured ctx1 x) = restructure $ addContext ctx1 (k x)
      continue Excepting = return Excepting

-- | Restructuring an 'ExceptE' statement is like a zero, in the sense that
--   it wipes out all other results.
restructureZero :: Restructure a
restructureZero = Restructure (return Excepting)

liftR :: LR a -> Restructure a
liftR m = Restructure $ do
  x <- m
  return (Restructured [] x)

-- | Add the context produced by @m@ to the environment in the continuation
floatAndAssume :: Restructure a -> (a -> Restructure b) -> Restructure b
floatAndAssume m k = Restructure $ restructure m >>= continue
  where
    continue Excepting = return Excepting
    continue (Restructured ctx x) = do
      -- When calling 'addContext', put previously floated context from 'm'
      -- outside the floated context introduced by this function call.
      assumeContext ctx $ restructure $ addContext ctx (k x)

-- | Float a piece of context.
--
--   The floated context goes inside of any previously floated context. 
floatItem :: ContextExp -> Restructure ()
floatItem item = Restructure $ return $ Restructured [contextItem item] ()

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

recFlattenExp :: ExpM -> Restructure ExpM
recFlattenExp e = Restructure $ restructure (flattenExp e) >>= continue
  where
    continue (Restructured ctx1 e') | not (null ctx1) = do
      assumeContext ctx1 $ restructure $ addContext ctx1 (recFlattenExp e')

    continue ret = return ret

-- | Flatten an expression.  Local let-bindings and case-bindings are 
--   floated outward.
flattenExp :: ExpM -> Restructure ExpM
flattenExp (ExpM expression) =
  case expression
  of LetE inf pat rhs body -> flattenLetExp inf pat rhs body
     LetfunE inf defs body -> flattenLetfunExp inf defs body
     CaseE inf scr alts -> flattenCaseExp inf scr alts
     AppE inf op ty_args args -> flattenAppExp inf op ty_args args
     ExceptE _ ty -> restructureZero
     _ -> return (ExpM expression)

flattenExps :: [ExpM] -> Restructure [ExpM]
flattenExps es = mapM flattenExp es

flattenLetExp inf pat rhs body = do
  -- Flatten the RHS.  Since the body of the RHS will be the new RHS,
  -- make sure it's completely flattened.
  flat_rhs <- recFlattenExp rhs

  -- Float this binding
  (floated, rn) <- liftR $ freshenContextExp $ LetCtx inf pat flat_rhs
  floatItem floated
  return (rename rn body)

flattenLetfunExp inf defs body = do
  -- Float this binding
  (floated, rn) <- liftR $ freshenContextExp $ LetfunCtx inf defs
  floatItem floated
  return (rename rn body)

flattenCaseExp inf scr alts = do
  -- Perform floating in the scrutinee
  floated_scr <-
    -- Flatten the scrutinee
    recFlattenExp scr `floatAndAssume` \flattened_scr -> do
      tenv <- liftR getTypeEnv
      
      -- If the scrutinee is 
      --
      -- * a trivial expression, then floating it outward won't make
      --   it any simpler.
      --
      -- * a data constructor application, then the case statement will
      --   cancel it out.  Leave it in place in order to make sure that
      --   happens.
      --
      -- Otherwise, assign the flattened scrutinee to a new variable and then
      -- float the newly created binding.
      if isTrivialExp flattened_scr || isDataConAppM tenv flattened_scr
        then return flattened_scr
        else float_scrutinee flattened_scr

  let simplified_case = ExpM $ CaseE inf floated_scr alts

  -- Is this case binding suitable for floating?
  case asCaseCtx simplified_case of
    Nothing ->
      return simplified_case

    Just (case_ctx, case_body) -> do
      -- Float the case binding.  Rename and return the body.
      (rn_case_ctx, rn) <- liftR $ freshenContextExp case_ctx
      floatItem rn_case_ctx
      return $ rename rn case_body
  where
    -- Assign the scrutinee value to a new variable, and float the assignment.
    -- Return the new scrutinee (which is the newly created variable).
    float_scrutinee flattened_scr = do
      -- Create a new variable that will bind the scrutinee
      scr_var <- liftR $ newAnonymousVar ObjectLevel
      scr_type <- liftR $ inferExpType flattened_scr

      -- Construct demand information for the new scrutinee variable.
      -- The scrutinee variable is used exactly once, in place of the
      -- original scrutinee expression.  Demand information can be
      -- reconstructed from the bindings in the case statement.
      let demand = Dmd OnceSafe (altListSpecificity alts)
          binder = setPatMDmd demand $ patM (scr_var ::: scr_type)
      floatItem (LetCtx inf binder flattened_scr)
      return (ExpM $ VarE inf scr_var)

flattenAppExp inf op ty_args args = do
  oper' <- flattenExp op
  args' <- flattenExps args
  return $ appE inf oper' ty_args args'

-- | Restructure an expression.  Find subexpressions that have local bindings
--   and float those bindings outward.  Bindings are only floated out from 
--   the following contexts:
--
--   * RHS of a let expression
--   * scrutinee of a case expression
--   * operator or operands of a function call
--
--   Restructuring is applied recursively to the body of a let expression.
--   It's also applied recursively to the body of a case expression if there 
--   is exactly one non-excepting case alternative.  Recursion is actually
--   performed by floating away the let-binding or case binding.
restructureExp :: ExpM -> LR ExpM
restructureExp ex = restructure (flattenExp ex) >>= rebuild
  where
    rebuild (Restructured [] _) =
      return ex -- Expression is unchanged

    rebuild x = do
      consumeFuel
      -- Use the original expression's type as the return type.  It's
      -- the same as the new expression's type.
      e_type <- inferExpType ex
      return $! case x 
                of Restructured ctx ex' ->
                     -- Put context onto the new expression
                     applyContextWithType e_type ctx ex'
                   Excepting ->
                     -- Replace with an exception
                     ExpM $ ExceptE defaultExpInfo e_type

-------------------------------------------------------------------------------
-- Traversing code

-- | Rewrite an expression.
--
--   Return the expression's value if it can be determined.
rwExp :: ExpM -> LR (ExpM, MaybeValue)
rwExp expression = debug "rwExp" expression $ do
    -- Flatten nested let and case statements.  Consume fuel only if flattening
    -- occurs.
    -- DEBUG: rename variables
    ex1 <- ifFuel expression $ restructureExp expression

    -- Simplify subexpressions.
    --
    -- Even if we're out of fuel, we _still_ must perform some simplification
    -- steps in order to propagate 'InlAV's.  If we fail to propagate
    -- them, the output code will still contain references to variables that
    -- were deleted.
    case fromExpM ex1 of
      VarE inf v -> rwVar ex1 inf v
      LitE inf l -> rwExpReturn (ex1, Just $ LitAV inf l)
      UTupleE inf args -> rwUTuple inf args
      AppE inf op ty_args args -> rwApp ex1 inf op ty_args args
      LamE inf fun -> do
        (fun', fun_val) <- rwFun fun
        rwExpReturn (ExpM $ LamE inf fun',
                     Just $ funAV inf fun_val fun')
      LetE inf bind val body -> rwLet inf bind val body
      LetfunE inf defs body -> rwLetrec inf defs body
      CaseE inf scrut alts -> rwCase inf scrut alts
      ExceptE _ _ -> rwExpReturn (ex1, Nothing)
      CoerceE inf from_t to_t body -> rwCoerce inf from_t to_t body
  where
    debug _ _ = id
    -- debug l e m = traceShow (text l <+> (pprExp e)) m
    {-debug l e m = do
      ret@(e', _) <- m
      traceShow (text l <+> (pprExp e $$ text "----" $$ pprExp e')) $ return ret
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
      | Just inl_value <- asInlinedValue val = do
          -- This variable is inlined unconditionally.  This step does not
          -- consume fuel; fuel was consumed when the variable was selected for
          -- unconditional inlining.
          rwExp inl_value

      | Just cheap_value <- asTrivialValue val =
          -- Use fuel to replace this variable
          useFuel (original_expression, Nothing) $
          rwExpReturn (cheap_value, Just val)

        -- Otherwise, don't inline, but propagate the value
      | otherwise = rwExpReturn (original_expression, Just val)
    rewrite Nothing =
      -- Give the variable a value, so that copy propagation may occur
      rwExpReturn (original_expression, Just $ VarAV inf v)

rwUTuple inf args = do
  -- Just rewrite subexpressions
  (args', arg_values) <- mapAndUnzipM rwExp args
  arg_types <- mapM inferExpType args'
  
  let ret_value = tupleConValue inf (map TypM arg_types) arg_values
      ret_exp = ExpM $ UTupleE inf args'
  return (ret_exp, ret_value)

rwApp :: ExpM -> ExpInfo -> ExpM -> [TypM] -> [ExpM] -> LR (ExpM, MaybeValue)
rwApp original_expression inf op ty_args args =
  -- First try to uncurry this application
  case op
  of ExpM (AppE _ inner_op inner_ty_args inner_args)
       | null ty_args ->
           use_fuel $ continue inner_op inner_ty_args (inner_args ++ args)
       | null inner_args ->
           use_fuel $ continue inner_op (inner_ty_args ++ ty_args) args
     _ -> simplify_op
  where
    use_fuel m = useFuel' simplify_op m

    continue op ty_args args =
      rwApp (appE inf op ty_args args) inf op ty_args args

    simplify_op = do
      (op', op_val) <- rwExp op
      let modified_expression = appE inf op' ty_args args
      rwAppWithOperator modified_expression inf op' op_val ty_args args


-- | Rewrite an application, depending on what the operator is.
--   The operator has been simplified, but the arguments have not.
--
--   This function is usually called from 'rwApp'.  It calls itself 
--   recursively to flatten out curried applications.
rwAppWithOperator original_expression inf op' op_val ty_args args =
  -- First, try to uncurry this application.
  -- This happens if the operator was rewritten to an application;
  -- otherwise we would have uncurried it in 'rwApp'.
  case op'
  of ExpM (AppE _ inner_op inner_ty_args inner_args)
       | null ty_args -> use_fuel $ do
           inner_op_value <- makeExpValue inner_op
           continue inner_op inner_op_value inner_ty_args (inner_args ++ args)
       | null inner_args -> use_fuel $ do
           inner_op_value <- makeExpValue inner_op
           continue inner_op inner_op_value (inner_ty_args ++ ty_args) args
     _ ->
       -- Apply simplification tecnhiques specific to this operator
       case op_val
       of Just (fromFunAV -> Just funm) ->
            use_fuel $ inline_function_call funm

          -- Use special rewrite semantics for built-in functions
          Just (VarAV _ op_var)
            | op_var `isPyonBuiltin` the_copy ->
                case ty_args
                of [ty] -> rwCopyApp inf op' ty args

          Just (VarAV _ op_var) ->
            -- Try to rewrite this application.  If it was rewritten, then
            -- consume fuel.
            ifElseFuel unknown_app $ do
              tenv <- getTypeEnv                  
              rewritten <- rewriteAppInSimplifier inf op_var ty_args args
              case rewritten of 
                Just new_expr -> do
                  consumeFuel     -- A term has been rewritten
                  rwExp new_expr
                Nothing ->
                  -- Try to construct a value for this application
                  case lookupDataConWithType op_var tenv  
                  of Just (type_con, data_con) ->
                       data_con_app type_con data_con op'
                     Nothing ->
                       unknown_app

          _ -> unknown_app
  where
    -- If out of fuel, then don't simplify this expression.  Process arguments.
    -- Operator is already processed.
    use_fuel m = useFuel' unknown_app m

    continue op op_value ty_args args =
      rwAppWithOperator original_expression inf op op_value ty_args args

    unknown_app = do
      (args', _) <- rwExps args
      let new_exp = appE inf op' ty_args args'
      return (new_exp, Nothing)

    -- The term is a data constructor application.  Simplify subexpressions
    -- and rebuild the expression.  Also construct a known value for the term.
    --
    -- Fuel is not consumed because this term isn't eliminated.
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
                etaReduceSingleLambdaFunction True inf f
              eta_reduce e = e

      -- Simplify arguments
      (args', arg_values) <- rwExps eta_reduced_args
      
      -- Construct a value from this expression
      let new_exp = appE inf op' ty_args args'
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
               use_fuel $       -- A 'copy' call has been replaced
               copyStoredValue inf val_type repr src Nothing
             [repr, src, dst] ->
               use_fuel $       -- A 'copy' call has been replaced
               copyStoredValue inf val_type repr src (Just dst)
             _ ->
               internalError "rwCopyApp: Unexpected number of arguments"
    _ -> unknown_source
  where
    -- If out of fuel, then don't simplify this expression.  Process arguments.
    use_fuel m = useFuel' unknown_source m
    
    -- Failed to eliminate the case statement before inspecting subexpressions
    unknown_source = do
      (args', arg_values) <- rwExps args
  
      -- Try to eliminate the statement based on values of subexpressions
      have_fuel <- checkFuel
      case arg_values of
        (_ : src_value@(Just (fromDataAV -> Just (DataValue inf ty fs))) : _)
          | have_fuel -> do
              -- The source is a (partly) known value.  Try to replace the
              -- copy expression by the known value.
              m_new_exp <- createDataConApp inf ty fs
              case m_new_exp of
                Nothing -> rebuild_copy args' arg_values
                Just (new_exp, new_val) -> do
                  consumeFuel
                  
                  -- If an output parameter was given, then apply to the
                  -- output parameter
                  let retval =
                        case args
                        of [_, _]       -> (new_exp, new_val)
                           [_, _, outp] -> (appE defaultExpInfo new_exp [] [outp], Nothing)
                  return retval

        _ -> rebuild_copy args' arg_values

    -- Could not simplify; rebuild expression
    rebuild_copy args' arg_values =
      let new_exp = appE inf copy_op [ty] args'
          new_value = copied_value arg_values
      in return (new_exp, new_value)

    -- Do we know what was stored here?
    copied_value [_, _, _] = Nothing
    copied_value [_, Just src_val] =
      Just $ bigAV $ WriterAV src_val
    copied_value [_, _] = Nothing
    copied_value _ =
      internalError "rwCopyApp: Wrong number of arguments in call"

-- | Rewrite a copy of a Stored value to a deconstruct and construct operation.
--
--   Eventually, we should be able to inline the 'copy' method to avoid this
--   special-case rewrite
copyStoredValue inf val_type repr arg m_dst = do
  tmpvar <- newAnonymousVar ObjectLevel
  let stored_op = ExpM $ VarE defaultExpInfo (pyonBuiltin the_stored)
      make_value = appE inf stored_op [TypM val_type]
                   ([ExpM $ VarE inf tmpvar] ++ maybeToList m_dst)
      alt = AltM $ DeCon { altConstructor = pyonBuiltin the_stored
                         , altTyArgs = [TypM val_type]
                         , altExTypes = []
                         , altParams = [setPatMDmd (Dmd OnceSafe Used) $
                                        patM (tmpvar ::: val_type)]
                         , altBody = make_value}
      new_expr = ExpM $ CaseE inf arg [alt]
  
  -- Try to simplify the new expression further
  rwExp new_expr

rwLet inf bind@(PatM (bind_var ::: bind_rtype) _) val body =
  ifElseFuel rw_recursive_let try_pre_inline
  where
    -- Check if we should inline the RHS _before_ rewriting it
    try_pre_inline = do
      tenv <- getTypeEnv
      case worthPreInlining tenv (patMDmd bind) val of
        Just val -> do
          -- The variable is used exactly once; inline it
          consumeFuel
          (body', body_val) <-
            assumePattern bind $ withKnownValue bind_var val $ rwExp body
          
          -- The local variable goes out of scope, so it must not be mentioned 
          -- by the known value
          let ret_val = forgetVariable bind_var =<< body_val
          rwExpReturn (body', ret_val)
        Nothing -> rw_recursive_let

    rw_recursive_let = rwLetNormal inf bind val body

rwLetNormal inf bind val body = do
  let bind_var = patMVar bind
  (val', val_value) <- rwExp val

  -- Inline the RHS expression, if desirable.  If
  -- inlining is not indicated, then propagate its known
  -- value.
  let local_val_value = fmap (setTrivialValue bind_var) $ val_value

  -- Add local variable to the environment and rewrite the body
  (body', body_val) <-
    assumePattern bind $
    withMaybeValue bind_var local_val_value $
    rwExp body

  -- The local variable goes out of scope, so it must not be mentioned 
  -- by the known value
  let ret_val = forgetVariable bind_var =<< body_val
  
  -- Number of uses may change after simplifying
  let bind' = setPatMDmd unknownDmd bind
  rwExpReturn (ExpM $ LetE inf bind' val' body', ret_val)

rwLetrec inf defs body = withDefs defs $ \defs' -> do
  (body', body_value) <- rwExp body
      
  let local_vars = Set.fromList $ map definiendum $ defGroupMembers defs'
      ret_value = forgetVariables local_vars =<< body_value
  rwExpReturn (ExpM $ LetfunE inf defs' body', ret_value)

rwCase inf scrut alts = do
  tenv <- getTypeEnv
  have_fuel <- checkFuel
  rwCase1 have_fuel tenv inf scrut alts

-- Special-case handling of the 'boxed' constructor.  This constructor cannot
-- be eliminated.  Instead, its value is propagated, and we hope that the case
-- statement becomes dead code.
--
-- The case statement isn't eliminated, so this step doesn't consume fuel.
rwCase1 _ _ inf scrut alts
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
            case scrut_val >>= fromDataAV
            of Just (DataValue { dataValueType = ConValueType c _ _
                               , dataFields = [f]})
                 | c `isPyonBuiltin` the_boxed -> f
               _ -> Nothing

      alt' <- rwAlt scrutinee_var (Just ([], [field_val])) alt

      -- Rebuild a new case expression
      return (ExpM $ CaseE inf scrut' [alt'], Nothing)

-- If this is a case of data constructor, we can unpack the case expression
-- before processing the scrutinee.
--
-- Unpacking consumes fuel
rwCase1 have_fuel tenv inf scrut alts
  | have_fuel,
    Just (dcon, ty_args, ex_args, args) <- unpackDataConAppM tenv scrut = do
      consumeFuel
      let alt = findAlternative alts $ dataConCon dcon
          field_kinds = dataConFieldKinds tenv dcon
      eliminateCaseWithExp tenv field_kinds (map TypM ex_args) args alt
  
  | have_fuel,
    ExpM (UTupleE _ fields) <- scrut = do
      consumeFuel
      case alts of
        [alt@(AltM (DeTuple params body))] ->
          let field_kinds = map (toBaseKind . typeKind tenv . patMType) params
          in eliminateCaseWithExp tenv field_kinds [] fields alt
        _ -> internalError "rwCase: Invalid case-of-tuple expression"

-- Simplify the scrutinee, then try to simplify the case statement.
rwCase1 _ tenv inf scrut alts = do
  -- Simplify scrutinee
  (scrut', scrut_val) <- rwExp scrut

  -- Try to deconstruct the new scrutinee expression
  ifElseFuel (can't_deconstruct scrut' scrut_val) $
    case makeDataExpWithAbsValue tenv scrut' scrut_val alts
    of Just app_with_value -> do
         -- Scrutinee is a constructor application that can be eliminated
         consumeFuel
         eliminateCaseWithAppAndValue False tenv app_with_value alts
       _ ->
         -- Can't deconstruct.  Propagate values and rebuild the case
         -- statement.
         can't_deconstruct scrut' scrut_val
  where
    can't_deconstruct scrut' scrut_val = rwCase2 inf alts scrut' scrut_val

-- | A data constructor expression 
data DataExpAndValue =
    -- | A data or tuple constructor application with arguments
    ConAppAndValue !DataValueType [(ExpM, MaybeValue)]

-- | Given an expression and its abstract value, deconstruct the
--   expression as if it were a data constructor application.
--
--   Return the components of the expression and the abstract values of
--   its fields.
makeDataExpWithAbsValue :: TypeEnv -> ExpM -> MaybeValue -> [AltM]
                        -> Maybe DataExpAndValue
makeDataExpWithAbsValue tenv expression expression_value alts =
  case unpackDataConAppM tenv expression
  of Just (data_con, ty_args, ex_args, args) ->
       -- This is a data constructor application
       case expression_value
       of Just (fromDataAV -> Just (DataValue _ dcon vs)) ->
            case dcon
            of ConValueType con _ ex_ts
                 | con == dataConCon data_con ->
                   Just $ ConAppAndValue dcon (zip args vs)
               _ ->
                   internalError "rwCase: Inconsistent constructor value"
          _ ->
            let dcon = ConValueType { dataCon = dataConCon data_con
                                    , dataTyArgs = map TypM ty_args
                                    , dataExTypes = map TypM ex_args}
            in Just $ ConAppAndValue dcon [(arg, Nothing) | arg <- args]
     _ ->
       case expression
       of ExpM (UTupleE _ fields) ->
            -- This is a tuple constructor term
            case alts
            of [AltM (DeTuple params _)] ->
                 let dcon = TupleValueType (map (TypM . patMType) params)
                 in Just $ ConAppAndValue dcon [(arg, Nothing) | arg <- fields]
               _ ->
                 internalError "rwCase: Inconsistent constructor value"
          _ -> Nothing

-- | Eliminate a case statement whose scrutinee was determined to be a
--   data constructor application.
eliminateCaseWithAppAndValue
  is_inspector tenv (ConAppAndValue con_type args_and_values) alts =
  let (field_kinds, ex_args, alt) =
        case con_type
        of ConValueType {dataCon = dcon, dataExTypes = ts} ->
             (case lookupDataCon dcon tenv
              of Just dc -> dataConFieldKinds tenv dc,
              ts,
              findAlternative alts dcon)
           TupleValueType ty_args ->
             (map (toBaseKind . typeKind tenv . fromTypM) ty_args,
              [],
              case alts of [alt] -> alt)
  in eliminateCaseWithSimplifiedExp
     is_inspector tenv field_kinds ex_args args_and_values alt

-- | Rewrite a case statement after rewriting the scrutinee.
--   The case statement cannot be eliminated by deconstructing the scrutinee
--   expression, because the scrutineee expression is not a data constructor
--   application.
--   If the scrutinee has a known value, it may still be possible to eliminate
--   the case statement.
rwCase2 inf alts scrut' scrut_val =
  case scrut_val
  of Just (fromDataAV -> Just (DataValue _ dcon field_values)) -> do
       have_fuel <- checkFuel
       case mapM (>>= asTrivialValue) field_values of
         Just field_exps | have_fuel -> do
           -- All fields can be represented as expressions. 
           -- The case statement can be eliminated.
           consumeFuel
           tenv <- getTypeEnv
           let data_value = ConAppAndValue dcon (zip field_exps field_values)
           eliminateCaseWithAppAndValue True tenv data_value alts
         Nothing -> do
           -- Cannot eliminate the case statement. 
           -- However, we may have eliminated some case alternatives. 
           let known_values =
                 case dcon 
                 of ConValueType {dataExTypes = []} -> Just ([], field_values)
                    -- The case alternative will bind existential types
                    -- to fresh variables.  If there are existential
                    -- types, then field values cannot be propagated
                    -- because they'll have their original types, not
                    -- the fresh type names.
                    ConValueType {} -> Nothing
                    TupleValueType {} -> Just ([], field_values)
           let alt =
                 -- The scrutinee has a known constructor
                 -- discard non-matching case alternatives
                 case dcon
                 of ConValueType {dataCon = c} -> findAlternative alts c
                    TupleValueType {} -> case alts of [a] -> a

           alt' <- rwAlt scrut_var known_values alt
           rwExpReturn (ExpM $ CaseE inf scrut' [alt'], Nothing)
     _ -> do
       alts' <- mapM (rwAlt scrut_var Nothing) alts
       rwExpReturn (ExpM $ CaseE inf scrut' alts', Nothing)
  where
    scrut_var =
      -- If the scrutinee is a variable, it will be assigned a known
      -- value while processing each alternative
      case scrut'
      of ExpM (VarE _ v) -> Just v
         _               -> Nothing

-- | Find the alternative matching constructor @con@
findAlternative :: [AltM] -> Var -> AltM
findAlternative alts con =
  case find match_con alts
  of Just alt -> alt
     Nothing -> internalError "rwCase: Missing alternative"
  where
    match_con (AltM (DeCon {altConstructor = c})) = c == con
    match_con (AltM (DeTuple {})) =
      -- The given constructor doesn't build values of the same type as what
      -- this alternative deconstructs
      internalError "findAlternative: Type error detected"

-- | Given the parts of a data constructor application and a list of case
--   alternatives, eliminate the case statement.  None of the given expressions
--   have been simplified yet.
--
--   This creates a new expression, then simplifies it.
--
--   Fuel should be consumed prior to calling this function.
eliminateCaseWithExp :: TypeEnv
                     -> [BaseKind]
                     -> [TypM]
                     -> [ExpM]
                     -> AltM
                     -> LR (ExpM, MaybeValue)
eliminateCaseWithExp
  tenv field_kinds ex_args initializers (AltM alt)
  | length (getAltExTypes alt) /= length ex_args =
      internalError "rwCase: Wrong number of type parameters"
  | length (altParams alt) /= length initializers =
      internalError "rwCase: Wrong number of fields"
  | otherwise = do
      -- Substitute known types for the existential type variables
      params <- substitutePatMs ex_type_subst (altParams alt)
      let subst = ex_type_subst
      body <- substitute subst (altBody alt)

      binders <-
        sequence [makeCaseInitializerBinding k p i
                 | (k, p, i) <- zip3 field_kinds params initializers]

      -- Continue simplifying the new expression
      rwExp $ applyCaseElimBindings binders body
  where
    ex_type_subst =
      substitution [(v, ex_type)
                   | (TyPatM (v ::: _), TypM ex_type) <-
                       zip (getAltExTypes alt) ex_args]

-- | Given a data value and a list of case
--   alternatives, eliminate the case statement.
--
--   This creates a new expression, then simplifies it.
--
--   Fuel should be consumed prior to calling this function.
--
--   This function generates code in two ways, depending on
--   whether the arguments are initializer expressions or not.
eliminateCaseWithSimplifiedExp :: Bool -- ^ Whether fields are given as field values or initializers
                               -> TypeEnv
                               -> [BaseKind] -- ^ Field kinds
                               -> [TypM]     -- ^ Existential type parameters
                               -> [(ExpM, MaybeValue)] -- ^ Initializers or field values, together with their abstract value
                               -> AltM                 -- ^ Case alternative to eliminate
                               -> LR (ExpM, MaybeValue) -- ^ Simplified case alternative and its abstract value
eliminateCaseWithSimplifiedExp
  is_inspector tenv field_kinds ex_args initializers (AltM alt)
  | length (getAltExTypes alt) /= length ex_args =
      internalError "rwCase: Wrong number of type parameters"
  | length (altParams alt) /= length initializers =
      internalError "rwCase: Wrong number of fields"
  | otherwise = do
      -- Substitute known types for the existential type variables
      params <- substitutePatMs ex_type_subst (altParams alt)
      let subst = ex_type_subst
      body <- substitute subst (altBody alt)

      binders <-
        sequence [if is_inspector
                  then makeCaseInspectorBinding p i
                  else makeCaseInitializerBinding k p i
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

-- | Given an expression that was a parameter of a data constructor,
--   bind the field value to a variable.  If the expression was an initializer
--   expression, then a new object must be created and inspected with a case
--   statement.  Otherwise, the value is just assigned to a variable.
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
      ExpM $ LetE defaultExpInfo (setPatMDmd unknownDmd param) initializer body

-- | Given an expression that represents a field of a data constructor,
--   bind the field value to a variable.  This is similar to
--   'makeCaseInitializerBinding', except the binding is always a let-binding.
makeCaseInspectorBinding :: PatM -> ExpM -> LR CaseElimBinding
makeCaseInspectorBinding param initializer = return let_binding
  where
    let_binding = CaseElimBinding $ \body ->
      ExpM $ LetE defaultExpInfo (setPatMDmd unknownDmd param) initializer body

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

           -- Number of uses may increase or decrease after simplifying
           params' = map (setPatMDmd unknownDmd) params
       assume_scrutinee $ assume_params exTypes (zip values params) $ do
         (body', _) <- rwExp body
         return $ AltM $ DeCon con tyArgs exTypes params' body'

     DeTuple params body -> do
       -- If the scrutinee is a variable, add its known value to the environment
       let arg_values = zipWith mk_arg values params
           arg_types = map (TypM . patMType) params
           data_value = tuplePatternValue defaultExpInfo arg_types arg_values
           assume_scrutinee m =
             case scr
             of Just scrutinee_var -> withMaybeValue scrutinee_var data_value m
                Nothing -> m
           -- Number of uses may increase or decrease after simplifying
           params' = map (setPatMDmd unknownDmd) params
       assume_scrutinee $ assume_params [] (zip values params) $ do
         (body', _) <- rwExp body
         return $ AltM $ DeTuple params' body'
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
    
    -- Create a AbsValue argument for a data field.  Use the previous known
    -- value if available, or the variable that the field is bound to otherwise
    mk_arg maybe_val pat =
      case maybe_val
      of Just val -> Just (setTrivialValue (patMVar pat) val)
         Nothing  -> Just (VarAV defaultExpInfo $ patMVar pat)

rwCoerce inf from_t to_t body = do
  -- Are the types equal in this context?
  types_equal <- compareTypes (fromTypM from_t) (fromTypM to_t)
  if types_equal
    then rwExp body             -- Coercion is not necessary
    else do
      (body', _) <- rwExp body
      return (ExpM $ CoerceE inf from_t to_t body', Nothing)

rwFun :: FunM -> LR (FunM, Maybe AbsFunValue)

-- Freshen bound variables to avoid name shadowing, then rename 
rwFun f = rwFun' =<< freshen in_type_env f
  where
    -- If a variable is in scope, it's in the type environment
    in_type_env v =
      withTypeEnv $ \tenv -> return $ isJust $ lookupType v tenv

rwFun' (FunM f) =
  assumeTyPatMs (funTyParams f) $
  assumePatterns (funParams f) $ do
    (body', body_value) <- rwExp (funBody f)
    let aval = abstract_value body_value
    trace_aval aval $ return (FunM $ f {funParams = params', funBody = body'}, aval)
  where
    -- If a parameter isn't dead, its uses may be changed by simplification
    params' = map update_param $ funParams f
      where
        update_param p =
          case multiplicity $ patMDmd p
          of Dead -> p
             _ -> setPatMDmd unknownDmd p

    abstract_value Nothing = Nothing 
    abstract_value (Just val)
      | not (null $ funTyParams f) = Nothing -- Cannot abstract polymorphic functions
      | otherwise = Just $ abstractFunction (funInfo f) (funParams f) val
                    
    trace_aval Nothing x = x
    trace_aval (Just v) x = traceShow (text "DEBUG: Abstracted function:" $$ pprAbsFun v) x

rwDef :: Def Mem -> LR (Def Mem)
rwDef def = mapMDefiniens (liftM fst . rwFun) def

rwExport :: Export Mem -> LR (Export Mem)
rwExport (Export pos spec f) = do
  (f', _) <- rwFun f
  return (Export pos spec f')

-- | Rewrite a definition group.  Then, add the defined functions to the
--   environment and rewrite something else.
withDefs :: DefGroup (Def Mem) -> (DefGroup (Def Mem) -> LR a) -> LR a
withDefs (NonRec def) k = do
  def' <- rwDef def
  assumeDef def' $ withDefValue False def' $ k (NonRec def')

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
    withDefValues True defgroup' $ k defgroup'
  where
    with_wrappers wrs m = foldr (withDefValue True) m wrs

rwModule :: Module Mem -> LR (Module Mem)
rwModule (Module mod_name imports defss exports) =
  -- Add imported functions to the environment.
  -- Note that all imported functions are added--recursive functions should
  -- not be in the import list, or they will be expanded repeatedly
  foldr (withDefValue False) (rw_top_level id defss) imports
  where
    -- First, rewrite the top-level definitions.
    -- Add defintion groups to the environment as we go along.
    rw_top_level defss' (defs:defss) =
      withDefs defs $ \defs' -> rw_top_level (defss' . (defs' :)) defss
    
    -- Then rewrite the exported functions
    rw_top_level defss' [] = do
      exports' <- mapM rwExport exports
      return $ Module mod_name imports (defss' []) exports'

-- | The main entry point for the simplifier
rewriteLocalExpr :: SimplifierPhase
                 -> RewriteRuleSet
                 -> Module Mem
                 -> IO (Module Mem)
rewriteLocalExpr phase ruleset mod =
  withTheNewVarIdentSupply $ \var_supply -> do
    fuel <- readInitGlobalVarIO the_fuel
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
              IntMap.insert (fromIdent $ varID v) (InlAV e) m

    let env = LREnv { lrIdSupply = var_supply
                    , lrRewriteRules = ruleset
                    , lrKnownValues = known_values
                    , lrTypeEnv = tenv
                    , lrDictEnv = denv
                    , lrIntEnv = ienv
                    , lrFuel = fuel
                    , lrPhase = phase
                    }
    runLR (rwModule mod) env

rewriteAtPhase :: SimplifierPhase -> Module Mem -> IO (Module Mem)
rewriteAtPhase phase mod = rewriteLocalExpr phase rules mod
  where
    rules =
      case phase
      of GeneralSimplifierPhase -> generalRewrites
         SequentialSimplifierPhase -> sequential_rewrites
         FinalSimplifierPhase -> sequential_rewrites
      where
        sequential_rewrites =
          combineRuleSets [generalRewrites, sequentializingRewrites]
