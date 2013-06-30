{-| The simplifier.

The simplifier makes a forward sweep through a program, more or less in
execution order, and tries to statically evaluate what it can.

This sweep performs copy propagation, constant propagation,
beta reduction (includes inlining), case-of-known-value elimination,
and some local expression reordering.
-}

{-# LANGUAGE TypeSynonymInstances, FlexibleContexts, Rank2Types,
    ViewPatterns, ConstraintKinds #-}
{-# OPTIONS_GHC -auto-all #-}
module SystemF.Simplifier.Simplify
       (SimplifierPhase(..),
        rewriteLocalExpr,
        rewriteAtPhase)
where

import Prelude hiding(mapM)
import Control.Applicative
import Control.Monad hiding(mapM)
import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
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
import SystemF.Context
import SystemF.Floating2
import SystemF.MemoryIR
import SystemF.Syntax
import SystemF.Rename
import SystemF.IncrementalSubstitution
import SystemF.TypecheckMem
import SystemF.PrintMemoryIR
import SystemF.Simplifier.Rewrite
import SystemF.Simplifier.AbsValue
import SystemF.Simplifier.StreamExp

import Common.Error
import Common.Identifier
import Common.MonadLogic
import Common.Supply
import qualified LowLevel.Syntax as LL
import qualified SystemF.Datatypes.Code
import SystemF.Datatypes.InfoCall
import Type.Compare
import qualified Type.Rename as Rename
import qualified Type.Substitute as Substitute
import Type.Substitute(substitute, freshen, Substitutable(..))
import Type.Type
import Type.Eval
import Type.Environment

import Globals
import GlobalVar

-- TODO: Remove this constrinat
type ReprDictMonad m = ()

-- | Return True if the expression is a variable or literal, False otherwise.
isTrivialExp :: ExpM -> Bool
isTrivialExp (ExpM (VarE {})) = True
isTrivialExp (ExpM (LitE {})) = True
isTrivialExp _                = False

-- | Return True if the expression is an application of the specical function
--   'reify'.  This function turns an initializer into a value, and behaves
--   in some respects like a data constructor.
isReifyApp :: ExpM -> Bool
isReifyApp e = case unpackVarAppM e
               of Just (op, _, _) | op `isCoreBuiltin` The_reify -> True
                  _ -> False

isTrivialOrReifyExp e = isTrivialExp e || isReifyApp e

-- | Get the type of a function containing a substituted expression
functionTypeSM (FunSM (Fun {funTyParams = ty_params
                           , funParams = params
                           , funReturn = ret})) =
  forallType [b | TyPat b <- ty_params] $
  funType (map (patMType . fromPatSM) params) ret

-- | Verify that the argument is an unboxed run-time representation object
checkRepr :: ExpM -> LR ()
checkRepr e = do
  e_ty <- inferExpType e
  case fromVarApp e_ty of
    Just (op, args)
      | op == valInfoV || op == bareInfoV -> return ()
    _ -> internalError $ "checkRepr: Invalid type:\n" ++ show (pprExp e)

-- | Verify that the argument is an unboxed run-time size object
checkSize :: ExpM -> LR ()
checkSize e = do
  e_ty <- inferExpType e
  case fromVarApp e_ty of
    Just (op, args)
      | op == sizeAlignV || op == sizeAlignV -> return ()
    _ -> internalError $ "checkSize: Invalid type:\n" ++ show (pprExp e)

-- | Different features of the simplifier are enabled
--   depending on the stage of compilation.
data SimplifierPhase =
    GeneralSimplifierPhase

    -- | After parallelization, the sequential phase
    --   converts loops to sequential form
  | SequentialSimplifierPhase
  
    -- | Finally, functions are inlined without regard to rewrite rules. 
  | FinalSimplifierPhase

    -- | Transformations that make high-level optimizations harder,
    --   but produce better lowered code, are performed here.
    --   Case-of-case is applied even to single-branch case statements.
    --   The inlining threshold is turned down.
  | PostFinalSimplifierPhase
    deriving(Eq, Ord)

-- | Parts of LREnv that don't change during a simplifier run.  By
--   keeping these in a separate data structure, we reduce the work
--   performed when updating the environment.
data LRConstants =
  LRConstants
  { -- | Variable ID supply
    lrIdSupply :: {-# UNPACK #-}!(Supply VarID)
    
  , lrLLIdSupply :: {-# UNPACK #-}!(IdentSupply LL.Var)

    -- | Set of imported variable IDs, used to decide whether a variable was
    --   defined in the current module
  , lrImportedSet :: !IntSet.IntSet
    
    -- | Active rewrite rules
  , lrRewriteRules :: !RewriteRuleSet

    -- | The current phase.  The phase is constant during a pass of the
    --   simplifier.
  , lrPhase :: !SimplifierPhase
    
    -- | Number of simplification steps to perform.  For debugging, we may
    --   stop simplification after a given number of steps.
    --
    --   If value is negative, then fuel is unlimited.  If value is zero, then
    --   further simplification is not performed.
  , lrFuel :: {-#UNPACK#-}!(IORef Int)
  }

data LREnv =
  LREnv
  { lrConstants :: !LRConstants
    
    -- | Information about the values stored in variables
  , lrKnownValues :: AbsEnv
    
    -- | Types of variables
  , lrTypeEnv :: TypeEnv
    
    -- | Singleton values such as class dictionaries
--  , lrDictEnv :: SingletonValueEnv
    
    -- | The return parameter of the current function, if there is one
  , lrReturnParameter :: !(Maybe PatM)
  }

-- | Simplification either transforms some code, or detects that the code
--   raises an exception and therefore can be replaced by an
--   exception-raising statement.
newtype LR a = LR {runLR :: LREnv -> IO (Maybe a)}

instance Functor LR where
  fmap f (LR g) = LR (\e -> fmap (fmap f) (g e))

instance Applicative LR where
  pure = return
  (<*>) = ap

instance Monad LR where
  {-# INLINE return #-}
  {-# INLINE (>>=) #-}
  return x = LR (\_ -> return (Just x))
  m >>= k = LR $ \env -> do
    m_x <- runLR m env
    case m_x of
      Just x  -> runLR (k x) env
      Nothing -> return Nothing

instance MonadIO LR where
  liftIO m = LR (\_ -> liftM Just m)

instance Supplies LR VarID where
  fresh = LR (\env -> liftM Just $ supplyValue (lrIdSupply $ lrConstants env))
  supplyToST = internalError "supplyToST: Not implemented for LR"

instance TypeEnvMonad LR where
  type EvalBoxingMode LR = UnboxedMode 
  getTypeEnv = LR $ \env -> return $ Just (lrTypeEnv env)

  liftTypeEnvM m = LR $ \env -> liftM Just $ runTypeEnvM (lrTypeEnv env) m

instance EvalMonad LR where
  liftTypeEvalM m = LR $ \env -> do
    liftM Just $ runTypeEvalM m (lrIdSupply $ lrConstants env) (lrTypeEnv env)

{-
instance ReprDictMonad LR where
  withVarIDs f = LR $ \env -> runLR (f $ lrIdSupply $ lrConstants env) env
  withTypeEnv f = LR $ \env -> runLR (f $ lrTypeEnv env) env
  withDictEnv f = LR $ \env -> runLR (f $ lrDictEnv env) env
  localDictEnv f m = LR $ \env ->
    let env' = env {lrDictEnv = f $ lrDictEnv env}
    in runLR m env'
-}

liftFreshVarM :: FreshVarM a -> LR a
liftFreshVarM m = LR $ \env -> do
  liftM Just $ runFreshVarM (lrIdSupply $ lrConstants env) m

getLLVarIdentSupply :: LR (IdentSupply LL.Var)
getLLVarIdentSupply = LR $ \env -> return (Just $ lrLLIdSupply $ lrConstants env)

getRewriteRules :: LR RewriteRuleSet
getRewriteRules = LR $ \env -> return (Just $ lrRewriteRules $ lrConstants env)

getPhase :: LR SimplifierPhase
getPhase = LR $ \env -> return (Just $ lrPhase $ lrConstants env)

getCurrentReturnParameter :: LR (Maybe PatM)
getCurrentReturnParameter = LR $ \env -> return (Just $ lrReturnParameter env)

setCurrentReturnParameter :: Maybe PatM -> LR a -> LR a
setCurrentReturnParameter x m = LR $ \env ->
  let env' = env {lrReturnParameter = x}
  in runLR m env'

clearCurrentReturnParameter = setCurrentReturnParameter Nothing

-- | Stop processing because the current expression will raise an exception.
--   The expression will be replaced with an 'except' expression, up to the
--   innermost enclosing multi-branch @case@ statement or function definition.
propagateException :: LR a
propagateException = LR $ \_ -> return Nothing

-- | If the given computation calls 'propagateException', then return
--   @Nothing@.  Otherwise return the result.
catchException :: LR a -> LR (Maybe a) 
catchException m = LR $ \env -> do
  result <- runLR m env
  return (Just result)

-- | Lift abstract exception values into the 'LR' monad
interpretComputation :: AbsComputation -> LR AbsCode
interpretComputation TopAC           = return topCode
interpretComputation (ReturnAC code) = return code
interpretComputation ExceptAC        = propagateException

interpretComputation' :: UnboxedTypeEvalM AbsComputation -> LR AbsCode
interpretComputation' m = liftTypeEvalM m >>= interpretComputation

lookupKnownValue :: Var -> LR AbsCode
lookupKnownValue v = LR $ \env ->
  return $! Just $! lookupAbstractValue v (lrKnownValues env)

-- | Add a variable's known value to the environment 
withKnownValue :: Var -> AbsCode -> LR a -> LR a
withKnownValue v val m = LR $ \env ->
  let kv' = insertAbstractValue v val $ lrKnownValues env
      env' = env {lrKnownValues = kv'}
  in kv' `seq` env' `seq` runLR m env'
  where
    -- Debugging: Show the known value for this variable
    -- TODO: implement pretty-printing
    trace_assignment =
      traceShow (text "Simpl" <+> pprVar v <+> text "=" <+> pprAbsCode val)

class Definiens t where
  definiensInfo :: t Mem -> ExpInfo
  definiensIsInliningCandidate :: SimplifierPhase -> Def t Mem -> Bool
  definiensValue :: Def t Mem -> LR AbsCode
  definiensTypeSM :: t SM -> Type

instance Definiens Fun where
  definiensInfo = funInfo . fromFunM
  definiensIsInliningCandidate = isInliningCandidate
  definiensValue (Def v _ f) = do
    let fun_info = funInfo $ fromFunM f
    fun_code <- liftTypeEvalM $ lambdaValue f
    return $ labelCodeVar v $ labelCode (ExpM $ LamE fun_info f) fun_code
  definiensTypeSM = functionTypeSM

instance Definiens Ent where
  definiensInfo (FunEnt f) = definiensInfo f
  definiensInfo (DataEnt d) = definiensInfo d

  definiensIsInliningCandidate phase (Def v ann (FunEnt f)) =
    definiensIsInliningCandidate phase (Def v ann f)
  definiensIsInliningCandidate phase (Def v ann (DataEnt d)) =
    definiensIsInliningCandidate phase (Def v ann d)

  definiensValue (Def v ann (FunEnt f)) =
    definiensValue (Def v ann f)
  definiensValue (Def v ann (DataEnt d)) =
    definiensValue (Def v ann d)

  definiensTypeSM (FunEnt f) = definiensTypeSM f
  definiensTypeSM (DataEnt d) = definiensTypeSM d

instance Definiens Constant where
  definiensInfo = constInfo
  definiensIsInliningCandidate phase _ = True
  definiensValue (Def v ann d) =
    return $ labelCodeVar v $ interpretConstant d

  definiensTypeSM = constType
  

-- | Add a function definition's value to the environment.
--
--   The function may or may not be added, depending on its attributes and
--   whether the function is part of a recursive group.
withDefValue :: Definiens t => Def t Mem -> LR a -> LR a
withDefValue def@(Def v _ f) m = do
  phase <- getPhase
  if definiensIsInliningCandidate phase def
    then do val <- definiensValue def
            withKnownValue v val m
    else m

-- | Add a function definition to the environment, but don't inline it
withUninlinedDefValue :: FDef Mem -> LR a -> LR a
withUninlinedDefValue (Def v _ f) m = m

withDefValues defs m = foldr withDefValue m defs

-- | Decide whether a function may be inlined within its own recursive
--   definition group.  The function's attributes are used for the decision.
--
--   We do not take into account here whether it's /beneficial/ to inline the
--   function.
isRecInliningCandidate :: SimplifierPhase -> FDef Mem -> Bool
isRecInliningCandidate _ def =
  -- It's inlinable only if it's a wrapper function
  defIsWrapper def

-- | Decide whether a function may be inlined (outside of its own definition
--   group).  The function's attributes are used for the decision.
--
--   The inlining annotation must allow inlinng.  Furthermore, the function
--   must either be used only once (to avoid code size explosion)
--   or be marked for aggressive inlining.
isInliningCandidate :: SimplifierPhase -> FDef Mem -> Bool
isInliningCandidate phase def = inlining_ok && phase_ok && code_growth_ok
  where
    ann = defAnnotation def
    phase_ok = phasePermitsInlining phase def
    inlining_ok = defAnnInlineRequest ann /= InlNever

    -- Decide whether code growth is reasonable
    code_growth_ok =
      is_wrapper || is_used_once || is_marked_inline || is_small || is_stream
      where
        is_wrapper = defAnnInlinePhase ann == InlWrapper
        is_marked_inline = defAnnInlineRequest ann == InlAggressively
        is_used_once = usesSuggestInlining def

        is_small =
          -- The inlined function will consist of the function body,
          -- and it will replace a function call.  Compare the function
          -- body's size to the threshold plus the function call size.
          let FunM function = definiens def
              num_args = length (funParams function) +
                         length (funTyParams function)
              threshold = fun_size_threshold + num_args + 1
          in expSize (funBody function) `compareCodeSize` threshold

        is_stream =
          -- Does the function return a stream?
          let FunM function = definiens def
          in case fromVarApp $ funReturn function
             of Just (op, _) | op `isCoreBuiltin` The_Stream -> True
                _ -> False

    -- An arbitrary function size threshold.  Functions smaller than this
    -- will be inlined aggressively.
    fun_size_threshold =
      -- Use a low threshold for compiler-inserted join points, because
      -- they generally don't provide useful opportunities for optimization
      if defAnnJoinPoint ann
      then 15
      else -- After the 'Final' phase, reduce the inlining threshold
           -- in order to focus on intraprocedural code cleanup
           if phase < PostFinalSimplifierPhase then 800 else 16

-- | Decide whether the function is good for inlining, based on 
--   its use annotation.  Functions that are used exactly once should be
--   inlined because inlining won't produce growth.
usesSuggestInlining :: FDef a -> Bool
usesSuggestInlining def =
  singleMultiplicity $ multiplicity $ defAnnUses $ defAnnotation def

-- | Decide whether inlining is permitted for the function in the current 
--   simplifier phase, based on its phase annotation.
phasePermitsInlining :: SimplifierPhase -> FDef a -> Bool
phasePermitsInlining phase def =
  let def_phase = defAnnInlinePhase $ defAnnotation def
  in def_phase `seq`
     case phase
     of GeneralSimplifierPhase ->
          case def_phase
          of InlNormal     -> True 
             InlWrapper    -> True
             InlSequential -> False
             InlFinal      -> False
             InlPostfinal  -> False
        SequentialSimplifierPhase ->
          case def_phase
          of InlNormal     -> True 
             InlWrapper    -> True
             InlSequential -> True
             InlFinal      -> False
             InlPostfinal  -> False
        FinalSimplifierPhase ->
          case def_phase
          of InlPostfinal -> False
             _ -> True
        PostFinalSimplifierPhase ->
          True

-- | Add a pattern-bound variable to the environment.  
--   This adds the variable's type to the environment and
--   its dictionary information if it is a dictionary.
--   The pattern must not be a local variable pattern.
assumePattern :: PatM -> LR a -> LR a
assumePattern pat m =
  {- saveReprDictPattern pat $ -} assumePatM pat m

assumePatterns :: [PatM] -> LR a -> LR a
assumePatterns pats m = foldr assumePattern m pats

-- | Add the function definition types to the environment
assumeDefs :: Definiens t => DefGroup (Def t SM) -> LR a -> LR a
assumeDefs defs m = foldr assumeDefSM m (defGroupMembers defs)

assumeDefSM :: Definiens t => Def t SM -> LR a -> LR a
assumeDefSM (Def v ann ent) m =
  let conlike = defAnnConlike ann
  in assumeWithProperties v (definiensTypeSM ent) conlike m

-- | Print the known values on entry to the computation.
--
--   Known values of imported variables are not printed.
dumpKnownValues :: LR a -> LR a
dumpKnownValues m = LR $ \env ->
  let kv_doc = hang (text "dumpKnownValues") 2 $
               vcat [hang (text (show n)) 8 (pprAbsCode kv)
                    | (n, kv) <- absEnvMembers $ lrKnownValues env,
                      not $ n `IntSet.member` lrImportedSet (lrConstants env)]
  in traceShow kv_doc $ runLR m env

-- | Check whether there is fuel available.
--   If True is returned, then it's okay to perform a task that consumes fuel.
checkFuel :: LR Bool
checkFuel = LR $ \env -> do
  fuel <- readIORef (lrFuel $ lrConstants env)
  return $! Just $! fuel /= 0

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
  fuel <- readIORef $ lrFuel $ lrConstants env
  when (fuel > 0) $ writeIORef (lrFuel $ lrConstants env) $! fuel - 1
  return (Just ())

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
makeExpValue :: ExpM -> LR AbsCode
makeExpValue (ExpM expression) =
  case expression
  of VarE inf v -> do
       mvalue <- lookupKnownValue v
       case codeValue mvalue of
         TopAV -> return $ valueCode $ VarAV v
         _ -> return mvalue
     LitE inf l -> return $ valueCode $ LitAV l
     _ -> return topCode

rewriteAppInSimplifier :: ExpInfo -> Var -> [Type] -> [ExpM] -> LR (Maybe ExpM)
rewriteAppInSimplifier inf operator ty_args args = LR $ \env -> do
  x <- rewriteApp (lrRewriteRules $ lrConstants env)
       -- (intIndexEnv $ lrDictEnv env)
       (lrIdSupply $ lrConstants env) (lrTypeEnv env)
       inf operator ty_args args
  return $ Just x

-------------------------------------------------------------------------------
-- Estimating code size
  
-- | Decide whether some code is below a given size threshold.
--   @checkCodeSize x n@ returns @n - sizeof x@ if @x@ is smaller than @n@,
--   or a nonpositive number otherwise.
newtype CodeSizeTest = CodeSizeTest {checkCodeSize :: Int -> Int}

-- | Return 'True' if the code size turns out to be smaller than the threshold
compareCodeSize :: CodeSizeTest -> Int -> Bool
compareCodeSize t n = checkCodeSize t n > 0

instance Monoid CodeSizeTest where
  mempty = CodeSizeTest id
  f1 `mappend` f2 = CodeSizeTest $ \space ->
    let space' = checkCodeSize f1 space
    in if space' <= 0 then 0 else checkCodeSize f2 space'

codeSize :: Int -> CodeSizeTest
codeSize n = CodeSizeTest (\space -> space - n)

-- | Decide whether a function's code size is less than the given cutoff.
expSize :: ExpM -> CodeSizeTest
expSize (ExpM expression) =
  case expression
  of VarE {} -> codeSize 1
     LitE {} -> codeSize 1
     ConE _ con sps ty_ob es -> codeSize 1 `mappend` expSizes (sps ++ maybeToList ty_ob ++ es)
     AppE _ op ts args -> codeSize 1 `mappend` expSizes (op : args)
     LamE _ f -> funSize f
     LetE _ b rhs body -> codeSize 1 `mappend` expSize rhs `mappend` expSize body
     LetfunE _ defs body ->
       mconcat (expSize body : map (funSize . definiens) (defGroupMembers defs))
     CaseE _ scr sps alts -> expSize scr `mappend` expSizes sps `mappend` alt_sizes alts
     ExceptE {} -> codeSize 1
     CoerceE _ _ _ b -> codeSize 1 `mappend` expSize b
     ArrayE _ _ es -> codeSize 1 `mappend` expSizes es
  where
    alt_sizes xs = mconcat $ map alt_size xs
    alt_size (AltM (Alt decon ty_ob params body)) =
      codeSize (1 + length params) `mappend` expSize body
    
expSizes :: [ExpM] -> CodeSizeTest
expSizes es = mconcat $ map expSize es

funSize :: FunM -> CodeSizeTest
funSize (FunM function) =
  codeSize (length (funTyParams function) + length (funParams function))
  `mappend` expSize (funBody function)

funIsSmallerThan :: FunM -> Int -> Bool
funIsSmallerThan f n = compareCodeSize (funSize f) n

-------------------------------------------------------------------------------
-- Inlining

-- | Decide whether to inline the expression, which is the RHS of an
--   assignment, /before/ simplifying it.  If inlining is indicated, it
--   must be possible to replace all occurrences of the assigned variable
--   with the inlined value; to ensure this, reference values are never
--   pre-inlined.  Pre-inlining is performed only if it does not duplicate
--   code or work.
worthPreInlining :: Dmd -> Type -> ExpM -> TypeEnvM UnboxedMode Bool
worthPreInlining dmd ty expr =
  let should_inline =
        case multiplicity dmd
        of OnceSafe -> inlckTrue
           OnceUnsafe -> inlckTrivial `inlckOr`
                         inlckFunction `inlckOr`
                         inlckConlike
           _ -> inlckTrivial
  in should_inline dmd expr
  where
    is_function_type = case ty of {FunT {} -> True; _ -> False}

-- | Decide whether to inline the bare expression /before/ simplifying it.
--   TODO: We actually want to use different heuristics for copied versus
--   case-inspected expressions.
worthPreInliningBare :: Dmd -> ExpM -> TypeEnvM UnboxedMode Bool
worthPreInliningBare dmd expr =
  case multiplicity dmd
  of OnceSafe -> return True
     ManySafe -> inlckBareDataCon dmd expr

-- | A test performed to decide whether to inline an expression
type InlineCheck = Dmd -> ExpM -> TypeEnvM UnboxedMode Bool

inlckTrue, inlckFalse :: InlineCheck
inlckTrue _ _  = return True
inlckFalse _ _ = return False

inlckBool :: Bool -> InlineCheck
inlckBool b _ _ = return b

inlckOr :: InlineCheck -> InlineCheck -> InlineCheck
infixr 2 `inlckOr`
inlckOr a b dmd e = a dmd e >||> b dmd e

inlckAnd :: InlineCheck -> InlineCheck -> InlineCheck
infixr 3 `inlckAnd`
inlckAnd a b dmd e = a dmd e >&&> b dmd e

-- | Is the expression trivial?
inlckTrivial :: InlineCheck
inlckTrivial _ e = return $ isTrivialExp e

-- | Is the expression a lambda function?
inlckFunction :: InlineCheck
inlckFunction _ (ExpM (LamE {})) = return True
inlckFunction _ _ = return False

-- | Is the expression a duplicatable term?
inlckConlike :: InlineCheck
inlckConlike dmd (ExpM (AppE _ (ExpM (VarE _ op)) _ args)) = do
  m_type_info <- lookupTypeWithProperties op
  case m_type_info of
    Just (_, conlike) | conlike == True ->
      allM ((inlckTrivial `inlckOr` inlckFunction) dmd) args
    _ -> return False

inlckConlike dmd _ = return False

-- | Is the given expression (of kind 'bare') a data constructor application?
--   The arguments must be trivial values (val or box fields) 
--   or bare data constructor applications (bare fields).
inlckBareDataCon :: InlineCheck
inlckBareDataCon dmd (ExpM (ConE _ (VarCon con _ _) sps ty_ob args)) =
  allM (inlckTrivial unknownDmd) sps >&&>
  maybe (return True) (inlckTrivial unknownDmd) ty_ob >&&>
  check_fields
  where
  check_fields = do
    m_dcon <- lookupDataCon con
    case m_dcon of
      Just dcon ->
        let field_kinds = dataConFieldKinds dcon
            check_field BareK arg = inlckBareDataCon unknownDmd arg
            check_field ValK  arg = inlckTrivial unknownDmd arg
            check_field BoxK  arg = inlckTrivial unknownDmd arg
        in andM $ zipWith check_field field_kinds args
      _ -> return False

-- | Create a substitution that pre-inlines the given list of variables
preinlineSubst :: [(Var, ExpM)] -> Subst
preinlineSubst xs = Subst Substitute.empty $ fromListV [(v, SubstitutedVar e) | (v, e) <- xs]

-- | Create a substitution that pre-inlines the given variable
preinlineSubst1 :: Var -> ExpM -> Subst
preinlineSubst1 v e = Subst Substitute.empty $ singletonV v (SubstitutedVar e)

-- | Given a function and its arguments, create an expression equivalent to
--   the function applied to those arguments.  Then, simplify the new
--   expression.
--
--   The created expression consists of a binding for each function parameter,
--   followed by the function body.  The expression is not actually created;
--   instead, the appropriate rewrite methods are called to simplify the
--   expression that would have been created.
betaReduce :: ExpInfo           -- ^ Function call info
           -> ExpM              -- ^ The function expression; only used for debugging
           -> FunM              -- ^ The function value
           -> [Type]            -- ^ Type arguments
           -> [ExpSM]           -- ^ Value arguments
           -> LR (ExpM, AbsCode)
betaReduce inf fun_exp fun ty_args args = do
  -- This wrapper is here to make it easier to print debugging information
  -- before beta reduction
  e <- betaReduce' inf fun ty_args args
  
  {- liftIO $ print (hang (text "betaReduce") 2 $ pprExp fun_exp) -}
  return e

betaReduce' inf (FunM fun) ty_args args
  | n_ty_args < n_ty_params && null args = do
      -- Substitute some type parameters and create a new function
      let leftover_ty_args = drop (length ty_args) $ funTyParams fun

          new_fun = FunM (fun {funTyParams = leftover_ty_args})
          substitution = Subst type_subst emptyV
      rwLam inf =<< freshenFun substitution new_fun

  | n_ty_args > n_ty_params && not (null $ funParams fun) =
        internalError "betaReduce: Type error in application"

  | n_ty_args /= n_ty_params =
      internalError "betaReduce: Type error in application"

  | otherwise = do
      -- Substitute type parameters
      inst_fun <- freshenFun (Subst type_subst emptyV) $
                  FunM (fun {funTyParams = []})

      -- Is the function fully applied?
      let FunSM (Fun fun_inf [] params return_type body) = inst_fun
      case length args `compare` length params of
        LT -> undersaturated_app fun_inf args params body return_type
        EQ -> saturated_app args params body
        GT -> oversaturated_app args params body
  where
    n_ty_args = length ty_args
    n_ty_params = length (funTyParams fun)

    -- Substitution of types for type parameters
    type_subst =
      Substitute.fromList [(tv, t)
                          | (TyPat (tv ::: _), t) <-
                              zip (funTyParams fun) ty_args]

    oversaturated_app args params body = do
      let applied_args = take (length params) args
          excess_args = drop (length params) args

      -- Compute result of function application
      (applied_expr, _) <- saturated_app applied_args params body
     
      -- Apply to other arguments
      subst_excess_args <- mapM applySubstitution excess_args
      let app_expr = ExpM $ AppE inf applied_expr [] subst_excess_args
      rwExp $ deferEmptySubstitution app_expr
  
    saturated_app args params body =
      -- Bind parameters to arguments and rewrite the expression
      caseInspectorBindings (zip params args) (substAndRwExp body)
    
    -- To process an undersaturated application,
    -- assign the parameters that have been applied and 
    -- create a new function that takes the remaining arguments.
    undersaturated_app inf args params body return =
      let applied_params = take (length args) params
          excess_params = drop (length args) params
          new_fun = FunSM $ Fun { funInfo = inf
                                , funTyParams = []
                                , funParams = excess_params
                                , funBody = body
                                , funReturn = return}
          simplify_new_fun subst =
            rwLam inf =<< substitute subst new_fun
      in caseInspectorBindings (zip applied_params args) simplify_new_fun

-- | Insert let-bindings for the parameters of a function that's been inlined
caseInspectorBindings :: [(PatSM, ExpSM)] -> (Subst -> LR (ExpM, AbsCode))
                      -> LR (ExpM, AbsCode)
caseInspectorBindings ((param, initializer):fs) compute_body =
  caseInspectorBinding param initializer $ \subst ->
  caseInspectorBindings fs (apply subst)
  where
    apply subst subst' = compute_body =<< (subst' `composeSubst` subst)

caseInspectorBindings [] compute_body = compute_body emptySubst

-- | Insert a let-binding for a parameter of a function that's been inlined
caseInspectorBinding :: PatSM -> ExpSM -> (Subst -> LR (ExpM, AbsCode))
                     -> LR (ExpM, AbsCode)
caseInspectorBinding param initializer compute_body
  | isDeadPattern (fromPatSM param) = compute_body emptySubst
  | otherwise = rwLet defaultExpInfo param initializer compute_body
  
-------------------------------------------------------------------------------
-- Useless copying

-- | Detect and eliminate useless copying.
--
--   The following specific code patterns (and some minor variations) 
--   are detected by this routine.  In each case, the pattern is simplified to
--   just the expression @E@.
--   The first pattern is let binding a value that could be returned 
--   directly.
--
-- > let x = E in x
--
--   The next is deconstructing a value only to rebuild it.
--
-- > case E of C x y z. C x y z
--
--   The last is initializing a temporary variable, then copying it to another
--   location.
--
-- > case boxed @t E of boxed @t x. copy t r x
eliminateUselessCopying :: ExpSM -> LR ExpSM
eliminateUselessCopying expression = do
  fresh_expression <- freshenHead expression
  case fresh_expression of
    LetE inf bind rhs body -> do
      subst_body <- freshenHead body
      case subst_body of
        VarE _ body_var | patMVar (fromPatSM bind) == body_var ->
          -- Useless let expression
          consumeFuel >> return rhs
        _ -> can't_eliminate

    CaseE inf scrutinee sps alts -> do
      -- Eliminate reconstruction of bare or val data in each alternative.
      -- If scrutinee is a complex expression, don't eliminate, as it may
      -- produce code duplication.
      debug_expr <- applySubstitution expression
      alts1 <-
        case discardSubstitution scrutinee
        of ExpM (VarE {}) -> do
             subst_scrutinee <- applySubstitution scrutinee
             -- Verify that scrutinee didn't become a big expression
             case subst_scrutinee of
               ExpM (VarE {}) -> do
                 mapM (eliminateReconstructor debug_expr subst_scrutinee) alts
               _ -> return alts
           _ -> return alts
  
      -- First, try to detect the case where a value is deconstructed and
      -- reconstructed.
      -- Skip this step for bare types, since we can't avoid copying.
      uses <- do
        scrutinee_kind <- alt_kind (head alts1)
        if scrutinee_kind == BareK
          then return Nothing
          else liftM sequence $ mapM useless_alt alts1

      -- Useless if all alternatives are useless.
      -- In well-typed code, all return parameters must be the same.
      case uses of
        Just (Nothing : _) ->
          consumeFuel >> return scrutinee

        {- TODO: Generate simplified code in this case.
        -- We must get rid of the old return
        -- argument by eta-reducing the scrutinee, then apply it to the new
        -- return argument.

        Just (Just p : _) -> undefined

        -}

        _ -> do
          -- Next, try to detect the case where a value is constructed and
          -- then copied
          elim_case <- eliminate_unbox_and_copy scrutinee alts1
          case elim_case of 
            Nothing -> do -- can't_eliminate
              -- Reconstruct the case expression
              scrutinee' <- applySubstitution scrutinee
              sps' <- mapM applySubstitution sps
              alts1' <- mapM applySubstitutionAlt alts1
              return $ deferEmptySubstitution $ ExpM (CaseE inf scrutinee' sps' alts1')
            Just new_exp -> consumeFuel >> return new_exp

    _ -> can't_eliminate
  where
    can't_eliminate = return expression

    -- Get the kind of the data type being matched
    alt_kind (AltSM (Alt {altCon = VarDeCon var _ _})) = do
      Just (type_con, _) <- lookupDataConWithType var
      return $ dataTypeKind type_con
    
    alt_kind (AltSM (Alt {altCon = TupleDeCon {}})) = return ValK

    -- Try to detect and simplify the pattern
    -- @case boxed E of boxed x. copy x@
    eliminate_unbox_and_copy scrutinee alts = do
      scrutinee' <- freshenHead scrutinee
      case scrutinee' of
        ConE _ (VarCon op [ty_arg] []) _ _ [initializer]
          | op `isCoreBuiltin` The_boxed ->
             case alts
             of [AltSM (Alt _ _ [field] body)] -> do
                  let pattern_var = patMVar $ fromPatSM field
                  -- Check whether body is @copy _ _ x@
                  -- where @x@ is the bound variable
                  body' <- freshenHead body
                  is_copy <- checkForCopyExpr' pattern_var body'
                  if is_copy then return (Just initializer) else do

                    -- Else, check whetehr body is @copy _ _ x e@
                    case body' of
                      AppE _ op [_] [_, copy_src, copy_dst] -> do
                        is_copy <-
                          checkForVariableExpr blockcopyV op >&&>
                          checkForVariableExpr pattern_var copy_src

                        if is_copy
                          then do
                            copy_dst' <- applySubstitution copy_dst
                            initializer' <- applySubstitution initializer
                            return $ Just $ deferEmptySubstitution $
                              appE defaultExpInfo initializer' [] [copy_dst']
                          else return Nothing
                      _ -> return Nothing
                _ -> return Nothing
        _ -> return Nothing

    -- Decide whether the alternative is useless.
    -- Return @Nothing@ if not useless.
    -- Return @Just Nothing@ if useless and there's no return parameter.
    -- Return @Just (Just p)@ if useless and the return parameter is @p@.
    useless_alt (AltSM (Alt decon _ alt_fields body)) = do
      body' <- freshenHead body
      case body' of
        ConE inf con _ _ fields ->
          compare_pattern_to_expression decon alt_fields con fields

        -- TODO: Also detect case where body is applied to a return parameter

        _ -> return Nothing

    -- Compare fields of a pattern to fields of a data constructor expression
    -- to determine whether they match.
    compare_pattern_to_expression decon alt_fields con exp_fields = do
      constructors_match <- matchConPattern decon con
      if constructors_match
        then do
          -- Compare fields
          fields_match <- andM (zipWith match_field alt_fields exp_fields)
          return $! if fields_match then Just Nothing else Nothing
        else
          return Nothing
      where
        -- This field should be @v@ (for a value),
        -- @copy _ v@ (for an initializer), or
        -- @\r. copy _ v r@ (for an initializer).
        -- Check for all possibilities.
        match_field pattern expr = do
          let pattern_var = patMVar (fromPatSM pattern)
          subst_expr <- freshenHead expr
          checkForVariableExpr' pattern_var subst_expr >||>
            checkForCopyExpr' pattern_var subst_expr

-- | Decide whether the deconstructor and constructor are equal
matchConPattern :: DeConInst -> ConInst -> LR Bool
matchConPattern
  (VarDeCon alt_op alt_ty_args alt_ex_types)
  (VarCon exp_op exp_ty_args exp_ex_types) 
  | alt_op /= exp_op = return False
  | otherwise =
    -- Compare type parameters
    andM (zipWith compareTypes alt_ty_args exp_ty_args) >&&>

    -- Compare existential types
    andM (zipWith compareTypes bound_ex_types exp_ex_types)
  where
    bound_ex_types = map (VarT . binderVar) alt_ex_types

matchConPattern (TupleDeCon alt_types) (TupleCon exp_types) 
  | length alt_types /= length exp_types = return False
  | otherwise =
    -- Compare type parameters
    andM (zipWith compareTypes alt_types exp_types)

matchConPattern _ _ = return False

-- | Test whether the expression is a variable expression referencing
--   the given variable.
checkForVariableExpr :: Var -> ExpSM -> LR Bool
checkForVariableExpr v e = checkForVariableExpr' v =<< freshenHead e

checkForVariableExpr' v (VarE _ v') = return $ v == v'
checkForVariableExpr' _ _ = return False

-- | Test whether the expression is an initializer function consisting of 
--   a call to 'copy'.  Check for both the partially applied and eta-expanded
--   forms.
checkForCopyExpr :: Var -> ExpSM -> LR Bool
checkForCopyExpr v e = checkForCopyExpr' v =<< freshenHead e

checkForCopyExpr' v e =
  case e
  of AppE _ op [_] [_, copy_src] ->
       checkForVariableExpr blockcopyV op >&&>
       checkForVariableExpr v copy_src
     LamE _ (FunSM (Fun _ [] [rparam] _ body)) -> do
       let rparam_var = patMVar (fromPatSM rparam)
       subst_body <- freshenHead body
       case subst_body of
         AppE _ op [_] [_, copy_src, copy_dst] ->
           checkForVariableExpr blockcopyV op >&&>
           checkForVariableExpr v copy_src >&&>
           checkForVariableExpr rparam_var copy_dst
         _ -> return False
     _ -> return False

-- | The code to look for when eliminating reconstructors:
--
--   A data constructor term and argument variables.
--   If an argument has kind 'ValK' or 'BoxK', look for the exact argument;
--   otherwise, the argument has kind 'BareK' and look for a 'copy' call.
data ReconstructorTemplate =
  ReconstructorTemplate 
  { tmplDataKind :: !BaseKind 
  , tmplDeCon    :: !DeConInst 
  , tmplFields   :: [(Var, BaseKind)]
  }

-- | In code that deconstructs and then reconstructs a value, replace the 
--   reconstruction with a copy of the original value.
--
--   FIXME: Do this in a separate pass to avoid redundant traversals!
eliminateReconstructor debug_expr scrutinee
    alt@(AltSM (Alt decon ty_ob params body)) = do

  -- Determine the kind of the scrutinee and the object fields
  -- and the type parameters
  (data_kind, field_kinds) <-
    case decon
    of VarDeCon data_con _ _ -> do
         Just (data_type, con_type) <- lookupDataConWithType data_con
         return (dataTypeKind data_type, dataConFieldKinds con_type)
       TupleDeCon fs -> do
         field_kinds <- mapM typeBaseKind fs
         return (ValK, field_kinds)
  let ty_args = deConTyArgs decon
      ex_types = deConExTypes decon
      param_vars = map (patMVar . fromPatSM) params

  let template = ReconstructorTemplate data_kind decon
                 (zip param_vars field_kinds)

  if data_kind /= BareK
    then do
      body' <- eliminateReconstructorTemplate scrutinee template body
      return $ AltSM (Alt decon ty_ob params (deferEmptySubstitution body'))
    else return alt

eliminateReconstructorTemplate scrutinee template body 
  | tmplDataKind template == BareK =
    internalError "eliminateReconstructor: Not implemented for bare types"
  | otherwise = do
    body' <- freshenHead body
    case body' of
      VarE inf v ->
        return $ ExpM $ VarE inf v
      ConE inf op _ _ args -> do
        -- Decide whether to eliminate this term
        con_match <- matchConPattern (tmplDeCon template) op
        if con_match
          then do
            args_match <- andM $ zipWith match_field (tmplFields template) args
            if args_match      
              then do
                -- Can eliminate this term
                return scrutinee
              else freshenFullyExp body
          else freshenFullyExp body
      LetE inf pat rhs body -> do
        rhs' <- recurse rhs
        body' <- assumeBinder (patMBinder $ fromPatSM pat) $ recurse body
        return $ ExpM $ LetE inf (fromPatSM pat) rhs' body'
      _ -> freshenFullyExp body
  where
    recurse e = eliminateReconstructorTemplate scrutinee template e

    match_field :: (Var, BaseKind) -> ExpSM -> LR Bool
    match_field (var, kind) field_exp
      | kind == ValK || kind == BoxK =
        checkForVariableExpr var field_exp
      | kind == BareK =
        checkForCopyExpr var field_exp

-------------------------------------------------------------------------------
-- Traversing code

-- | Apply a substitution, then rewrite an expression.
substAndRwExp :: ExpSM -> Subst -> LR (ExpM, AbsCode)
substAndRwExp e s = rwExp =<< substitute s e

rwMaybeExp Nothing  = return (Nothing, Nothing) 
rwMaybeExp (Just e) = do (e, c) <- rwExp e
                         return (Just e, Just c)

-- | Rewrite an expression.
--
--   Return the expression's value if it can be determined.
rwExp :: ExpSM -> LR (ExpM, AbsCode)
rwExp expression =
  debug "rwExp" expression $
  ifElseFuel (substitute expression) (rewrite expression)
  where
    -- Don't rewrite the expression.
    -- Just apply the current substitution, and return.
    substitute expression = do
      exp' <- applySubstitution expression
      return (exp', topCode)

    -- Rewrite the expression.
    -- First perform local restructuring, then simplify.
    rewrite expression = do
      ex2 <- ifFuel expression $ eliminateUselessCopying expression
      ifElseFuel (substitute ex2) (simplify ex2)

    -- Simplify the expression.
    simplify expression = do
      -- Rename variables to avoid name conflicts
      ex3 <- freshenHead expression

      -- Simplify subexpressions.
      --
      -- Even if we're out of fuel, we _still_ must perform some simplification
      -- steps in order to propagate 'InlAV's.  If we fail to propagate
      -- them, the output code will still contain references to variables that
      -- were deleted.
      case ex3 of
        VarE inf v -> rwVar inf v
        LitE inf l -> rwExpReturn (ExpM (LitE inf l), valueCode $ LitAV l)
        ConE inf con sps ty_ob args -> rwCon inf con sps ty_ob args
        AppE inf op ty_args args -> rwApp ex3 inf op ty_args args
        LamE inf fun -> rwLam inf fun
        LetE inf bind val body ->
          rwLet inf bind val (substAndRwExp body)
        LetfunE inf defs body -> rwLetrec inf defs body
        CaseE inf scrut sps alts -> rwCase inf scrut sps alts
        ExceptE _ _ -> propagateException
        CoerceE inf from_t to_t body ->
          rwCoerce inf from_t to_t body
        ArrayE inf ty es ->
          rwArray inf ty es 

    debug _ _ = id

    {- debug l e m = do
      ret@(e', _) <- m
      shadowing <- traceShow (text "R" <+> pprExp e') $ checkForShadowingExpHere e'
      shadowing `seq` return ret -}

    {- debug l e m = do
      e' <- applySubstitution e
      traceShow (text l <+> pprExp e') m -}

    -- Print abstract values
    {-debug l e m = do
      ret@(_, av) <- m
      traceShow (text l <+> (pprExp e $$ text "----" $$ pprAbsCode av)) $ return ret
    -}
    {-debug l e m = do
      ret@(e', _) <- m
      traceShow (text l <+> (pprExp e $$ text "----" $$ pprExp e')) $ return ret
    -}

-- | Rewrite a list of expressions that are in the same scope,
--   such as arguments of a function call.
rwExps :: [ExpSM] -> LR ([ExpM], [AbsCode])
rwExps es = mapAndUnzipM rwExp es

rwExpReturn (exp, val) = return (exp, val)
    
-- | Rewrite a variable expression and compute its value.
--
--   It is assumed that fuel is available when this expression is called.
rwVar inf v = lookupKnownValue v >>= rewrite
  where
    original_expression = ExpM $ VarE inf v

    rewrite val
      | Just cheap_value <- codeTrivialExp val = do
          -- Use fuel to replace this variable
          consumeFuel
          rwExpReturn (cheap_value, val)

        -- Otherwise, don't inline, but propagate the value.
        -- Label the value if it's not already labeled.
      | otherwise =
          rwExpReturn (original_expression, labelCodeVar v val)

rwLam :: ExpInfo -> FunSM -> LR (ExpM, AbsCode)
rwLam inf fun = do
  -- First try to eta-reduce
  restructured <- restructureLamExp inf fun
  case restructured of
    Nothing -> do
      (fun', fun_val) <- rwFun fun
      rwExpReturn (ExpM $ LamE inf fun', fun_val)

    Just e -> rwExp $ deferEmptySubstitution e

-- | Try to restructure a lambda expression.
--
-- If function is of the form (\x. E x) where E doesn't mention x,
-- then replace it with E.
--
-- This is especially important when 'E' is a constructor application,
-- because some other optimizations are enabled for terms containing 
-- constructor applications but not terms containing lambdas.
restructureLamExp inf fun@(FunSM (Fun fun_inf ty_params params ret body))
  | null ty_params, [param] <- params = do
      let param_var = patMVar $ fromPatSM param
      body' <- freshenHead body
      case body' of
        AppE body_inf body_op body_ty_args body_args
          | not $ null body_args -> do
              -- Body is a function application
              let last_arg = last body_args
                  first_args = init body_args

              -- Check whether last argument is the parameter variable
              last_arg' <- freshenHead last_arg
              case last_arg' of
                VarE _ v | v == param_var -> do

                  -- Make sure parameter isn't mentioned in other expressions
                  body_op' <- applySubstitution body_op
                  first_args' <- mapM applySubstitution first_args
                  if any ((param_var `Set.member`) . Rename.freeVariables)
                     (body_op' : first_args')
                    then return Nothing
                    else let reduced_body =
                               appE body_inf body_op' body_ty_args first_args'
                         in return $ Just reduced_body

                _ -> return Nothing
        _ -> return Nothing
  | otherwise = return Nothing


rwCon :: ExpInfo -> ConInst -> [ExpSM] -> Maybe ExpSM -> [ExpSM]
      -> LR (ExpM, AbsCode)
rwCon inf con sps ty_ob args = do
  -- Simplify fields
  (sps', sps_values) <- clearCurrentReturnParameter $ rwExps sps
  (ty_ob', ty_ob_value) <-
    clearCurrentReturnParameter $ rwMaybeExp ty_ob
  (args', arg_values) <- clearCurrentReturnParameter $ rwExps args

  -- Simplify the constructor's type arguments
  con' <- liftTypeEvalM $ simplifyCon con

  -- Interpret the constructor's value
  new_val <- interpretComputation' $
             interpretCon con' ty_ob_value sps_values arg_values
  let new_exp = ExpM $ ConE inf con' sps' ty_ob' args'
  return (new_exp, new_val)

-- | Simplify type arguments of a constructor.
--   This can slightly reduce the intermediate code size.
simplifyCon (VarCon op ty_args ex_types) = do
  ty_args' <- mapM reduceToWhnf ty_args
  ex_types' <- mapM reduceToWhnf ex_types
  return $ VarCon op ty_args' ex_types'

simplifyCon (TupleCon ty_args) = do
  ty_args' <- mapM reduceToWhnf ty_args
  return $ TupleCon ty_args'

rwApp :: BaseExp SM -> ExpInfo -> ExpSM -> [Type] -> [ExpSM]
      -> LR (ExpM, AbsCode)
rwApp original_expression inf op ty_args args = do
  (op', ty_args', args') <- preUncurryApp inf op ty_args args

  -- Simplify type arguments
  ty_args'' <- mapM reduceToWhnf ty_args'

  case op' of
    Left op_exp ->
      rwAppOperator inf op_exp ty_args'' args'
    Right (case_inf, scr, sps, alts) ->
      rwAppOfCase inf case_inf scr sps alts ty_args'' args'

-- Try to uncurry this application.  The operator and arguments have not been
-- rewritten.
--
-- If the operator is a case expression, then deconstruct the case expression;
-- there is a special code path to handle case statements.
preUncurryApp :: ExpInfo -> ExpSM -> [Type] -> [ExpSM]
              -> LR (Either ExpSM (ExpInfo, ExpSM, [ExpSM], [AltSM]), [Type], [ExpSM])
preUncurryApp inf op ty_args args = do
  op' <- freshenHead op
  case op' of
    AppE _ inner_op inner_ty_args inner_args
      | null ty_args ->
          continue inner_op inner_ty_args (inner_args ++ args)
      | null inner_args ->
          continue inner_op (inner_ty_args ++ ty_args) args
    CaseE case_inf scr sps alts ->
      return (Right (case_inf, scr, sps, alts), ty_args, args)
    _ -> return (Left op, ty_args, args)
  where
    continue op ty_args args =
      preUncurryApp inf op ty_args args

-- | Convert an app-of-case expression to a case-of-app expression.
--   To avoid duplicating code across all case branches,
--   the arguments are bound to new variables.
--
-- > (case x of {C. e1}) e2
--
-- becomes
--
-- > let z = e2 in case x of C. e1 z
rwAppOfCase :: ExpInfo -> ExpInfo -> ExpSM -> [ExpSM] -> [AltSM] -> [Type]
            -> [ExpSM]
            -> LR (ExpM, AbsCode)
rwAppOfCase inf case_inf scr sps alts ty_args args = do
  scr' <- applySubstitution scr
  sps' <- mapM applySubstitution sps
  restructured_exp <- withMany bind_argument args $ \args' -> do
    alts' <- mapM (insert_app inf ty_args args') alts
    return $ ExpM $ CaseE case_inf scr' sps' alts'

  -- Rewrite the new expression
  rwExp $ deferEmptySubstitution restructured_exp
  where
    bind_argument arg k = do
      -- Bind the argument to a variable.
      -- The variable will be used once in each case alternative, so
      -- annotate the argument with 'ManySafe' multiplicity.
      let_var <- newAnonymousVar ObjectLevel
      arg' <- applySubstitution arg
      arg_type <- inferExpType arg'
      let pat = setPatMDmd (Dmd ManySafe Used) $ patM (let_var ::: arg_type)
      new_expr <- k arg'
      return $ ExpM $ LetE inf pat arg' new_expr

    -- Put a function application term inside a case alternative
    insert_app inf ty_args args altm = do
      AltM (Alt decon ty_ob params body) <- applySubstitutionAlt altm
      return $ AltM $ Alt decon ty_ob params (appE inf body ty_args args)

rwAppOperator inf op ty_args args =
  clearCurrentReturnParameter $ do
    (op', op_val) <- rwExp op
    rwAppWithOperator inf op' op_val ty_args args

-- | Rewrite an application, depending on what the operator is.
--   The operator has been simplified, but the arguments have not.
--
--   This function is usually called from 'rwApp'.  It calls itself 
--   recursively to flatten out curried applications.
rwAppWithOperator :: ExpInfo -> ExpM -> AbsCode
                  -> [Type] -> [ExpSM] -> LR (ExpM, AbsCode)
rwAppWithOperator inf op op_val ty_args args = do
  -- First, try to uncurry this application.
  -- This happens if the operator was rewritten to an application;
  -- otherwise we would have uncurried it in 'rwApp'.
  (op', op_val', ty_args', args') <- postUncurryApp inf op op_val ty_args args
  rwAppWithOperator' inf op' op_val' ty_args' args'

postUncurryApp inf op op_val ty_args args =
  case op
  of ExpM (AppE _ inner_op inner_ty_args inner_args)
       | null ty_args -> do
           inner_op_value <- makeExpValue inner_op
           continue inner_op inner_op_value
             inner_ty_args
             (map deferEmptySubstitution inner_args ++ args)
       | null inner_args -> do
           inner_op_value <- makeExpValue inner_op
           continue inner_op inner_op_value
             (inner_ty_args ++ ty_args) args
     _ -> return (op, op_val, ty_args, args)
  where
    continue op op_value ty_args args =
      postUncurryApp inf op op_value ty_args args

rwAppWithOperator' inf op op_val ty_args args =
  -- Apply simplification techniques specific to this operator.
  -- Fuel must be available to simplify.
  ifElseFuel unknown_app $
  case op
  of ExpM (LamE _ f) ->
       consumeFuel >> inline_function_call op f
     _ ->
       case codeExp op_val
       of Just (ExpM (LamE _ f)) ->
            trace_inlining $ consumeFuel >> inline_function_call op f

          -- Use special rewrite semantics for built-in functions
          Just (ExpM (VarE _ op_var))
            | Just f <- lookupBuiltinFunctionSimplifier
                        (length ty_args) (length args) op_var ->
                f inf ty_args args

            | otherwise -> do
                -- Try to apply a rewrite rule
                (args', arg_values) <- rwExps args
                rewritten <- rewriteAppInSimplifier inf op_var ty_args args'
                case rewritten of
                  Just new_expr -> do
                    consumeFuel     -- A term has been rewritten
                    rwExp $ deferEmptySubstitution new_expr

                  Nothing ->
                    rebuild_app args' arg_values
          _ -> unknown_app
  where
    -- If out of fuel, then don't simplify this expression.  Process arguments.
    -- Operator is already processed.
    use_fuel m = useFuel' unknown_app m

    -- No simplifications are applicable to this term
    unknown_app = do
      (args', arg_values) <- rwExps args
      rebuild_app args' arg_values

    -- Reconstruct an application term
    rebuild_app args' arg_values = do
      -- Compute the application's value, and detect if it raises an exception
      new_value <- interpretComputation' $ applyCode op_val ty_args arg_values

      let new_exp = appE inf op ty_args args'
      return (new_exp, new_value)

    -- Inline the function call and continue to simplify it.
    -- The arguments will be processed after inlining.
    inline_function_call op_exp funm = betaReduce inf op_exp funm ty_args args

    -- Change this to print out the names of direct-called functions that
    -- get inlined
    trace_inlining x = x
    {-
    trace_inlining x = traceShow (text "Inlining" <+> pprExp op) x
    -}

-- | Special simplification rules for applications of built-in functions.
--   The key is the variable ID of the function name.
--   Each value in the map consists of:
--   * Number of type parameters required
--   * Minimum number of value parameters required
--   * Simplifier function
builtinFunctionSimplifiers ::
  IntMap.IntMap (Int, Int, ExpInfo -> [Type] -> [ExpSM] -> LR (ExpM, AbsCode))
builtinFunctionSimplifiers =
  IntMap.fromList [(fromIdent $ varID v, (a, b, c)) | (v, a, b, c) <- entries]
  where
    entries =
      [ (blockcopyV, 1, 2, rwCopyApp)
      , (coreBuiltin The_eqI, 0, 2, rwIntEqApp)
      , (coreBuiltin The_and, 0, 2, rwAndApp)
      ]

lookupBuiltinFunctionSimplifier n_ty_args n_args op_var =
  case IntMap.lookup (fromIdent $ varID op_var) builtinFunctionSimplifiers
  of Just (expected_ty_args, expected_args, f)
       | n_ty_args == expected_ty_args && n_args >= expected_args -> Just f
     _ -> Nothing

-- | Attempt to statically evaluate a copy.
--   Requires two or three arguments.

{- -- One argument.  Cannot optimize.
rwCopyApp inf copy_op ty [repr] = do
  (repr', _) <- rwExp False repr
  return (appE inf copy_op [ty] [repr'], topCode) -}

rwCopyApp inf [ty] args = debug $
  -- Rewrite @blockcopy _ _ (reify _ E)@ to @E@
  case args
  of (size_arg : src : rest) -> do
       let maybe_dst = case rest
                       of []  -> Nothing
                          [e] -> Just e
                          _ -> wrong_number_of_arguments
       src' <- freshenHead src
       case src' of
         AppE _ src_op _ [src_arg] -> do
           src_op' <- freshenHead src_op
           case src_op' of
             VarE _ src_op_var
               | src_op_var `isCoreBuiltin` The_reify ->
                   -- Rewrite to src_arg.  Apply the argument from 'maybe_dst'
                   -- if it exists.
                   case maybe_dst
                   of Nothing -> rwExp src_arg
                      Just e  -> do
                        src_arg' <- applySubstitution src_arg
                        e' <- applySubstitution e
                        rwExp $ deferEmptySubstitution $ appE' src_arg' [] [e']
             _ -> rwCopyApp1 inf ty size_arg src maybe_dst
         _ -> rwCopyApp1 inf ty size_arg src maybe_dst
     _ -> wrong_number_of_arguments
  where
    debug m = m

    {-debug m = do
      x@(e, _) <- m
      args' <- mapM applySubstitution args
      traceShow (hang (text "rwCopyApp") 2 $
             pprExp (appE inf copy_op [ty] args') $$ text "----" $$ pprExp e) $ return x
    -}

    copy_op = varE inf blockcopyV

    wrong_number_of_arguments :: a
    wrong_number_of_arguments =
      internalError "rwCopyApp: Unexpected number of arguments"

rwCopyApp1 inf ty size src m_dst = do
  whnf_type <- reduceToWhnf ty
  case fromVarApp whnf_type of
    Just (op, [val_type]) | op == storedV ->
      -- Specialize to deconstruct the argument and construct the result
      copyStoredValue inf val_type size src m_dst
    _ -> do
      (size', size_value) <- rwExp size
      (src', src_value) <- rwExp src
      maybe_dst_result <- mapM rwExp m_dst
  
      -- Compute the value of the function call.  First, compute the value 
      -- of 'copy' applied to the source value.
      src_type <- inferExpType src'
      let src_initializer_type = writerType src_type
      src_initializer <- liftTypeEvalM $ initializerValue src_value src_type

      -- If a destination was given, apply the value.
      new_value <- 
        case maybe_dst_result
        of Nothing -> return src_initializer
           Just (_, dst_value) ->
             interpretComputation' $ applyCode src_initializer [] [dst_value]

      let rebuild_copy_expr =
            -- Rebuild the copy expression with simplified arguments
            let rebuilt_args =
                  size' : src' : fmap fst (maybeToList maybe_dst_result)
                new_exp = appE inf copy_op [ty] rebuilt_args
            in return (new_exp, new_value)

      let create_initializer = do
             -- Create an initializer expression from the source, if possible
            src_initializer_expr <-
              liftTypeEvalM $ concretize src_initializer_type src_initializer

            case src_initializer_expr of
              Nothing -> rebuild_copy_expr
              Just e -> do
                consumeFuel
                case maybe_dst_result of
                  Nothing ->
                    return (e, new_value)
                  Just (dst', dst_value) ->
                    return (appE defaultExpInfo e [] [dst'], new_value)

      ifElseFuel rebuild_copy_expr create_initializer
  where
    copy_op = varE inf blockcopyV

-- | Rewrite a copy of a Stored value to a deconstruct and construct operation.
--
-- > case x of stored y. stored y
copyStoredValue inf val_type repr arg m_dst = do
  tmpvar <- newAnonymousVar ObjectLevel
  arg' <- applySubstitution arg
  m_dst' <- mapM applySubstitution m_dst

  let -- Construct a stored value
      stored_con = VarCon stored_conV [val_type] []
      value = conE inf stored_con [] Nothing [ExpM $ VarE inf tmpvar]
      result_value = case m_dst'
                     of Nothing  -> value
                        Just dst -> appE inf value [] [dst]

      -- Deconstruct the original value
      stored_decon = VarDeCon stored_conV [val_type] []
      alt = AltM $ Alt { altCon = stored_decon
                       , altTyObject = Nothing
                       , altParams = [setPatMDmd (Dmd OnceSafe Used) $
                                      patM (tmpvar ::: val_type)]
                       , altBody = result_value}
      new_expr = ExpM $ CaseE inf arg' [] [alt]
  
  -- Try to simplify the new expression further
  rwExp $ deferEmptySubstitution new_expr

rwIntEqApp inf [] [arg1, arg2] = do
  -- Evaluate arguments
  (arg1', val1) <- rwExp arg1
  (arg2', val2) <- rwExp arg2

  let
    can't_simplify =
      return (appE inf eq_op [] [arg1', arg2'], topCode)

    rewrite_value_prop var lit =
      -- Can't simplify.  However, if the result is True, then 
      -- we can replace 'var' by 'lit'.
      return (appE inf eq_op [] [arg1', arg2'], varEqualityTestCode var lit)

    -- Since this is an int equality test, literal arguments are integers
    -- and we can evaluate them immediately.
    test_equality (IntL n1 _) (IntL n2 _)
      | n1 == n2 = return_true
      | otherwise = return_false
    test_equality _ _ = internalError "rwIntEqApp: Not an integer"

    return_true =
      -- Simplified to the constant value 'True'
      return (trueE inf, trueCode)

    return_false =
      -- Simplified to the constant value 'False'
      return (falseE inf, falseCode)

  -- Try to compute value information for this expression
  case codeTrivialExp val1 of
    Just (ExpM (VarE _ v1)) -> 
      case codeTrivialExp val2 of
        Just (ExpM (VarE _ v2))
          -- The expression @x == x@ is always true
          | v1 == v2            -> return_true
          | otherwise           -> can't_simplify
        Just (ExpM (LitE _ l2)) -> rewrite_value_prop v1 l2
        _                       -> can't_simplify
    Just (ExpM (LitE _ l1)) ->
      case codeTrivialExp val2 of
        Just (ExpM (VarE _ v2)) -> rewrite_value_prop v2 l1
        Just (ExpM (LitE _ l2)) -> test_equality l1 l2
        _                       -> can't_simplify
    _ -> can't_simplify
  where
    eq_op = varE inf (coreBuiltin The_eqI)
      
rwAndApp inf [] [arg1, arg2] = do
  -- Evaluate arguments
  (arg1', val1) <- rwExp arg1
  (arg2', val2) <- rwExp arg2

  -- If either argument is a literal 'True', return the other argument
  case () of 
    _ | is_true arg1' -> return (arg2', val2)
      | is_true arg2' -> return (arg1', val1)
      | otherwise ->
          -- Create a conjunction proposition
          return (appE inf and_op [] [arg1', arg2'],
                  conjunctionCode val1 val2)
  where
    and_op = varE inf (coreBuiltin The_and)

    -- Is the given expression a literal 'True'?
    is_true (ExpM (ConE {expCon = con}))
      | summarizeConstructor con == Just (coreBuiltin The_True) = True

    is_true _ = False

-- | Rewrite a let expression.  The expression may be from the input program,
--   or it may have been generated by case elimination or beta reduction.
rwLet :: ExpInfo
      -> PatSM                  -- ^ Let-bound variable
      -> ExpSM                  -- ^ Right-hand side of let expression
      -> (Subst -> LR (ExpM, AbsCode))
         -- ^ Computation that rewrites the body after applying a substitution.
         --   The substitution holds inlining decisions that were made while
         --   processing the binder part of the let expression.
      -> LR (ExpM, AbsCode)
rwLet inf (PatSM bind@(PatM (bind_var ::: _) _)) val simplify_body =
  ifElseFuel rw_recursive_let try_pre_inline
  where
    -- Check if we should inline the RHS _before_ rewriting it
    try_pre_inline = do
      rhs_type <- reduceToWhnf (patMType bind)
      subst_val <- applySubstitution val
      should_pre_inline <-
        liftTypeEnvM $ worthPreInlining (patMDmd bind) rhs_type subst_val
      if should_pre_inline
        then do
          -- The variable is used exactly once or is trivial; inline it.
          -- Since substitution will eliminate the variable before the
          -- simplifier observes it, the variable isn't added to the environment.
          consumeFuel
          simplify_body (preinlineSubst1 bind_var subst_val)
        else rw_recursive_let

    rw_recursive_let = rwLetNormal inf bind val (simplify_body emptySubst)

-- | Rewrite a let expression that isn't pre-inlined.
rwLetNormal inf bind val simplify_body = do
  let bind_var = patMVar bind
  (val', val_value) <- clearCurrentReturnParameter $ rwExp val

  -- Inline the RHS expression, if desirable.  If
  -- inlining is not indicated, then propagate its known
  -- value.
  
  -- If nothing is known about the RHS, there's no point in adding the
  -- abstract value to the environment.  The only thing we know about the
  -- value is that the bound variable represents it.  That case is handled
  -- by the call to 'labelCodeVar' in 'rwVar'.
  let local_val_value = if isTopCode val_value
                        then topCode
                        else labelCodeVar bind_var val_value

  -- Add local variable to the environment and rewrite the body
  (body', _) <-
    assumePattern bind $ withKnownValue bind_var local_val_value simplify_body

  -- Number of uses may change after simplifying
  let bind' = setPatMDmd unknownDmd bind
  rwExpReturn (ExpM $ LetE inf bind' val' body', topCode)

-- | Rewrite a letrec expression, by rewriting the functions and the
--   expression body.  
rwLetrec :: ExpInfo -> DefGroup (FDef SM) -> ExpSM -> LR (ExpM, AbsCode)
rwLetrec inf defs body = do
  phase <- getPhase
  have_fuel <- checkFuel

  case defs of
    -- If the function is nonrecursive and used exactly once, the function is
    -- unconditionally pre-inlined.
    -- Wrapper functions are always pre-inlined.
    -- FIXME: Should use the same code as 'isInliningCandidate'
    NonRec def | have_fuel &&
                 defAnnInlineRequest (defAnnotation def) /= InlNever &&
                 (defIsWrapper def ||
                  usesSuggestInlining def && phasePermitsInlining phase def) -> do
      consumeFuel

      -- Substitute a lambda expression for this variable
      function <- applySubstitutionFun (definiens def)
      let lambda_fun = ExpM $ LamE inf function
          subst = preinlineSubst1 (definiendum def) lambda_fun

      -- Rewrite the body
      rwExp =<< substitute subst body

    NonRec {} -> do
      -- Do not inline this function
      withFDefs defs $ \defs' -> do
        (body', _) <- rwExp body
        rwExpReturn (ExpM $ LetfunE inf defs' body', topCode)

    -- Otherwise, the letrec expression itself is not eliminated.
    -- Wrapper functions are pre-inlined.
    -- (A wrapper function cannot contain a reference to another wrapper function).
    -- Local functions are simplified,
    -- then may be considered for inlining at each callsite.
    Rec rec_defs -> do

      -- Pre-inline wrappers
      let (wrappers, others) = partition defIsWrapper rec_defs
      wrapper_bindings <- forM wrappers $ \wrapper_def -> do
        function <- applySubstitutionFun (definiens wrapper_def)
        return (definiendum wrapper_def, ExpM $ LamE (funInfo $ fromFunM function) function)
      let subst = preinlineSubst wrapper_bindings
      substituted_defs <- mapM (mapMDefiniens $ substitute subst) others
      substituted_body <- substitute subst body

      -- Rewrite other functions
      withFDefs (Rec substituted_defs) $ \defs' -> do
        (body', _) <- rwExp substituted_body
        rwExpReturn (ExpM $ LetfunE inf defs' body', topCode)

rwCase :: ExpInfo -> ExpSM -> [ExpSM] -> [AltSM] -> LR (ExpM, AbsCode)
rwCase inf scrut sps alts = do
  rwCase1 inf scrut sps alts
  where
    -- For debugging, print the case expression that will be rewritten
    debug_print_case :: LR (ExpM, AbsCode) -> LR (ExpM, AbsCode)
    debug_print_case m = do
      scrut' <- applySubstitution scrut
      sps' <- mapM applySubstitution sps
      alts' <- mapM applySubstitutionAlt alts
      let expr = ExpM $ CaseE inf scrut' sps' alts'
      traceShow (text "rwCase" <+> pprExp expr) m

-- | First stages of rewriting a case expression.  Try to simplify the case
--   expression before simplifying subexpressions.
--
--   It is assumed that fuel is available.

-- Special-case handling of the 'boxed' constructor.  This constructor cannot
-- be eliminated.  Instead, its value is propagated, and we hope that the case
-- statement becomes dead code.
--
-- The case statement isn't eliminated, so this step doesn't consume fuel.
rwCase1 inf scrut sps alts
  | [alt@(AltSM (Alt {altCon = VarDeCon op _ _}))] <- alts,
    op `isCoreBuiltin` The_boxed = do
      let [sp] = sps
      let AltSM (Alt _ (Just ty_ob) [binder] body) = alt
      rwLetViaBoxed inf scrut sp ty_ob binder (substAndRwExp body)

-- If this is a case of data constructor, we can unpack the case expression
-- before processing the scrutinee.
--
-- We can peek at the scrutinee using 'discardSubstitution' to see if it's
-- a constructor application.
--
-- Unpacking consumes fuel
rwCase1 inf scrut sps alts
  | ExpM (ConE {}) <- discardSubstitution scrut = eliminate_case scrut
  | otherwise = do
      -- Check for an application of "reify _ E".
      -- If present, the argument E must be a data constructor application.
      scrut' <- freshenHead scrut
      case scrut' of
        AppE _ op _ [arg] -> do
          op' <- freshenHead op
          case op' of
            VarE _ v | v `isCoreBuiltin` The_reify ->
              -- Verify that argument is a data constructor application.
              -- Only the simplifier puts a 'reify' expression here, and
              -- it should only put in a data constructor.
              case discardSubstitution arg of
                ExpM (ConE {}) -> eliminate_case arg
                _ -> internalError "rwCase: Unexpected 'reify' in argument"
            _ -> not_case_of_constructor
        _ -> not_case_of_constructor
  where
    not_case_of_constructor = rwCaseScrutinee inf scrut sps alts

    -- This is a case of data constructor expression.  The case
    -- expression and data constructor cancel out.
    eliminate_case data_con_expr = do
      consumeFuel

      -- Rename the scrutinee and get constructor fields
      ConE _ scrut_con _ ty_ob scrut_args <- freshenHead data_con_expr

      alt <- findAlternative alts scrut_con
      let ex_types = conExTypes scrut_con
      field_kinds <- conFieldKinds scrut_con

      -- Compute dictionaries for bare fields
      m_field_dicts <- conFieldDicts' scrut_con
      case m_field_dicts of
        Nothing -> not_case_of_constructor -- Cannot simplify
        Just field_dicts ->
          -- Eliminate this case statement
          eliminateCaseWithExp field_dicts ex_types
          ty_ob scrut_args alt

-- | Create field dictionary expressions for all bare fields of a data type.
--   Return 'Nothing' if unable to generate suitable expressions.
--
--   Each returned tuple is @(BareK, Just e)@, @(BoxK, Nothing)@,
--   or @(ValK, Nothing)@.
conFieldDicts :: ConInst -> LR (Maybe [(BaseKind, Maybe ExpM)])
conFieldDicts con@(VarCon op ty_args ex_types) = do
  Just dcon_type <- lookupDataCon op
  let field_kinds = dataConFieldKinds dcon_type
      ty_args = conTyArgs con
      ex_types = conExTypes con
  (field_types, _) <-
    instantiateDataConTypeWithExistentials dcon_type (ty_args ++ ex_types)

  field_assocs <- zipWithM field_dict field_kinds field_types
  return $ sequence field_assocs
  where
    field_dict :: BaseKind -> Type -> LR (Maybe (BaseKind, Maybe ExpM))
    field_dict BareK ty =
      condM (liftTypeEvalM $ deconVarAppType ty)
      [ do Just (op, args) <- it
           Just data_type <- lift $ liftTypeEvalM $ lookupDataType op
           lift $ do supply <- getLLVarIdentSupply
                     (m_dict_exp, context) <-
                       liftTypeEvalM $ SystemF.Datatypes.Code.execGen supply $
                       callConstantUnboxedInfoFunction data_type args
                     return $ do dict_exp <- m_dict_exp
                                 return (BareK, Just $ context dict_exp)
      , return Nothing
      ]

    field_dict k ty = return (Just (k, Nothing))

conFieldDicts con@(TupleCon ts) = do
  -- Tuples have no bare fields
  field_kinds <- conFieldKinds con
  return $ Just [(k, Nothing) | k <- field_kinds]

conFieldDicts' con = do
  x <- conFieldDicts con
  return $ fmap (fmap (\ (k, m_e) -> (k, fmap deferEmptySubstitution m_e))) x

-- Simplify the scrutinee, then try to simplify the case statement.
rwCaseScrutinee :: ExpInfo -> ExpSM -> [ExpSM] -> [AltSM]
                -> LR (ExpM, AbsCode)
rwCaseScrutinee inf scrut sps alts = do
  -- Simplify scrutinee and size parameters
  (scrut', scrut_val) <- clearCurrentReturnParameter $ rwExp scrut
  (sps', _) <- clearCurrentReturnParameter $ rwExps sps

  -- Try to deconstruct the new scrutinee expression
  ifElseFuel (can't_deconstruct scrut' scrut_val sps') $ do
    let maybe_exp = makeDataExpWithAbsValue scrut' scrut_val
    case maybe_exp of
      Just app_with_value -> do
        -- Scrutinee is a constructor application that can be eliminated
        consumeFuel
        eliminateCaseWithAppAndValue False app_with_value alts
      _ ->
        -- Can't deconstruct.  Propagate values and rebuild the case
        -- statement.
        can't_deconstruct scrut' scrut_val sps'
  where
    can't_deconstruct scrut' scrut_val sps' =
      rwCase2 inf alts scrut' scrut_val sps'

-- | Rewrite a case statement that stands for a let-expression.
--   This code is similar to 'rwLet'.
rwLetViaBoxed :: ExpInfo -> ExpSM -> ExpSM -> PatSM -> PatSM
              -> (Subst -> LR (ExpM, AbsCode))
                 -- ^ Computation that rewrites the body after
                 --   applying a substitution.  The substitution holds
                 --   inlining decisions that were made while
                 --   processing the binder part of the let expression.
              -> LR (ExpM, AbsCode)
rwLetViaBoxed inf scrut size_param (PatSM ty_ob) (PatSM pat) compute_body =
  ifElseFuel rw_recursive_let try_pre_inline
  where
    -- Check if we should inline the constructed value _before_ rewriting it.
    -- Should inline if the scrutinee is a data constructor application
    -- @boxed t E@, the bound value has safe uses, and one of the following: 
    --
    -- * The bound value is inspected or deconstructed,
    --   and E is a data constructor application.
    --
    -- * The bound value is copied.
    --
    -- The inlined expression will be @reify t E@.
    try_pre_inline
      -- The scrutinee must be used safely so that inlining 
      -- doesn't duplicate work
      | multiplicity scrut_demand == OnceSafe = do
          subst_scr <- applySubstitution scrut
          -- Scrutinee must be a data constructor application @boxed t E@.
          -- We only need to check for a data constructor application; it's
          -- already known that the data constructor is 'boxed'.
          case subst_scr of
            ExpM (ConE _ (VarCon _ [val_type] []) _ _ [subst_val]) 
              --  It's only worth inlining if we can eliminate the inlined
              --  code afterwards.  Either the specificity is
              --  * 'Copied' (so we can eliminate 'copy'); or
              --  * 'Inspected' or 'Decond {}' /and/ our expression is a
              --    data constructor application, so we can use
              --    case-of-constructor to eliminate the case statement.
              | is_copied ||
                is_deconstructed && is_con_app subst_val -> do
                  -- Inline this value since it's used exactly once
                  consumeFuel

                  -- Create the expression @reify t $(subst_val)@
                  let subst_val' = varAppE inf (coreBuiltin The_reify)
                                   [val_type] [subst_val]

                  -- Simplify the body of the case statement
                  compute_body (preinlineSubst1 (patMVar pat) subst_val')

            _ -> rw_recursive_let   -- Cannot pre-inline
      | otherwise = rw_recursive_let
      where
        scrut_demand = patMDmd pat

        is_copied =
          case specificity scrut_demand of {Copied -> True; _ -> False}

        is_deconstructed =
          case specificity scrut_demand
          of Decond {} -> True
             Inspected -> True
             _ -> False

        is_con_app (ExpM (ConE {})) = True
        is_con_app _ = False

    rw_recursive_let = rwLetViaBoxedNormal inf scrut size_param (PatSM ty_ob) (PatSM pat) compute_body

rwLetViaBoxedNormal inf scrut size_param (PatSM ty_ob_pat) (PatSM pat) compute_body = do
  -- Rewrite the scrutinee
  (scrut', scrut_val) <- clearCurrentReturnParameter $ rwExp scrut
  (size_param', _) <- clearCurrentReturnParameter $ rwExp size_param
      
  checkSize size_param'

  -- If scrutinee is 'boxed' applied to a case statement,
  -- apply case-of-case transformation to move the 'boxed' constructor
  -- inwards
  have_fuel <- checkFuel
  phase <- getPhase
  m_deconstructed_scrutinee <- ifFuel Nothing $ decon_scrutinee_case scrut'
  case m_deconstructed_scrutinee of
    Just (scrut_type, scrut_ty_ob, scrut_sp, inner_scrutinee, inner_sps, inner_alts) | have_fuel -> do
      consumeFuel
      
      -- Simplify the alternative.
      -- FIXME: We really should restructure this, since 'rwCaseOfCase' will 
      -- re-process the alternative.  The case alternative should only be
      -- processed once.
      alt <- case_alternative scrut_val
      subst_alt <- freshenAlt emptySubst alt
      rwCaseOfCase inf (Just (scrut_type, scrut_ty_ob, scrut_sp))
        inner_scrutinee inner_sps inner_alts [size_param'] [subst_alt]
    _ ->
      -- If scrutinee is a multi-branch case statement,
      -- apply case-of-case transformation
      -- FIXME: This code for applying case-of-case is redundant with
      -- rwCaseAlternatives.
      -- Should refactor it.
      case scrut' of
        ExpM (CaseE _ inner_scrut inner_sps inner_alts)
          | have_fuel &&
            phase >= PostFinalSimplifierPhase &&
            length inner_alts >= 1 -> do
              consumeFuel

              alt <- case_alternative scrut_val
              subst_alt <- freshenAlt emptySubst alt
              rwCaseOfCase inf Nothing
                inner_scrut inner_sps inner_alts [size_param'] [subst_alt]
        _ -> rewrite_body scrut' scrut_val [size_param']
  where
    -- Attempt to deconstruct an expression of the form
    -- @boxed (t) (case e of ...)@ where the case statement has multiple
    -- branches.
    decon_scrutinee_case expr@(ExpM (ConE _ con [sp] (Just ty_ob) [arg]))
      | is_boxed_con,
        Just (scr, sps, alts) <- from_deconstructable_case arg =
          return $ Just (ty_arg, ty_ob, sp, scr, sps, alts)

        -- Also detect the variant @boxed (t) (lambda r. case e of ...)@
      | is_boxed_con,
        ExpM (LamE lam_inf (FunM (Fun f_inf [] [f_arg] f_rtype f_body))) <- arg,
        Just (scr, sps, alts) <- from_deconstructable_case f_body = do
          -- Rename the function argument to avoid name shadowing
          fun_var <- newClonedVar (patMVar f_arg)
          let f_arg' = patM (fun_var ::: patMType f_arg)
              renaming = Rename.singleton (patMVar f_arg) fun_var
              
              -- Turn the body of a case alternative into a function
              mk_fun alt =
                case Rename.rename renaming alt
                of AltM alt ->
                     let new_fun =
                           FunM (Fun f_inf [] [f_arg'] f_rtype (altBody alt))
                         new_exp = ExpM $ LamE lam_inf new_fun
                     in AltM (alt {altBody = new_exp})
          return $ Just (ty_arg, ty_ob, sp, scr, sps, map mk_fun alts)
      where
        -- True if the data constructor is 'boxed'
        is_boxed_con =
          case con
          of VarCon op _ _ -> op `isCoreBuiltin` The_boxed
             _ -> False

        -- The data constructor's type argument
        ty_arg =
          case con of VarCon _ [t] _ -> t

        from_deconstructable_case expression =
          case expression
          of ExpM (CaseE _ scr sps alts) | isUnfloatableCase expression ->
               Just (scr, sps, alts)
             _ -> Nothing

    decon_scrutinee_case _ = return Nothing

    -- Construct and simplify a case alternative
    --
    -- > case ... of boxed @t (x : t) -> body
    case_alternative :: AbsCode -> LR AltM
    case_alternative scrut_val = do
      -- Propagate abstract value
      let field_val =
            case codeValue scrut_val
            of DataAV (AbsData _ _ _ [val]) -> val
               _ -> topCode

      -- Simplify body
      (body', _) <- assumePattern ty_ob_pat $
                    assumePattern pat $
                    withKnownValue (patMVar pat) field_val $
                    compute_body emptySubst

      -- Construct a new case alternative
      let decon = VarDeCon (coreBuiltin The_boxed) [patMType pat] []
      return $ AltM $ Alt decon (Just ty_ob_pat) [pat] body'
      
    -- The scrutinee has been simplified.  Propagate its value into the case 
    -- statement.
    rewrite_body scrut' scrut_val sps' = do
      -- Rewrite the case alternative
      alt' <- case_alternative scrut_val

      -- Rebuild a new case expression
      return (ExpM $ CaseE inf scrut' sps' [alt'], topCode)

-- | A data constructor expression 
data DataExpAndValue =
    -- | A data or tuple constructor application with arguments
    ConAppAndValue !ConInst !(Maybe FieldExpAndValue) ![FieldExpAndValue]

-- | A field of a data constructor consists of an expression,
--   a representation (for bare types only), and an abstract value
type FieldExpAndValue = (ExpM, Maybe ExpM, AbsCode)

-- | Given an expression and its abstract value, deconstruct the
--   expression as if it were a data constructor application.
--
--   Return the components of the expression and the abstract values of
--   its fields.
makeDataExpWithAbsValue :: ExpM -> AbsCode
                        -> Maybe DataExpAndValue
makeDataExpWithAbsValue expression expression_value =
  case expression
  of ExpM (ConE inf con sps m_ty_ob args) ->
       case codeValue expression_value
       of DataAV (AbsData dcon d_sps d_ty_ob field_values) ->
            -- 'con' and 'dcon' should be equal
            trace "Warning: makeDataExpWithAbsValue not implemented" Nothing {-
            Just $ ConAppAndValue dcon
                   (liftM2 (,) m_ty_ob d_ty_ob)
                   (zip args field_values) -}
          _ ->
            -- Unknown values
            trace "Warning: makeDataExpWithAbsValue not implemented" Nothing {-
            Just $ ConAppAndValue con
                   (fmap unknown_value m_ty_ob)
                   (map unknown_value args) -}
     _ ->
       Nothing
  where
    -- Attach an unknown value to expression 'x'
    unknown_value e = (e, topCode)

-- | Eliminate a case statement whose scrutinee was determined to be a
--   data constructor application.
eliminateCaseWithAppAndValue
  is_inspector (ConAppAndValue con ty_ob args_and_values) alts = do
  field_kinds <- conFieldKinds con
  let ex_args = conExTypes con
  alt <- findAlternative alts con
  eliminateCaseWithSimplifiedExp
     is_inspector field_kinds ex_args ty_ob args_and_values alt

-- | Rewrite a case statement after rewriting the scrutinee.
--   The case statement cannot be eliminated by deconstructing the scrutinee
--   expression, because the scrutineee expression is not a data constructor
--   application.
--   If the scrutinee has a known value, it may still be possible to eliminate
--   the case statement.
rwCase2 :: ExpInfo -> [AltSM] -> ExpM -> AbsCode -> [ExpM]
        -> LR (ExpM, AbsCode)
rwCase2 inf alts scrut' scrut_val sps = do
  have_fuel <- checkFuel
  case codeValue scrut_val of

    -- Can all fields be represented as expressions?
    DataAV (AbsData dcon _ data_ty_ob field_values) ->
      case (do ty_ob_exp <- mapM codeTrivialExp data_ty_ob
               field_exps <- mapM codeTrivialExp field_values 
               return (ty_ob_exp, field_exps)) of
        Just (ty_ob_exp, field_exps) | have_fuel -> do
          -- Eliminate the case statement by substituting field values into 
          -- all uses of the fields
          consumeFuel

          -- Create sizes of fields
          field_dicts <- conFieldDicts dcon
          case field_dicts of
            Nothing -> cannot_eliminate_data dcon field_values
            Just ds ->
              let tyob_v = do e <- ty_ob_exp 
                              v <- data_ty_ob
                              return (e, Nothing, v)
                  field_vs = [(e, d, v) | (e, (_, d), v) <-
                                 zip3 field_exps ds field_values]
                  data_value = ConAppAndValue dcon tyob_v field_vs
              in eliminateCaseWithAppAndValue True data_value alts

        _ -> cannot_eliminate_data dcon field_values

    BoolAV prop -> do
      -- This is a boolean case statement.
      -- Cannot eliminate the case statement, but we can replace
      -- some variables by their values in a branch of the case statement. 
      let (true_subst, false_subst) = absPropSubstitutions prop
      alts' <- substitute_in_case_branches true_subst false_subst alts
      rwCaseAlternatives inf scrut' scrut_var Nothing sps alts'
    _ ->
      -- Cannot eliminate; simplify the case alternatives
      rwCaseAlternatives inf scrut' scrut_var Nothing sps alts
  where
    cannot_eliminate_data dcon field_values = do
      -- Cannot eliminate the case statement. 
      -- However, we may have eliminated some case alternatives. 
      let known_values =
            -- The case alternative will bind existential types
            -- to fresh variables.  If there are existential
            -- types, then field values cannot be propagated
            -- because they'll have their original types, not
            -- the fresh type names.
            if null $ conExTypes dcon
            then Just ([], field_values)
            else Nothing
      alt <- findAlternative alts dcon

      rwCaseAlternatives
        inf scrut' scrut_var known_values sps [alt]
    {-
    is_product_case tenv =
      case alts
      of (AltSM (Alt {altCon = con}) : _) ->
           case con
           of TupleDeCon {} -> True
              VarDeCon v _ _ ->
                case lookupDataConWithType v tenv
                of Just (ty, _) -> length (dataTypeDataConstructors ty) == 1
                   Nothing -> internalError "rwCase: Invalid constructor"
         [] -> internalError "rwCase: Empty case statement"-}

    -- Apply a function to the true and false branches of the case statement
    substitute_in_case_branches :: Subst -> Subst -> [AltSM] -> LR [AltSM]
    substitute_in_case_branches t f alts = mapM apply alts
      where
        apply altsm@(AltSM alt) =
          case altCon alt
          of VarDeCon v [] []
               | v `isCoreBuiltin` The_True -> substitute t altsm
               | v `isCoreBuiltin` The_False -> substitute f altsm
             -- Anything else is not boolean-valued 
             _ -> internalError "rwCase: Bool scrutinee of non-boolean case"

    scrut_var =
      -- If the scrutinee is a variable, it will be assigned a known
      -- value while processing each alternative
      case scrut'
      of ExpM (VarE _ v) -> Just v
         _               -> Nothing

-- | Rewrite the alternatives of a case statement.  The scrutinee has already
--   been processed, and the case statement could not be eliminated.
rwCaseAlternatives inf scrut scrut_var known_values sps alts = do
  -- If scrutinee is a multi-branch case statement and the outer case
  -- statement's scrutinee is not a product type, then use the
  -- case-of-case transformation.
  --
  -- Product types are skipped because they are transformed by
  -- argument flattening instead.
  have_fuel <- checkFuel
  tenv <- getTypeEnv
  phase <- getPhase
  cond scrut
    [ do ExpM (CaseE _ inner_scrut inner_sps inner_alts) <- it
         aguard have_fuel
         -- Before 'PostFinal', only transform when the outer case inspects
         -- a sum type
         aguard (phase >= PostFinalSimplifierPhase) <|> (lift (sum_case alts) >>= aguard)
         aguard (isUnfloatableCase scrut)
         
         lift $ do
           -- Apply the case-of-case transformation
           rwCaseOfCase inf Nothing inner_scrut inner_sps inner_alts sps alts

    , -- Continue rewriting in the body of each case alternative
      lift $ do
        let one_alt = length alts == 1
        alts' <- mapM (rwAlt one_alt scrut_var known_values sps) alts
        rwExpReturn (ExpM $ CaseE inf scrut sps alts', topCode)
    ]
  where
    -- Check whether the outer case statement is inspecting a type with
    -- more than one constructor
    sum_case (AltSM alt : _) =
      -- Get the data type from the case alternative
      case altCon alt
      of TupleDeCon {} -> return False
         VarDeCon con _ _ -> do
           Just (data_type, _) <- lookupDataConWithType con
           return $ length (dataTypeDataConstructors data_type) /= 1

-- | Find the alternative matching constructor @con@
findAlternative :: [AltSM] -> ConInst -> LR AltSM
findAlternative alts con =
  case find match_con alts
  of Just alt -> return alt
     Nothing -> do -- DEBUG: print alternatives
                   rn_alts <- mapM applySubstitutionAlt alts 
                   traceShow (vcat $ map pprAlt rn_alts) $ traceShow con_summary $ return $! internalError "rwCase: Missing alternative"
  where
    con_summary = summarizeConstructor con

    match_con (AltSM (Alt {altCon = c})) =
      summarizeDeconstructor c == con_summary

-- | Eliminate the existential type part of a case alternative.
eliminateCaseExTypes :: [Type]  -- ^ Existential type arguments
                     -> AltSM   -- ^ Alternative to eliminate
                     -> (Maybe PatM -> [PatM] -> ExpSM -> LR a)
                        -- ^ Eliminator for the rest of the alternative
                     -> LR a
eliminateCaseExTypes ex_args (AltSM alt) k
  | length ex_types /= length ex_args =
      internalError "rwCase: Wrong number of type parameters"
  | otherwise = do
      -- Substitute known types for the existential type variables
      let subst = Subst ex_type_subst emptyV
          ty_ob_param = fmap fromPatSM $ altTyObject alt
          params = map fromPatSM $ altParams alt
      substituteMaybePatM subst ty_ob_param $ \subst' ty_ob_param' -> do
        substitutePatMs subst' params $ \subst'' params' -> do
          subst_body <- substitute subst'' (altBody alt)
          k ty_ob_param' params' subst_body
  where
    ex_types = deConExTypes $ altCon alt
    ex_type_subst =
      Substitute.fromList [(v, ty) | (v ::: _, ty) <- zip ex_types ex_args]

-- | Given the parts of a data constructor application and a list of case
--   alternatives, eliminate the case statement.  None of the given expressions
--   have been simplified yet.
--
--   This creates a new expression, then simplifies it.
--
--   Fuel should be consumed prior to calling this function.
eliminateCaseWithExp :: [(BaseKind, Maybe ExpSM)]
                     -> [Type]
                     -> Maybe ExpSM
                     -> [ExpSM]
                     -> AltSM
                     -> LR (ExpM, AbsCode)
eliminateCaseWithExp field_kinds ex_args ty_ob initializers alt =
  eliminateCaseExTypes ex_args alt $ \ty_ob_param params body ->
  
  let -- Bind the values to variables
      field_bindings =
        if length params /= length initializers
        then internalError "rwCase: Wrong number of fields"
        else [(k, s, p, i) | ((k, s), p, i) <- zip3 field_kinds params initializers]
      ty_ob_binding =
        case (ty_ob_param, ty_ob)
        of (Just pat, Just exp) -> [(BoxK, Nothing, pat, exp)]
           (Nothing,  Nothing)  -> []

  in caseInitializerBindings (ty_ob_binding ++ field_bindings) $ do
      -- Continue simplifying the new expression
      substAndRwExp body

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
                               -> [BaseKind] -- ^ Field kinds
                               -> [Type]     -- ^ Existential type parameters
                               -> Maybe FieldExpAndValue -- ^ Boxed scrutinee's type object
                               -> [FieldExpAndValue] -- ^ Initializers or field values, together with their abstract value
                               -> AltSM                -- ^ Case alternative to eliminate
                               -> LR (ExpM, AbsCode) -- ^ Simplified case alternative and its abstract value
eliminateCaseWithSimplifiedExp
  is_inspector field_kinds ex_args ty_ob initializers alt =
  eliminateCaseExTypes ex_args alt $ \ty_ob_param params body ->
  if length params /= length initializers
  then internalError "rwCase: Wrong number of fields"
  else do
    -- Bind the values to variables
    let ty_ob_initializer = fmap (\(e, Nothing, _) -> (e, Nothing)) ty_ob
        ty_ob_abstract_value = fmap (\(_, _, x) -> x) ty_ob
    let initializer_exps = [(e, d) | (e, d, _) <- initializers]
        initializer_values = [v | (_, _, v) <- initializers]

    -- Assign abstract values to the new bound variables
    let ty_ob_value = do p <- ty_ob_param
                         v <- ty_ob_abstract_value
                         return (patMVar p, v)
    let values = maybeToList ty_ob_value ++
                 [(patMVar p, v) | (p, v) <- zip params initializer_values]

    -- Add known values to the environment.  Simplify the body
    -- expression.
    (body', _) <- assumePatterns params $ with_values values $ rwExp body

    -- Bind local variables
    let new_body = 
          if is_inspector
          then postCaseInspectorBindingMaybe (liftM2 (,) ty_ob_param ty_ob_initializer) $
               foldr postCaseInspectorBinding body' $
               zip params initializer_exps
          else postCaseInspectorBindingMaybe (liftM2 (,) ty_ob_param ty_ob_initializer) $
               foldr postCaseInitializerBinding body' $
               zip3 field_kinds params initializer_exps
    return (new_body, topCode)
  where
    with_values vs e = foldr (uncurry withKnownValue) e vs

-- | Given an expression that was a parameter of a data constructor term,
--   bind the expression's value to a variable.  The correct way to bind the
--   expression depends on the data type's kind.
--
--   * Value and boxed fields are assigned using a let-expression.
--
--   * Bare fields are assigned by creating and unpacking a boxed object.
caseInitializerBinding :: BaseKind -> PatM -> Maybe ExpSM -> ExpSM
                       -> (Subst -> LR (ExpM, AbsCode))
                       -> LR (ExpM, AbsCode)
caseInitializerBinding kind param m_repr initializer compute_body =
  case kind of
    BareK -> do
      -- Box the initializer
      -- TODO: Simplify the RHS now, so we don't have to apply the substitution
      -- and traverse the expression again
      initializer_exp <- applySubstitution initializer
      let Just repr = m_repr
      repr_exp <- freshenFullyExp repr
      checkRepr repr_exp

      -- Create a type object for this boxed object
      Just boxed_data_type <- lookupDataType (coreBuiltin The_Boxed)
      let ty_ob = varAppE' (dataTypeBoxedInfoVar boxed_data_type (coreBuiltin The_boxed))
                  [param_type] [repr_exp]
      ty_ob_param <- newAnonymousVar ObjectLevel
      let ty_ob_pat = PatSM $ patM (ty_ob_param ::: pat_type)
            where
              pat_type =
                boxInfoV `varApp`
                [coreBuiltin The_Boxed `varApp` [param_type]]
      let size_exp = varAppE' (coreBuiltin The_reprSizeAlign) [param_type] [repr_exp]

      let boxed_initializer =
            deferEmptySubstitution $
            conE' constructor [size_exp] (Just ty_ob) [initializer_exp]
      rwLetViaBoxed defaultExpInfo boxed_initializer
        (deferEmptySubstitution size_exp) ty_ob_pat param' compute_body
    _ ->
      rwLet defaultExpInfo param' initializer compute_body
  where
    param_type = patMType param
    constructor = VarCon (coreBuiltin The_boxed) [param_type] []
    param' = PatSM $ setPatMDmd unknownDmd param

caseInitializerBindings :: [(BaseKind, Maybe ExpSM, PatM, ExpSM)]
                        -> (Subst -> LR (ExpM, AbsCode))
                        -> LR (ExpM, AbsCode)
caseInitializerBindings ((kind, m_size, param, initializer):fs) compute_body =
  caseInitializerBinding kind param m_size initializer $ \subst ->
  caseInitializerBindings fs (apply subst)
  where
    apply subst subst' = compute_body =<< (subst' `composeSubst` subst)

caseInitializerBindings [] compute_body = compute_body emptySubst

-- | Bind the value constructed by a parameter of a data constructor term
--   to a variable.  The generated code is equivalent to
--   'caseInitializerBinding', except that it is not fed into the simplifier.
postCaseInitializerBinding :: (BaseKind, PatM, (ExpM, Maybe ExpM)) -> ExpM -> ExpM
postCaseInitializerBinding (kind, param, (initializer, m_rep)) body =
  case (kind, m_rep) of
    (BareK, Just rep) -> letViaBoxed (patMBinder param) rep initializer body
    (_, Nothing) -> letE (setPatMDmd unknownDmd param) initializer body

-- | Given an expression that represents a field of a data constructor,
--   bind the field value to a variable.  This is similar to
--   'makeCaseInitializerBinding', except the binding is always a let-binding.
postCaseInspectorBinding :: (PatM, (ExpM, Maybe ExpM)) -> ExpM -> ExpM
postCaseInspectorBinding (param, (initializer, _)) body =
  letE (setPatMDmd unknownDmd param) initializer body

postCaseInspectorBindingMaybe :: Maybe (PatM, (ExpM, Maybe ExpM)) -> ExpM -> ExpM
postCaseInspectorBindingMaybe Nothing  e = e
postCaseInspectorBindingMaybe (Just b) e = postCaseInspectorBinding b e

rwAlt :: Bool                   -- ^ Whether to propagate exceptions.
                                --   If this is the only case alternative,
                                --   then its exception-raising status
                                --   propagates to the entire case statement.
      -> Maybe Var              -- ^ Scrutinee, if it's just a variable
      -> Maybe ([Type], [AbsCode]) -- ^ Deconstruted scrutinee value
      -> [ExpM]                    -- ^ Size parameters
      -> AltSM                        -- ^ Alternative to rewrite
      -> LR AltM
rwAlt propagate_exceptions scr m_values sps (AltSM alt) = do
  let decon = altCon alt
      -- Clear demand information because number of uses
      -- may increase or decrease after simplifying
      params = map (setPatMDmd unknownDmd . fromPatSM) $ altParams alt
      ty_ob = fmap (setPatMDmd unknownDmd . fromPatSM) $ altTyObject alt
  let arg_values = zipWith mk_arg values params
      sp_values = [labelCode e topCode | e <- sps]
  data_value <- liftTypeEvalM $
                scrutineeDataValue decon sp_values ty_ob params
  let assume_scrutinee m =
        case scr
        of Just scrutinee_var -> withKnownValue scrutinee_var data_value m
           Nothing -> m

  -- If scrutinee is a variable, add its known value to the environment
  assume_scrutinee $
    assume_params (deConExTypes decon) ty_ob (zip values params) $ do
    (body', _) <- rewrite_expression (altBody alt)
    return $ AltM $ Alt decon ty_ob params body'
  
  where
    -- Rewrite the body expression.  If it will raise an exception,
    -- generate an exception expression here.
    rewrite_expression body
      | propagate_exceptions =
          rwExp body
      | otherwise = do
          body_result <- catchException $ rwExp body
          case body_result of
            Just x -> return x
            Nothing -> do
              body_type <- inferExpType =<< applySubstitution body
              return (ExpM $ ExceptE defaultExpInfo body_type, topCode)

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
               repeat topCode
           | otherwise ->
               given_values
         _ -> repeat topCode

    -- Add existential types, paramters, and known values to the environment
    assume_params ex_types tyob_param params_and_values m = do
      let with_params = assume_parameters params_and_values m
          with_tyob_param = case tyob_param
                            of Nothing -> with_params
                               Just p  -> assume_param (topCode, p) with_params
          with_ty_params = foldr assumeBinder with_tyob_param ex_types
      with_ty_params
      
    assume_parameters labeled_params m = foldr assume_param m labeled_params
    
    -- Add a parameter and its value to the environment
    assume_param (maybe_value, param) m =
      assumePattern param $ withKnownValue (patMVar param) maybe_value m
    
    -- Create a AbsValue argument for a data field.  Use the previous known
    -- value if available, or the variable that the field is bound to otherwise
    mk_arg arg_val pat = labelCodeVar (patMVar pat) arg_val

-- | Apply the case-of-case transformation to a multi-branch case statement.
--   The scrutinee and inner branches have been simplified; the outer branches
--   have not been simplified.  They will be simplified during this
--   transformation. 
rwCaseOfCase :: ExpInfo
             -> Maybe (Type, ExpM, ExpM)
                                -- ^ If a 'boxed' constructor was
                                --   applied to the inner case statement,
                                --   this is the constructor's type argument,
                                --   type object, and size parameter.
                                --   Otherwise this is Nothing.
             -> ExpM            -- ^ Inner case statement's scrutinee
             -> [ExpM]          -- ^ Inner case statement's size parameters
             -> [AltM]          -- ^ Inner case statement's branches
             -> [ExpM]          -- ^ Outer case statement's size parameters
             -> [AltSM]         -- ^ Outer case statement's branches
             -> LR (ExpM, AbsCode)
rwCaseOfCase inf result_is_boxed scrutinee
  inner_sps inner_branches outer_sps outer_branches = do

  m_return_param <- getCurrentReturnParameter

  -- For each of the outer case statement's alternatives, create a function
  -- and a case alternative that calls that function
  (outer_defs, moveable_alts) <-
    mapAndUnzipM (makeBranchContinuation inf (fmap PatSM m_return_param)) outer_branches

  -- Put a new case statement into each branch of the inner case statement
  new_branches <- mapM (invert_branch moveable_alts) inner_branches

  -- Insert function definitions before the new case statement
  let new_case = ExpM $ CaseE inf scrutinee inner_sps new_branches
      new_expr = foldr bind_outer_def new_case outer_defs
        where
          bind_outer_def def e = ExpM $ LetfunE inf (NonRec def) e
  return (new_expr, topCode)
  where
    invert_branch moveable_alts (AltM branch) =
      let boxed_body =
            case result_is_boxed
            of Nothing -> altBody branch
               Just (t, ty_ob, sp) ->
                 let con = VarCon (coreBuiltin The_boxed) [t] []
                 in ExpM $ ConE inf con [sp] (Just ty_ob) [altBody branch]
          body' = ExpM $ CaseE inf boxed_body outer_sps moveable_alts
      in return $ AltM (branch {altBody = body'})

-- | Convert a case alternative's body expression into a function, and
--   create an equivalent case alternative that calls the newly cretaed
--   function.
--   For example, transform the case alternative @C x y. foo y x@ into
--   the function @f = \ x y. foo y x@ and the case alternative
--   @C x2 y2. f x2 y2@.
--
--   The case alternative is renamed to avoid name shadowing, because it
--   will be moved inside another case statement.
--
--   The function's parameters are the variables bound by the case
--   alternative's pattern, plus a return parameter if required.
--   If there would be no function parameters, a dummy parameter
--   of type 'NoneType' is created.
makeBranchContinuation :: ExpInfo -> Maybe PatSM -> AltSM
                       -> LR (FDef Mem, AltM)
makeBranchContinuation inf m_return_param alt = do
  -- Rename the return parameter (if present) to avoid name collisions
  (m_return_param', alt') <-
    case m_return_param
    of Nothing  -> return (m_return_param, alt)
       Just pat -> substitutePatSM emptySubst pat $ \s pat' -> do
         alt' <- substitute s alt
         return (Just pat', alt')

  -- Create dummy parameter if there are no other parameters
  m_dummy_param <-
    if null (altParams $ fromAltSM alt) &&
       isNothing (altTyObject $ fromAltSM alt) &&
       isNothing m_return_param'
    then do
      field_var <- newAnonymousVar ObjectLevel
      return $ Just $ PatSM $ patM (field_var ::: VarT (coreBuiltin The_NoneType))
    else return Nothing

  fun <- constructBranchContinuationFunction
         inf m_return_param' m_dummy_param alt'
  
  -- Simplify the function
  (fun', _) <- rwFun fun

  -- Create a function definition
  fun_name <- newAnonymousVar ObjectLevel
  let def1 = mkDef fun_name fun'
      def2 = modifyDefAnnotation (\a -> a {defAnnJoinPoint = True}) def1

  -- Create the case alternative
  let m_return_arg =
        case m_return_param
        of Nothing -> Nothing 
           Just pat -> Just $ ExpM $ VarE defaultExpInfo (patMVar $ fromPatSM pat)

  alt <- constructBranchContinuationAlt
         inf m_return_param' m_return_arg m_dummy_param alt' fun_name
  return (def2, alt)

-- | Turn the body of a case alternative into a function.
-- The function's parameters consist of the variables that are bound by 
-- the case alternative, and the return parameter of the enclosing function
-- (if there is one).
-- There must be at least one parameter;
-- create a dummy parameter if needed.
constructBranchContinuationFunction :: ExpInfo
                                    -> Maybe PatSM
                                    -> Maybe PatSM
                                    -> AltSM
                                    -> LR FunSM
constructBranchContinuationFunction
  inf m_return_param m_dummy_param (AltSM alt) = do

  -- Compute the case alternative's return type
  return_type <-
    assumeBinders ex_types $ assumePatterns (map fromPatSM params) $ do
      inferExpType =<< applySubstitution body
  
  -- Construct a function
  let ty_params = map TyPat ex_types 
      fun = FunSM $ Fun inf ty_params params return_type body
  return fun
  where
    -- These will become the parameters and body of the returned function
    ex_types = deConExTypes $ altCon alt
    params = maybeToList m_dummy_param ++
             maybeToList (altTyObject alt) ++
             altParams alt ++
             maybeToList m_return_param
    body = altBody alt

-- | Rename variables bound by the case alternative, and replace its body
--   with a function call.
constructBranchContinuationAlt
  inf m_return_param m_return_arg m_dummy_param
  (AltSM (Alt decon tyob_param params _)) callee = do

  unless (isJust m_return_param && isJust m_return_arg ||
          isNothing m_return_param && isNothing m_return_arg) $
    internalError "constructBranchContinuationAlt: Inconsistent arguments"

  -- Rename all parameters that came from the original case alternative.
  -- The return and dummy parameters are newly created, so they don't need 
  -- to be renamed.
  (decon', decon_rn) <- freshenDeConInst decon
  params' <- mapM (rename_param decon_rn) params
  tyob_param' <- mapM (rename_param decon_rn) tyob_param

  -- Construct the new case alternative
  let call_ty_args = map (VarT . binderVar) $ deConExTypes decon'
      tyob_arg = fmap (\p -> ExpM $ VarE inf (patMVar p)) tyob_param'
      decon_args = [ExpM $ VarE inf (patMVar p) | p <- params']
      dummy_arg = case m_dummy_param
                  of Nothing -> []
                     Just _ -> [noneE inf]
      call_args = dummy_arg ++ maybeToList tyob_arg ++ decon_args ++ maybeToList m_return_arg
      call = ExpM $ AppE inf (ExpM $ VarE inf callee) call_ty_args call_args
  return $ AltM $ Alt decon' tyob_param' params' call
  where
    -- Apply the given renaming to the pattern, and rename the pattern
    -- variable.
    -- The bound variable is used exactly once in the new case alternative,
    -- as a parameter to 'callee'.
    rename_param rn (PatSM param) = do
      new_var <- newClonedVar $ patMVar param 
      let ty = Rename.rename rn $ patMType param
          dmd = Dmd OnceSafe Used
      return $ setPatMDmd dmd $ patM (new_var ::: ty)

rwCoerce inf from_t to_t body = do
  -- Are the types equal in this context?
  types_equal <- compareTypes from_t to_t
  if types_equal
    then rwExp body -- Coercion is not necessary
    else do
      (body', _) <- rwExp body
      return (ExpM $ CoerceE inf from_t to_t body', topCode)

rwArray inf ty es = do
  -- Rewrite all array elements
  (es', _) <- mapAndUnzipM rwExp es
  
  -- Rebuild the array expression
  return (ExpM $ ArrayE inf ty es', topCode)

rwFun :: FunSM -> LR (FunM, AbsCode)

-- Freshen bound variables to avoid name shadowing, then rename 
rwFun f = rwFun' f

rwFun' (FunSM f) = do
  rtype <- reduceToWhnf $ funReturn f
  assumeTyPats ty_params $ assumePatterns params $ 
    set_return_parameter rtype $ do
      body_result <- catchException $ rwExp (funBody f)
    
      -- If the function body raises an exception,
      -- replace it with an exception statement
      let (body', body_computation) =
            case body_result
            of Just (new_exp, value) ->
                 (new_exp, case codeValue value
                           of {TopAV -> TopAC; _ -> ReturnAC value})
               Nothing ->
                 (ExpM $ ExceptE defaultExpInfo rtype, ExceptAC)
      let aval = funValue ty_params params body_computation
          new_fun = FunM $ Fun (funInfo f) ty_params params' rtype body'
      return (new_fun, aval)
  where
    ty_params = funTyParams f
    params = map fromPatSM $ funParams f

    -- If the function has a return parameter, record that fact.
    -- It has a return parameter if the function's type is
    -- (... -> OutPtr a -> Store) for some 'a'.
    set_return_parameter rtype k 
      | null (funParams f) =
          -- No parameters
          setCurrentReturnParameter Nothing k
      | otherwise = do
        let last_param = last params
        last_param_kind <- typeBaseKind $ patMType last_param
        let returns_store =
              case rtype
              of VarT v -> v == storeV
                 _ -> False
        if last_param_kind == OutK && returns_store
          then setCurrentReturnParameter (Just last_param) k
          else setCurrentReturnParameter Nothing k

    -- If a parameter isn't dead, its uses may be changed by simplification
    params' = map update_param $ funParams f
      where
        update_param (PatSM p) =
          case multiplicity $ patMDmd p
          of Dead -> p
             _ -> setPatMDmd unknownDmd p

rwDef :: FDef SM -> LR (FDef Mem)
rwDef def = mapMDefiniens (liftM fst . rwFun) def

rwGlobalDef :: GDef SM -> LR (GDef Mem)
rwGlobalDef (Def v ann (FunEnt f)) = do
  (f', _) <- rwFun f
  return $ Def v ann (FunEnt f')

rwGlobalDef (Def v ann (DataEnt (Constant inf ty e))) = do
  e' <- applySubstitution e
  return $ Def v ann (DataEnt (Constant inf ty e'))

rwExport :: Subst -> Export Mem -> LR (Export Mem)
rwExport initial_subst (Export pos spec f) = do
  subst_f <- freshenFun initial_subst f
  (f', _) <- rwFun subst_f
  return (Export pos spec f')

-- | Rewrite a definition group.  Then, add the defined functions to the
--   environment and rewrite something else.
withDefs :: Definiens t =>
            (Def t SM -> LR (Def t Mem))
         -> DefGroup (Def t SM)
         -> (DefGroup (Def t Mem) -> LR a)
         -> LR a
withDefs do_def (NonRec def) k = do
  def' <- do_def def
  assumeDefSM def $ withDefValue def' $ k (NonRec def')

withDefs do_def defgroup@(Rec defs) k = assumeDefs defgroup $ do
  -- Don't inline recursive functions in general.  However, we _do_ want to
  -- inline wrapper functions into non-wrapper functions, even in recursive
  -- definition groups.  So process the wrapper functions first, followed by
  -- the other functions.
  let (wrappers, others) = partition defIsWrapper defs
  wrappers' <- mapM do_def wrappers
  withDefValues wrappers' $ do
    others' <- mapM do_def others
    k $ Rec (wrappers' ++ others')

withFDefs = withDefs rwDef
withGDefs = withDefs rwGlobalDef

rwModule :: Subst -> Module Mem -> LR (Module Mem)
rwModule initial_subst (Module mod_name imports defss exports) =
  -- Add imported functions to the environment.
  -- Note that all imported functions are added--recursive functions should
  -- not be in the import list, or they will be expanded repeatedly
  withDefValues imports $ rw_top_level id defss
  where
    -- First, rewrite the top-level definitions.
    -- Add defintion groups to the environment as we go along.
    rw_top_level defss' (defs:defss) = do
      -- Insert an empty substition into each function body
      subst_defs <- mapM (mapMDefiniens (freshenEnt initial_subst)) defs
      withGDefs subst_defs $ \defs' -> rw_top_level (defss' . (defs' :)) defss
    
    -- Then rewrite the exported functions
    rw_top_level defss' [] = do
      exports' <- mapM (rwExport initial_subst) exports
      return $ Module mod_name imports (defss' []) exports'

-- | The main entry point for the simplifier
rewriteLocalExpr :: SimplifierPhase
                 -> RewriteRuleSet
                 -> Module Mem
                 -> IO (Module Mem)
rewriteLocalExpr phase ruleset mod =
  withTheNewVarIdentSupply $ \var_supply ->
  withTheLLVarIdentSupply $ \ll_var_supply -> do
    fuel <- readInitGlobalVarIO the_fuel
    i_tenv <- readInitGlobalVarIO the_memTypes
    tenv <- thawTypeEnv i_tenv
    -- denv <- runFreshVarM var_supply createDictEnv

    -- Initialize the global substitution with the variable rewrite rules.
    known_value_list <-
      runFreshVarM var_supply $ getVariableReplacements ruleset
    let known_value_subst =
          fromListV [(v, SubstitutedVar e) | (v, e) <- known_value_list]
        initial_subst = Subst Substitute.empty known_value_subst

    let env_constants =
          LRConstants { lrIdSupply = var_supply
                      , lrLLIdSupply = ll_var_supply
                      , lrImportedSet = IntSet.fromList
                                        [fromIdent $ varID $ definiendum def 
                                        | def <- modImports mod]
                      , lrRewriteRules = ruleset
                      , lrPhase = phase
                      , lrFuel = fuel}
        env =
          LREnv { lrConstants = env_constants
                , lrKnownValues = emptyAbsEnv
                , lrReturnParameter = Nothing
                , lrTypeEnv = tenv
--                , lrDictEnv = denv
                }
    Just result <- runLR (rwModule initial_subst mod) env
    return result

rewriteAtPhase :: SimplifierPhase -> Module Mem -> IO (Module Mem)
rewriteAtPhase phase mod = rewriteLocalExpr phase rules mod
  where
    rules =
      case phase
      of GeneralSimplifierPhase -> generalRewrites
         SequentialSimplifierPhase -> sequential_rewrites
         FinalSimplifierPhase -> sequential_rewrites
         PostFinalSimplifierPhase -> sequential_rewrites
      where
        sequential_rewrites =
          combineRuleSets [generalRewrites, sequentializingRewrites]
