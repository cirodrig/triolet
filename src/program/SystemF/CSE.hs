{-| Common subexpression elimination.

This compiler pass removes redundant computation of singletons.  A singleton
is a member of a type that has exactly one inhabitant.  If we find two
values with the same type, and that type is a singleton type, then the
values must be equal.  The first value can be substituted for the second, 
removing redundant computation.

For example, if we have

> let x = repr_Stored repr_int in
> let y = repr_Stored repr_int in
> ...

this will be replaced with

> let x = repr_Stored repr_int in
> let y = x in
> ...

CSE is designed to work on code that has been flattened.  After flattening,
all CSE opportunities occur at let-bindings, and CSE only exploits
opportunities at let-bindings.
CSE should work on non-flattened code, just less effectively.

CSE invalidates the results of demand analysis because it inserts additional
uses of variables.  It removes demand annotations from variable bindings.
-}


{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving #-}
module SystemF.CSE(commonSubexpressionElimination)
where

import Prelude hiding(mapM)
import Control.Applicative
import Control.Monad hiding(mapM)
import Control.Monad.Trans
import Control.Monad.Trans.Reader
import qualified Data.Map as Map
import Data.Maybe
import Data.Traversable
import Debug.Trace
import Text.PrettyPrint.HughesPJ

import Builtins.Builtins
import Common.Identifier
import Common.MonadLogic
import Common.Supply
import SystemF.Build
import SystemF.IncrementalSubstitution
import SystemF.ReprDict
import SystemF.MemoryIR
import SystemF.PrintMemoryIR
import SystemF.Syntax
import SystemF.Simplifier.Rewrite
import Type.Compare
import Type.Environment
import Type.Eval
import Type.Type
import Globals
import GlobalVar

-- | True if the operator is known to be pure.
--   Note that purity includes absence of nondeterminism and nontermination.
isPureOp v = v `elem` pure_list
  where
    pure_list = [coreBuiltin The_defineIntIndex]

-- | A singleton type is always a named type or type application,
--   and always has an inhabited kind
data SingletonType = SingletonType Var [Type]

-- | Decide whether two singleton types are equal
compareSingletonTypes :: EvalMonad m =>
                         SingletonType -> SingletonType -> m Bool
compareSingletonTypes (SingletonType v1 ts1) (SingletonType v2 ts2)
  | v1 == v2  = andM [compareTypes s t | (s, t) <- zip ts1 ts2]
  | otherwise = return False

-- | Decide whether a type is a singleton type.  If so, deconstruct it.
asSingletonType :: EvalMonad m => Type -> m (Maybe SingletonType)
asSingletonType ty = liftTypeEvalM $ do
  m_type_app <- deconVarAppType ty
  case m_type_app of
    Nothing        -> return Nothing   -- Not a type application
    Just (con, ts) -> do
      m_dtype <- lookupDataType con
      case m_dtype of
        Just dtype | dataTypeIsSingleton dtype ->
          return $ Just $ SingletonType con ts
        _ -> return Nothing     -- Not a singleton type

-- | A map from singleton types to values
type SingletonTypeMap a = Map.Map Var [([Type], a)]

lookupST :: forall m a. EvalMonad m =>
            SingletonType -> SingletonTypeMap a -> m (Maybe a)
lookupST (SingletonType op args) m =
  -- Look up operator
  case Map.lookup op m
  of Nothing      -> return Nothing
     Just members -> do
       -- Find matching operands
       m_match <- findM same_types members :: m (Maybe ([Type], a))
       return $ case m_match
                of Just (_, x) -> Just x
                   Nothing     -> Nothing
  where
    same_types (ts, _) = andM [compareTypes s t | (s, t) <- zip args ts]

insertST :: SingletonType -> a -> SingletonTypeMap a -> SingletonTypeMap a
insertST (SingletonType op args) x m =
  let add_member mbs = Just $ (args, x) : fromMaybe [] mbs
  in Map.alter add_member op m

-------------------------------------------------------------------------------

-- | A CSE-able function call.
--
--   Can only represent functions applied to variable or literal arguments.
data CSECall = CSECall !Var [Type] [TrivialArg]

data TrivialArg = VarArg !Var | LitArg !Lit

eqArg (VarArg v1) (VarArg v2) = v1 == v2
eqArg (LitArg l1) (LitArg l2) = eqLit l1 l2
eqArg _           _           = False

eqArgs (x:xs) (y:ys) = eqArg x y && eqArgs xs ys
eqArgs []     []     = True
eqArgs _      _      = False

eqLit (IntL m _)   (IntL n _)   = m == n
eqLit (FloatL f _) (FloatL g _) = f == g
eqLit _            _            = False

-- | Check whether two 'CSECall's are equal
eqCall :: EvalMonad m => CSECall -> CSECall -> m Bool
eqCall (CSECall op1 ty_args1 args1) (CSECall op2 ty_args2 args2) =
  return (op1 == op2 && eqArgs args1 args2) >&&>
  return (length ty_args1 == length ty_args2) >&&>
  andM (zipWith compareTypes ty_args1 ty_args2)

-- | Convert an expression to a CSECall if it is CSEable.
--   CSEable expressions must be pure function calls with trivial arguments.
asCSECall :: ExpM -> Maybe CSECall
asCSECall (ExpM (AppE _ (ExpM (VarE _ op_var)) ty_args args))
  | isPureOp op_var,
    Just cse_args <- mapM asTrivialArg args =
      Just $ CSECall op_var ty_args cse_args

asCSECall _ = Nothing

asTrivialArg (ExpM (VarE _ v)) = Just $ VarArg v
asTrivialArg (ExpM (LitE _ l)) = Just $ LitArg l

-- | A map from function calls to their known result value
type CSEMap = [(CSECall, Var)] 

lookupCSE :: EvalMonad m => CSECall -> CSEMap -> m (Maybe Var)
lookupCSE call m = search m
  where
    search ((c,v) : m) = ifM (eqCall call c) (return (Just v)) (search m)
    search []          = return Nothing

insertCSE :: CSECall -> Var -> CSEMap -> CSEMap
insertCSE c v m = (c,v) : m

-------------------------------------------------------------------------------

data CSEEnv =
  CSEEnv
  { singletonTypes :: !(SingletonTypeMap ExpM)
  , cseCalls       :: !CSEMap
  }

emptyCSEEnv = CSEEnv Map.empty []

newtype CSE a = CSE (ReaderT CSEEnv UnboxedTypeEvalM a)
                deriving(Functor, Applicative, Monad, MonadIO)

runCSE :: IdentSupply Var -> TypeEnv -> CSE a -> IO a
runCSE var_supply tenv (CSE m) =
  runTypeEvalM (runReaderT m emptyCSEEnv) var_supply tenv

instance EvalMonad CSE where liftTypeEvalM m = CSE $ lift m

instance TypeEnvMonad CSE where
  type EvalBoxingMode CSE = UnboxedMode
  getTypeEnv = CSE $ lift getTypeEnv
  liftTypeEnvM m = CSE $ liftTypeEnvM m

instance Supplies CSE (Ident Var) where
  fresh = CSE $ lift fresh

getSingletonTypeMap :: CSE (SingletonTypeMap ExpM)
getSingletonTypeMap = CSE (asks singletonTypes)

getCSECalls :: CSE CSEMap
getCSECalls = CSE (asks cseCalls)

-- | Look up an instance of a singleton type
lookupSingleton :: SingletonType -> CSE (Maybe ExpM)
lookupSingleton st = getSingletonTypeMap >>= lookupST st

-- | Add a singleton type to the environment
withSingleton :: SingletonType -> ExpM -> CSE a -> CSE a
withSingleton ty val (CSE m) = CSE (local insert_type m)
  where
    insert_type env =
      env {singletonTypes = insertST ty val $ singletonTypes env}

withSingleton' :: Type -> ExpM -> CSE a -> CSE a
withSingleton' ty e m = do
  m_singleton <- asSingletonType ty
  case m_singleton of
    Nothing -> m
    Just st -> withSingleton st e m

-- | Look up a value equivalent to a CSEable call
lookupCSECall :: CSECall -> CSE (Maybe ExpM)
lookupCSECall c = getCSECalls >>= lookupCSE c >>= return . (fmap varE')

withCSECall :: CSECall -> Var -> CSE a -> CSE a
withCSECall c v (CSE m) = CSE (local insert_call m)
  where
    insert_call env =
      env {cseCalls = insertCSE c v $ cseCalls env}

-- | Add a pattern binding to the environment.
--   However, if the binding is a singleton type, don't replace it.
withPatM p m = do
  m_singleton <- asSingletonType (patMType p)
  let continue = m
  assumeBinder (patMBinder p) $
    case m_singleton
    of Nothing -> continue
       Just st -> do
         -- If this type is not already bound,
         -- add it to the singleton environment
         m_preexisting <- lookupSingleton st
         case m_preexisting of
           Nothing -> withSingleton st (varE' $ patMVar p) continue
           Just _  -> continue

withPatMs ps m = foldr withPatM m ps

withMaybePatM Nothing  m = m
withMaybePatM (Just p) m = withPatM p m

withGDef def m =
  withSingleton' (entityType (definiens def)) (varE' $ definiendum def) m

withGDefs defs m = foldr withGDef m defs

-- | Remove demand information from a binder, since the old information may be
--   invalidated
clearDemandInfo b = setPatMDmd unknownDmd b

-- | Rewrite a let-binding.
--   If it's a singleton type, look it up or add it to the
--   environment.
--   If it's a CSEable value, look it up or add it to the environment.
rwLetBinding inf b rhs body = do
  -- Singleton type?
  m_singleton <- asSingletonType (patMType b)
  case m_singleton of
    Just st -> do
      m_val <- lookupSingleton st
      case m_val of
        Nothing -> bind_singleton st
        Just x  -> use_rhs x
    Nothing -> do
      rhs' <- rwExp rhs
      
      -- CSEable value?
      case asCSECall rhs' of
        Just cse_call -> do
          m_val <- lookupCSECall cse_call
          case m_val of
            Nothing -> bind_cse rhs' cse_call
            Just x  -> use_rhs x
        Nothing -> use_rhs rhs'
  where
    b' = clearDemandInfo b

    -- Use the given RHS.  It's a simplified version of the
    -- old RHS, a replacement produced by value CSE, or a replacement
    -- produced by singleton type CSE.
    use_rhs rhs' = do
      body' <- assumeBinder (patMBinder b') $ rwExp body
      return $ ExpM $ LetE inf b' rhs' body'

    bind_cse rhs' cse_call = do
      let cse_var = patMVar b'
      withCSECall cse_call cse_var $ use_rhs rhs'

    bind_singleton st = do
      rhs' <- rwExp rhs
      let singleton_value = varE' (patMVar b')
      withSingleton st singleton_value $ use_rhs rhs'

rwExp expression@(ExpM exp) =
  case exp
  of VarE {} -> return expression
     LitE {} -> return expression
     ConE inf op ty_ob sps args ->
       ExpM <$> ConE inf op ty_ob sps <$> mapM rwExp args
     AppE inf op ty_args args ->
       ExpM <$> (AppE inf <$> (rwExp op) <*> pure ty_args <*> mapM rwExp args)
     LamE inf f -> ExpM <$> LamE inf <$> rwFun f
     LetE inf b rhs body -> rwLetBinding inf b rhs body
     LetfunE inf defs body -> rwLetfun inf defs body
     CaseE inf scr sps alts ->
       ExpM <$> (CaseE inf <$> rwExp scr <*> pure sps <*> mapM rwAlt alts)
     ExceptE _ _ -> return expression
     CoerceE inf arg ret body -> ExpM <$> (CoerceE inf arg ret <$> rwExp body)
     ArrayE inf ty es -> ExpM <$> (ArrayE inf ty <$> mapM rwExp es)

rwLetfun inf defs body = do
  (defs', body') <- assumeFDefGroup defs (mapM rwDef defs) (rwExp body)
  return $ ExpM $ LetfunE inf defs' body'

rwAlt (AltM (Alt decon ty_ob params body)) =
  assumeBinders (deConExTypes decon) $
  withMaybePatM ty_ob $
  withPatMs params $ do
    body' <- rwExp body
    return $ AltM $ Alt decon (fmap clearDemandInfo ty_ob) (map clearDemandInfo params) body'

rwFun (FunM (Fun inf ty_params params return_type body)) =
  assumeTyPats ty_params $
  withPatMs params $ do
    body' <- rwExp body
    return $ FunM $ Fun inf ty_params (map clearDemandInfo params) return_type body'

rwDef (Def v ann f) = do
  f' <- rwFun f
  let ann' = ann {defAnnUses = unknownDmd} -- Remove demand information
  return $ Def v ann' f'

rwGlobalDef (Def v ann e) = do 
  e' <- rwEnt e
  let ann' = ann {defAnnUses = unknownDmd} -- Remove demand information
  return $ Def v ann' e'

rwConstant (Constant inf ty e) =
  Constant inf ty <$> rwExp e

rwEnt (FunEnt f)  = FunEnt <$> rwFun f
rwEnt (DataEnt d) = DataEnt <$> rwConstant d

rwExport (Export pos spec f) = Export pos spec <$> rwFun f

rwTopLevel (defs:defss) exports = do
  (defs', (defss', exports')) <-
    assumeGDefGroup defs (mapM rwGlobalDef defs) (rwTopLevel defss exports)
  return (defs':defss', exports')

rwTopLevel [] exports = do
  exports' <- mapM rwExport exports
  return ([], exports')

rwModule (Module name imps defs exps) =
  withGDefs imps $ do
    (defs', exps') <- rwTopLevel defs exps
    return $ Module name imps defs' exps'

commonSubexpressionElimination :: Module Mem -> IO (Module Mem)
commonSubexpressionElimination mod = do
  withTheNewVarIdentSupply $ \supply -> do
    tenv <- readInitGlobalVarIO the_memTypes
    mutable_tenv <- thawTypeEnv tenv
    runCSE supply mutable_tenv $ rwModule mod
