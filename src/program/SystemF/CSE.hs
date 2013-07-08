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

newtype CSE a = CSE (ReaderT (SingletonTypeMap ExpM) UnboxedTypeEvalM a)
                deriving(Functor, Applicative, Monad, MonadIO)

runCSE :: IdentSupply Var -> TypeEnv -> CSE a -> IO a
runCSE var_supply tenv (CSE m) =
  runTypeEvalM (runReaderT m Map.empty) var_supply tenv

instance EvalMonad CSE where liftTypeEvalM m = CSE $ lift m

instance TypeEnvMonad CSE where
  type EvalBoxingMode CSE = UnboxedMode
  getTypeEnv = CSE $ lift getTypeEnv
  liftTypeEnvM m = CSE $ liftTypeEnvM m

instance Supplies CSE (Ident Var) where
  fresh = CSE $ lift fresh

getSingletonTypeMap :: CSE (SingletonTypeMap ExpM)
getSingletonTypeMap = CSE ask

-- | Look up an instance of a singleton type
lookupSingleton :: SingletonType -> CSE (Maybe ExpM)
lookupSingleton st = getSingletonTypeMap >>= lookupST st

-- | Add a singleton type to the environment
withSingleton :: SingletonType -> ExpM -> CSE a -> CSE a
withSingleton ty val (CSE m) = CSE (local (insertST ty val) m)

withSingleton' :: Type -> ExpM -> CSE a -> CSE a
withSingleton' ty e m = do
  m_singleton <- asSingletonType ty
  case m_singleton of
    Nothing -> m
    Just st -> withSingleton st e m

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
rwLetBinding inf b rhs body = do
  m_singleton <- asSingletonType (patMType b)
  case m_singleton of
    Nothing -> not_singleton
    Just st -> do
      m_val <- lookupSingleton st
      case m_val of
        Nothing -> bind_singleton st
        Just x  -> use_singleton x
  where
    b' = clearDemandInfo b

    not_singleton = do
      rhs' <- rwExp rhs
      body' <- assumeBinder (patMBinder b') $ rwExp body
      return $ ExpM $ LetE inf b' rhs' body'

    bind_singleton st = do
      rhs' <- rwExp rhs
      let singleton_value = varE' (patMVar b')
      body' <- assumeBinder (patMBinder b') $
               withSingleton st singleton_value $ rwExp body
      return $ ExpM $ LetE inf b' rhs' body'

    use_singleton x = do
      body' <- assumeBinder (patMBinder b') $ rwExp body
      return $ ExpM $ LetE inf b' x body'

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
