

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module CParser2.GenCode.Util
       (toVar,
        showResolvedVar,
        UpdateTypeEnv(..),
        applyUpdates,
        LetTypeEnv,
        TransT,
        runTypeTranslation,
        HasLetSynonym(..),
        lookupBuiltinTypeFunction
       )
where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Data.List
import Data.Maybe
import Data.Monoid
import qualified Data.Map as Map
import Debug.Trace

import Common.Identifier
import Common.SourcePos
import Common.Supply
import CParser2.AST
import Type.Environment
import qualified Type.Compare
import qualified Type.Eval
import Type.Var
import Type.Type(Binder(..), Level(..))
import qualified Type.Type as Type

toVar (ResolvedVar v) = v

showResolvedVar = show . toVar

-------------------------------------------------------------------------------
-- Type environment updates

-- | A set of updates to make to a type environment
newtype UpdateTypeEnv = UpdateTypeEnv (TypeEnv -> TypeEnv)

instance Monoid UpdateTypeEnv where
  mempty = UpdateTypeEnv id
  UpdateTypeEnv f `mappend` UpdateTypeEnv g = UpdateTypeEnv (f . g)

applyUpdates :: UpdateTypeEnv -> TypeEnv -> TypeEnv
applyUpdates (UpdateTypeEnv f) e = f e

-------------------------------------------------------------------------------
-- Type translation

-- | A mapping from "let type"-bound identifiers to types.
type LetTypeEnv = Map.Map Var Type.Type

data TransTEnv =
  TransTEnv 
  { envLetTypes      :: !LetTypeEnv
  , envTypes         :: !TypeEnv
  , envIDSupply      :: !(IdentSupply Var)
  , envTypeFunctions :: !(Map.Map String BuiltinTypeFunction)
  }

newtype TransT a = TransT (ReaderT TransTEnv IO a)
                 deriving(Functor, Applicative, Monad, MonadIO)

instance TypeEnvMonad TransT where
  type EvalBoxingMode TransT = UnboxedMode
  getTypeEnv = TransT (asks envTypes)
  askTypeEnv f = TransT (asks (f . envTypes))

  assumeWithProperties v t b (TransT m) = TransT (local insert m)
    where
      insert e = e {envTypes = insertTypeWithProperties v t b $
                                   envTypes e}

instance Supplies TransT (Ident Var) where
  fresh = TransT $ ReaderT $ \env -> supplyValue $ envIDSupply env

instance EvalMonad TransT where
  liftTypeEvalM m = TransT $ ReaderT $ \env -> do
    runTypeEvalM m (envIDSupply env) (envTypes env)

runTypeTranslation :: IdentSupply Var
                   -> TypeEnv
                   -> [(Var, Type.Type)]
                   -> Map.Map String BuiltinTypeFunction
                   -> TransT a
                   -> IO a
runTypeTranslation var_ids tenv type_synonyms type_functions (TransT m) =
  let let_types = Map.fromList type_synonyms
  in runReaderT m (TransTEnv let_types tenv var_ids type_functions)

class HasLetSynonym m where
  lookupLetTypeSynonym :: ResolvedVar -> m (Maybe Type.Type)
  withLetTypeSynonym :: ResolvedVar -> Type.Type -> m a -> m a

instance HasLetSynonym TransT where
  lookupLetTypeSynonym v = TransT $ asks (Map.lookup (toVar v) . envLetTypes)

  withLetTypeSynonym v t (TransT m) = TransT $ local insert m
    where
      insert e = e {envLetTypes = Map.insert (toVar v) t $ envLetTypes e}

lookupBuiltinTypeFunction :: String -> TransT (Maybe BuiltinTypeFunction)
lookupBuiltinTypeFunction name = TransT $ asks lookup_name
  where
    lookup_name env = Map.lookup name $ envTypeFunctions env
