
module Untyped.TIMonad where

import Control.Monad.Reader
import Untyped.Type

data Environment

newtype TE a = TE {unTE :: ReaderT Environment IO a}

class Monad m => EnvMonad m where
  getEnvironment :: m Environment
  getsEnvironment :: (Environment -> a) -> m a
  getsEnvironment f = liftM f getEnvironment
  withEnvironment :: (Environment -> Environment) -> m a -> m a

getTyConDataType :: EnvMonad m => TyCon -> m (Maybe DataType)
getTyConClass :: EnvMonad m => TyCon -> m (Maybe Class)
getTyConTypeFunction :: EnvMonad m => TyCon -> m (Maybe TyFamily)
