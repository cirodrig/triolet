{-| Global dataflow variables.

Several parts of Pyon utilize global variables.  The most common uses are
constants that need to be initialized in the IO monad and supplies of unique
integers.  This module assists in defining and using such variables.
-}

-- Profiling information for these functions is not useful
{-# OPTIONS_GHC -no-auto #-}
module GlobalVar
where

import System.IO.Unsafe
import Control.Concurrent.MVar
import Common.Error
import Common.MonadLogic

-- | A statically defined global variable.
--
-- Static global variables should be defined as monomorphic CAFs at global
-- scope.  Each definition should be given a NOINLINE pragma.
newtype StaticGlobalVar a = SGV {getSGV :: MVar a}

-- | Define a static global variable.  The given function is used to 
-- initialize the variable.  Since initialization is performed lazily,
-- the results will be unpredictable if the initialization function has
-- observable side effects.
defineStaticGlobalVar :: IO a -> StaticGlobalVar a
defineStaticGlobalVar f = unsafePerformIO $ do
  return . SGV =<< newMVar =<< f

withStaticGlobalVar :: StaticGlobalVar a -> (a -> IO b) -> IO b
withStaticGlobalVar (SGV v) f = withMVar v f

modifyStaticGlobalVar_ :: StaticGlobalVar a -> (a -> IO a) -> IO ()
modifyStaticGlobalVar_ (SGV v) f = modifyMVar_ v f 

modifyStaticGlobalVar :: StaticGlobalVar a -> (a -> IO (a, b)) -> IO b
modifyStaticGlobalVar (SGV v) f = modifyMVar v f 

-- | An explicitly initialized global variable.
newtype InitGlobalVar a = IGV {getIGV :: MVar a}

defineInitGlobalVar :: () -> InitGlobalVar a
defineInitGlobalVar x = unsafePerformIO (realDefineInitGlobalVar x)

-- The parameter 'x' is a hack to prevent CSE
{-# NOINLINE realDefineInitGlobalVar #-}
realDefineInitGlobalVar x = do
  mvar <- x `seq` newEmptyMVar
  return (IGV mvar)

-- | Return True if the variable has been initialized.
testInitGlobalVar :: InitGlobalVar a -> IO Bool
testInitGlobalVar (IGV v) = fmap not $ isEmptyMVar v

initializeGlobalVar :: InitGlobalVar a -> IO a -> IO ()
initializeGlobalVar (IGV v) m = do
  unlessM (isEmptyMVar v) already_initialized
  value <- m
  unlessM (tryPutMVar v value) already_initialized
  where
    already_initialized =
      internalError "initializeGlobalVar: Already initialized"

readInitGlobalVarIO :: InitGlobalVar a -> IO a
{-# INLINE readInitGlobalVarIO #-}
readInitGlobalVarIO (IGV v) = do
  whenM (isEmptyMVar v) $ internalError "readInitGlobalVar: Not initialized"
  readMVar v

readInitGlobalVar :: InitGlobalVar a -> a
{-# INLINE readInitGlobalVar #-}
readInitGlobalVar (IGV v) = unsafePerformIO $ do
  whenM (isEmptyMVar v) $ internalError "readInitGlobalVar: Not initialized"
  readMVar v