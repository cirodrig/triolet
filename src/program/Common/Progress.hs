{-| A progress-tracking monad transformer
-}

module Common.Progress
       (ProgressT, runProgressT, evalProgressT,
        step, stepIf, liftStep, stepTo, ignoreProgress, fixedpoint)
where

import Control.Monad
import Control.Monad.Trans

-- | Progress-tracking state; strict in the progress value
data P x = P !Bool x

-- | A monad that keeps track of whether a computation has made progress.
--   Intended for fixed-point iteration.
newtype ProgressT m a = ProgressT {runP :: Bool -> m (P a)}

instance Monad m => Monad (ProgressT m) where
  return x = ProgressT (\p -> return (P p x))
  ProgressT m >>= k = ProgressT $ \p -> m p >>= \(P p' x) -> runP (k x) p'

instance MonadTrans ProgressT where
  lift m = ProgressT $ \p -> liftM (\x -> (P p x)) m

instance MonadIO m => MonadIO (ProgressT m) where
  liftIO m = lift $ liftIO m

-- | Run a 'ProgressT' computation and report whether progress was made
runProgressT :: Monad m => ProgressT m a -> m (Bool, a)
runProgressT m = do
  -- Initially, no progress has been made
  P p x <- runP m False
  return (p, x)

-- | Run a 'ProgressT' computation and return its result
evalProgressT :: Monad m => ProgressT m a -> m a
evalProgressT m = liftM snd $ runProgressT m

-- | Indicate that progress has been made
step :: Monad m => ProgressT m ()
step = ProgressT $ \_ -> return (P True ())

-- | If the condition holds, indicate that progress has been made
stepIf :: Monad m => Bool -> ProgressT m ()
stepIf b = ProgressT $ \p -> return (P (p || b) ())

-- | Run a computation and use the first element of its return tuple as a 
--   progress indicator
liftStep :: Monad m => m (Bool, a) -> ProgressT m a
liftStep m = do
  (b, x) <- lift m
  stepIf b
  return x

-- | Run a computation.  If it makes progress, pass its result to a
--   continuation.
--
--   @m `stepTo` k@ makes progress iff @m@ makes progress.
stepTo :: Monad m => ProgressT m a -> (a -> ProgressT m a) -> ProgressT m a
m `stepTo` k = ProgressT $ \p -> do
  (local_progress, x) <- runProgressT m
  if local_progress
    then runP (k x) True
    else return $ P p x

ignoreProgress :: Monad m => ProgressT m a -> ProgressT m a
ignoreProgress m = ProgressT $ \p -> do
  (_, x) <- runProgressT m
  return (P p x)

-- | Perform some iterative computation until a fixed point is reached.
--   A fixed point is indicated by the lack of progress.
fixedpoint :: Monad m => (a -> ProgressT m a) -> a -> ProgressT m a
fixedpoint f z = f z `stepTo` fixedpoint f