{-| Useful monad versions of logical operations.
-} 

module Common.MonadLogic where

infixr 3 >&&>
infixr 2 >||>

-- | Monadic version of 'when'
whenM :: Monad m => m Bool -> m () -> m ()
whenM cond m = ifM cond m (return ())

-- | Monadic version of 'unless'
unlessM :: Monad m => m Bool -> m () -> m ()
unlessM cond m = ifM cond (return ()) m

-- | Monadic version of 'if'
ifM :: Monad m => m Bool -> m a -> m a -> m a
ifM cond tr fa = cond >>= \b -> if b then tr else fa

-- | Short-circuiting '&&' operator
(>&&>) :: Monad m => m Bool -> m Bool -> m Bool
m >&&> n = m >>= \b -> if b then n else return False

-- | Monadic, short-circuiting version of 'and'
andM :: Monad m => [m Bool] -> m Bool
andM (m:ms) = ifM m (andM ms) (return False)
andM []     = return True

-- | Monadic, short-circuiting version of 'all'
allM :: Monad m => (a -> m Bool) -> [a] -> m Bool
allM f xs = go xs
    where
      go (x:xs) = ifM (f x) (go xs) (return False)
      go []     = return True

-- | Short-circuiting '||' operator
(>||>) :: Monad m => m Bool -> m Bool -> m Bool
m >||> n = m >>= \b -> if b then return True else n

-- | Monadic, short-circuiting version of 'or'
orM :: Monad m => [m Bool] -> m Bool
orM (m:ms) = ifM m (return True) (orM ms)
orM []     = return False

-- | Monadic, short-circuiting version of 'any'
anyM :: Monad m => (a -> m Bool) -> [a] -> m Bool
anyM f xs = go xs
    where
      go (x:xs) = ifM (f x) (return True) (go xs)
      go []     = return False

-- | Monadic version of 'find'
findM :: Monad m => (a -> m Bool) -> [a] -> m (Maybe a)
findM f xs = go xs
    where
      go (x:xs) = ifM (f x) (return (Just x)) (go xs)
      go []     = return Nothing

-- | Monad version of 'findIndex'
findIndexM f xs = fi 0 xs
    where
      fi n (x:xs) = do b <- f x
                       if b then return (Just n)
                            else fi (n+1) xs
      fi _ []     = return Nothing

-- | Monad analogue of mapAccumL
mapAccumM :: Monad m => (acc -> a -> m (acc, b)) -> acc -> [a] -> m (acc, [b])
mapAccumM f acc xs = go acc id xs
    where
      go acc ys (x:xs) = do (acc', y) <- f acc x
                            go acc' (ys . (y:)) xs

      go acc ys [] = return (acc, ys [])

-- | Apply a list of context transformations to a computation.  This is based
-- on a FFI library function, reproduced here because it's useful
-- independently of the FFI.
withMany :: (a -> (b -> c) -> c) -> [a] -> ([b] -> c) -> c
withMany f xs k = go xs k
  where
    go (x:xs) k = f x $ \y -> go xs $ \ys -> k (y:ys)
    go []     k = k []
