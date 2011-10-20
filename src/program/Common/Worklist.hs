{-| Utilities for worklist algorithms.

A worklist algorithm is one that finds a fixed point of a set of assignment
equations (@x := FORMULA@, for some problem-specific type of formula)
by iteratively evaluating the equations assignments until convergence.
-}

module Common.Worklist where

import Control.Monad
import Data.IORef
import qualified Data.Set as Set

type Worklist a = IORef (Set.Set a)

-- | Create a worklist containing the given list of things
newWorklist :: Ord a => [a] -> IO (Worklist a)
newWorklist contents = newIORef (Set.fromList contents)

-- | Insert a thing into a worklist
putWorklist :: Ord a => Worklist a -> a -> IO ()
putWorklist wl x = modifyIORef wl $ Set.insert x

-- | Extract a thing from a worklist.  Return 'Nothing' if the worklist 
--   is empty
readWorklist :: Ord a => Worklist a -> IO (Maybe a)
readWorklist wl = do
  s <- readIORef wl
  case Set.minView s of
    Just (x, s') -> do
      writeIORef wl s'
      return (Just x)
    Nothing -> return Nothing

-- | Test whether a worklist is empty.
isEmptyWorklist :: Ord a => Worklist a -> IO Bool
isEmptyWorklist wl = do
  s <- readIORef wl
  return $ Set.null s

-- | Process the contents of a worklist until it is empty.
--   Things may be inserted into the worklist during processing.
forWorklist :: Ord a => Worklist a -> (a -> IO ()) -> IO ()
forWorklist wl f = readWorklist wl >>= continue
  where
    continue Nothing  = return ()
    continue (Just x) = f x >> forWorklist wl f

-- | Modify the contents of an @IORef@, and test whether the value has
--   actually changed.
modifyCheckIORef :: Eq a => (a -> a) -> IORef a -> IO Bool
modifyCheckIORef f ref = do
  x <- readIORef ref
  let y = f x
  let change = x /= y
  when change $ writeIORef ref y
  return change

