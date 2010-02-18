
{-# LANGUAGE DeriveDataTypeable #-}
module Pyon.Exports.Delayed where

import Control.Applicative
import Control.Monad
import Data.IORef
import Data.Typeable
import Data.Maybe


-- Pyon's Hindley-Milner type inference generates expressions.  Some 
-- expressions generated by type inference start out as undetermined 
-- placeholders that are subsequently assigned a value.  This is represented
-- here as lazy evaluation (explicit in the IO monad).
--
-- Placeholders are used in two ways:
-- 1. Types are marshaled lazily, allowing unification to mutate type variables
-- 2. Dictionary-passing translation updates generated function calls and 
--    variable references after they are created
data Delayed a =
    Unevaluated (IO a) 
  | Placeholder {-# UNPACK #-} !(DelayedRef a)
  deriving(Typeable)

type DelayedRef a = IORef (Maybe (Delayed a))

newPlaceholder :: IO (Delayed a)
newPlaceholder = do ref <- newIORef Nothing
                    return (Placeholder ref)

isPlaceholder :: Delayed a -> Bool
isPlaceholder (Placeholder _) = True
isPlaceholder (Unevaluated _) = False

setPlaceholder :: Delayed a -> Delayed a -> IO ()
setPlaceholder (Placeholder ref) new_value = do
  old_value <- readIORef ref
  when (isJust old_value) $ fail "Placeholder has already been assigned"
  writeIORef ref (Just $ new_value)

setPlaceholder (Unevaluated _) _ = fail "Delayed value is not a placeholder"

force :: Delayed a -> IO a
force (Unevaluated f) = f
force (Placeholder ref) = do
  e <- readIORef ref
  case e of
    Nothing -> error "Placeholder has not been assigned"
    Just e  -> force e

instance Functor Delayed where
  fmap f m = Unevaluated $ fmap f $ force m

instance Applicative Delayed where
  pure x = Unevaluated (return x)
  df <*> dx = Unevaluated $ do f <- force df
                               x <- force dx
                               return (f x)