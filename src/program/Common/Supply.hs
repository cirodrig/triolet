-- | An implementation of value supplies.  Value supplies provide globally
-- unique values on demand.  Getting a value from a supply involves side
-- effects; but there is an interface to use supplies in pure contexts.

{-# LANGUAGE MultiParamTypeClasses, Rank2Types #-}
module Common.Supply
    (Supply,
     newSupply,
     supplyValue,
     forceSupplyValue,
     supplyList,
     Supplies(..)
    )
where

-- For thread safety; if we know we're single-threaded, we could just use
-- IORef
import Control.Concurrent.MVar
import Control.Monad.ST.Strict
import System.IO.Unsafe

data Supply a = Supply {next :: !(a -> a), ref :: !(MVar a)}

-- | Create a new value supply.
newSupply :: a                  -- ^ Seed
          -> (a -> a)           -- ^ Successor function
          -> IO (Supply a)
newSupply init inc = do ref <- newMVar init
                        return $! Supply inc ref

-- | Obtain a new value from a supply. 
supplyValue :: Supply a -> IO a
supplyValue s =
    let update x = let x' = next s x in x' `seq` return (x', x')
    in do modifyMVar (ref s) update

-- | Obtain a new value from a supply in a pure context.  This function
-- breaks referential transparency and should be used with caution.
{-# NOINLINE forceSupplyValue #-}
forceSupplyValue :: Supply a -> (a -> b) -> b
forceSupplyValue s f = f $! unsafePerformIO (supplyValue s)

-- | Obtain a list of unique values from a supply.  The unique values are
-- computed lazily.
{-# NOINLINE supplyList #-}
supplyList :: Supply a -> IO [a]
supplyList s = unsafeInterleaveIO $ do x <- supplyValue s
                                       xs <- supplyList s
                                       return (x:xs)

class Monad m => Supplies m a where
    -- | Get a new, globally unique value
    fresh :: m a

    -- | Get access to this variable supply in a local computation
    supplyToST :: (forall s. ST s a -> ST s b) -> m b