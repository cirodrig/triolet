{-| Timers for coarse-grained profiling.
-}

module Timer
       (TimeAttribution(..),
        Times,
        newTimes,
        printTimes,
        time)
where

import Control.Monad
import Data.Array.IO
import System.CPUTime

-- | The part of a program to which execution time is accounted.
data TimeAttribution =
    RewriteTimer
  | FlattenTimer
  | SpecializeTimer
  | DemandTimer
  | FloatingTimer
  | ParallelizeTimer
  | FlattenArgumentsTimer
  | TypecheckTimer
  | PrintTimer
    deriving(Eq, Ord, Enum, Bounded, Show)

instance Ix TimeAttribution where
  range (l, h) = [l .. h]
  index (l, _) i = fromEnum i - fromEnum l
  inRange (l, h) i = fromEnum i >= fromEnum l && fromEnum i <= fromEnum h
  rangeSize (l, h) = fromEnum h - fromEnum l + 1

newtype Times = Times (IOUArray TimeAttribution Double)

newTimes :: IO Times
newTimes = Times `liftM` newArray (minBound, maxBound) 0

time :: Times -> TimeAttribution -> IO a -> IO a
time (Times a) i m = do
  t1 <- getCPUTime
  x <- m
  t2 <- getCPUTime
  old_time <- readArray a i
  writeArray a i $ old_time + fromIntegral (t2 - t1)
  return x

printTimes :: Times -> IO ()
printTimes (Times arr) = do
  assocs <- getAssocs arr
  forM_ assocs $ \(i, e) -> do
    let timer = show i
        seconds = show (e * 1e-12)
    putStrLn $ "Time spent in " ++ timer ++ ": " ++ seconds
  