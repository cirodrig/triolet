
module LowLevel.BinaryUtils where

import Data.Binary

import Common.Error

readError m = internalError m

putEnum x = putWord8 $ fromIntegral $ fromEnum x

getEnum msg = fmap pick getWord8
  where
    pick n | n < minBound || n > maxBound = readError msg
           | otherwise = toEnum $ fromIntegral n

