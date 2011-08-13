{-|
This is a reference implementation of the library function 'intersectSliceWithRange'.
The function implements a mostly Python-compatible slice function.

Unlike Python, arrays can have negative indices.  Negative indices do _not_ wrap
around to the end of an array.
-}

import Debug.Trace

data Slice =
    RangeSlice (Maybe Int) (Maybe Int)
  | StrideSlice (Maybe Int) (Maybe Int) (Maybe Int)

intersectSliceWithRange :: Slice -> Int -> Int -> (Int, Int, Int, Int)
intersectSliceWithRange slice lo hi =
  case slice
  of RangeSlice m_slice_lo m_slice_hi ->
       -- Determine lower and upper bounds
       let lb = case m_slice_lo
                of Nothing -> lo
                   Just slice_lo -> max slice_lo lo
           ub = case m_slice_hi
                of Nothing -> hi
                   Just slice_hi -> min slice_hi hi
       in (lb, ub, 1, 0)
     StrideSlice m_slice_lo m_slice_hi m_slice_stride ->
       let pos_stride stride =
             -- Determine lower and upper bounds
             let lb = case m_slice_lo
                      of Nothing -> lo
                         Just slice_lo
                           | slice_lo < lo ->
                             let diff = lo - slice_lo
                             in lo + diff + (negate diff) `mod` stride
                           | otherwise -> slice_lo
                 ub = max lb $ case m_slice_hi 
                               of Nothing -> hi
                                  Just slice_hi -> min slice_hi hi

                 -- Determine size of range.  Round up.
                 size = max 0 $ (ub - lb + stride - 1) `div` stride
             in (0, size, stride, lb)

           neg_stride stride =
             -- Determine lower and upper bounds.
             -- Upper bound is inclusive; lower bound is exclusive.
             let ub = case m_slice_lo
                      of Nothing -> hi - 1
                         Just slice_hi
                           | slice_hi >= hi ->
                             let diff = slice_hi - hi + 1
                             in hi - (diff + (negate diff) `mod` stride)
                           | otherwise -> slice_hi
                 lb = min ub $ case m_slice_hi
                               of Nothing -> lo - 1
                                  Just slice_lo -> max slice_lo (lo - 1)
                 
                 -- Determine size of range.  Round up.
                 nstride = negate stride
                 size = max 0 $ (ub - lb + nstride - 1) `div` nstride
             in (0, size, stride, ub)

       in case m_slice_stride
          of Nothing -> pos_stride 1
             Just 0  -> error "sliceobj: Zero stride"
             Just i | i >= 0    -> pos_stride i
                    | otherwise -> neg_stride i
 
enumSliceobj :: Slice -> Int -> Int -> [(Int, Int)]
enumSliceobj slice lo hi =
  let (lo', hi', stride, offset) = intersectSliceWithRange slice lo hi
  in [(i, i * stride + offset) | i <- [lo' .. (hi' - 1)]]

main = do print $ enumSliceobj (RangeSlice Nothing Nothing) (-5) 6
          print $ enumSliceobj (RangeSlice (Just (-7)) (Just 5)) (-5) 6
          print $ enumSliceobj (RangeSlice (Just (-3)) (Just 4)) (-5) 6
          print $ enumSliceobj (StrideSlice (Just (-3)) (Just 5) (Just 2)) (-5) 6
          print $ enumSliceobj (StrideSlice (Just 5) (Just (-2)) (Just (-2))) (-5) 6
