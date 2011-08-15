{-|
This is a reference implementation of the library function 'intersectSliceWithRange'.
The function implements a mostly Python-compatible slice function.

Unlike Python, arrays can have negative indices.  Negative indices do _not_ wrap
around to the end of an array.
-}

import Control.Monad
import Debug.Trace
import Test.HUnit

data Slice = Slice (Maybe Int) (Maybe Int) (Maybe (Maybe Int))

rangeSlice l u = Slice l u Nothing 
strideSlice l u r = Slice l u (Just r)

data AffineInt = Finite Int | PosInfty | NegInfty

intersectSliceWithRange :: Slice -> AffineInt -> AffineInt -> (Maybe Int, Maybe Int, Int, Int)
intersectSliceWithRange (Slice m_slice_lo m_slice_hi m_m_stride) range_lo range_hi = let
  -- Direction is 'True' if slice counts upward, 'False' if slice
  -- counts downward.  Inclusiveness of the slice bounds depends on 
  -- the direction.
  -- It is an error for the stride to be zero.  That error is checked later.
  counting_up = case m_m_stride
                of Nothing -> True
                   Just m_stride ->
                     case m_stride
                     of Nothing -> True
                        Just n -> n > 0

  -- Get the inclusive lower bound of the result range.  The lower
  -- bound is the tighter of the bounds determined by the slice and
  -- the range.
  lo_bound = case range_lo
             of Finite l1 ->
                  if counting_up
                  then case m_slice_lo
                       of Nothing -> Just l1
                          Just l2 -> Just $ max l1 l2
                  else case m_slice_hi
                       of Nothing -> Just l1
                          Just l2 -> Just $ max l1 (l2 + 1)
                NegInfty ->
                  if counting_up
                  then m_slice_lo
                  else fmap (+1) m_slice_hi
                PosInfty -> error "Invalid lower bound"

  -- Get the exclusive upper bound of the result range.  The upper
  -- bound is the tighter of the bounds determined by the slice and
  -- the range.
  hi_bound = case range_hi
             of Finite l1 ->
                  if counting_up
                  then case m_slice_hi
                       of Nothing -> Just l1
                          Just l2 -> Just $ min l1 l2
                  else case m_slice_lo
                       of Nothing -> Just l1
                          Just l2 -> Just $ min l1 (l2 + 1)
                PosInfty ->
                  if counting_up
                  then m_slice_hi
                  else fmap (+1) m_slice_lo
                NegInfty -> error "Invalid upper bound"

  in if case lo_bound
        of Just lb -> case hi_bound
                      of Just hb -> lb > hb
                         _ -> False
           _ -> False
     then (Just 0, Just 0, 1, 0)    -- Slice does not intersect range
     else case m_m_stride
          of Nothing ->
               (lo_bound, hi_bound, 1, 0) -- Use this range
             Just m_stride ->
               let stride = case m_stride
                            of Nothing            -> 1
                               Just n | n == 0    -> error "Zero stride"
                                      | otherwise -> n
               in intersectStrideSliceWithRange lo_bound hi_bound m_slice_lo m_slice_hi stride

intersectStrideSliceWithRange :: Maybe Int -> Maybe Int -> Maybe Int -> Maybe Int -> Int
                              -> (Maybe Int, Maybe Int, Int, Int)
intersectStrideSliceWithRange lo_bound hi_bound slice_lo_bound slice_hi_bound stride = let
  -- Counting up or down?
  counting_up = stride > 0

  sense = if counting_up then 1 else -1

  -- The inclusive bound of the range on the slice_lo_bound side
  near_bound =
    if counting_up
    then lo_bound
    else fmap (subtract 1) hi_bound

  -- The exclusive bound of the range on hte slice_hi_bound side
  far_bound =
    if counting_up
    then hi_bound
    else fmap (subtract 1) lo_bound

  -- The first point in the slice.  The first point is slice_lo_bound if it's within the range,
  -- otherwise it's slice_lo_bound + N * stride for the smallest N that brings the point within
  -- the range.
  first_point =
    case slice_lo_bound
    of Nothing ->
         case near_bound
         of Nothing -> error "Slice with explicit stride has no lower bound"
            Just nb -> nb
       Just lb ->
         case near_bound
         of Nothing -> lb
            Just nb | sense * (nb - lb) > 0 ->
                        -- slice_lo_bound is outside the range
                        nb + (lb - nb) `mod` stride
                    | otherwise ->
                        -- slice_lo_bound is in the range
                        lb
  
  -- The endpoint of the slice (not inclusive).
  end_point =
    case slice_hi_bound
    of Nothing -> far_bound
       Just hb ->
         case far_bound
         of Nothing -> Just hb
            Just fb | sense * (fb - hb) < 0 ->
                        -- slice_hi_bound is outside the range
                        Just fb
                    | otherwise ->
                        -- slice_hi_bound is in the range
                        Just hb

  -- Compute size of range.  Use ceiling division.
  size =
    case end_point
    of Nothing -> Nothing
       Just ep ->
         let delta = ep - first_point
             count = delta `div` stride + if delta `mod` stride /= 0 then 1 else 0
         in Just $ max 0 count
            
  in (Just 0, size, stride, first_point)

-- | Apply a slice to a range and get a list of (input, output) pairs
sliceAssocs :: Slice -> Int -> Int -> [(Int, Int)]
sliceAssocs sl lo hi =
  let (Just lo', Just hi', stride, offset) = intersectSliceWithRange sl (Finite lo) (Finite hi)
  in [(i, i * stride + offset) | i <- [lo' .. (hi' - 1)]]

tests :: Test
tests = TestList
  [ rangeSlice Nothing Nothing `yields1` [(x, x) | x <- [-5 .. 5]]

    -- Test out-of-bounds and near-bounds cases
  , rangeSlice (Just (-7)) (Just 5) `yields1` [(x, x) | x <- [-5 .. 4]]
  , rangeSlice (Just (-5)) (Just 21) `yields1` [(x, x) | x <- [-5 .. 5]]

    -- Test in-bounds case
  , rangeSlice (Just (-3)) (Just 4) `yields1` [(x, x) | x <- [-3 .. 3]]
    
    -- Test empty cases
  , rangeSlice (Just 6) (Just 10) `yields1` []
  , rangeSlice (Just 3) (Just 0) `yields1` []
    
    -- Test range slicing of unbounded ranges
  , rangeSlice Nothing Nothing `yields2` (Nothing, Just 50, 1, 0)
  , rangeSlice (Just (-3)) Nothing `yields2` (Just (-3), Just 50, 1, 0)

    -- Test shifting by using a strided slice
  , strideSlice Nothing Nothing Nothing `yields1` zip [0..] [-5 .. 5]

    -- Test positive stride
  , strideSlice (Just (-3)) (Just 5) (Just 2) `yields1`
    zip [0..] [-3, -1, 1, 3]
    
    -- Test stride slicing of unbounded ranges
  , strideSlice (Just 10) Nothing (Just 2) `yields3`
    (Just 0, Nothing, 2, 10)
  , strideSlice (Just 10) Nothing (Just (-2)) `yields2`
    (Just 0, Nothing, -2, 10)

    -- Test first boundary with positive stride
  , strideSlice (Just (-5)) (Just 50) (Just 3) `yields1`
    zip [0..] [-5, -2, 1, 4]
  , strideSlice (Just (-6)) (Just 50) (Just 3) `yields1`
    zip [0..] [-3, 0, 3]
  , strideSlice (Just (-7)) (Just 50) (Just 3) `yields1`
    zip [0..] [-4, -1, 2, 5]

    -- Test second boundary with positive stride
  , strideSlice (Just (-5)) (Just 6) (Just 2) `yields1`
    zip [0..] [-5, -3, -1, 1, 3, 5]
  , strideSlice (Just (-4)) (Just 6) (Just 2) `yields1`
    zip [0..] [-4, -2, 0, 2, 4]
  , strideSlice (Just (-5)) (Just 7) (Just 2) `yields1`
    zip [0..] [-5, -3, -1, 1, 3, 5]
  , strideSlice (Just (-4)) (Just 7) (Just 2) `yields1`
    zip [0..] [-4, -2, 0, 2, 4]
  , strideSlice (Just (-5)) (Just 5) (Just 2) `yields1`
    zip [0..] [-5, -3, -1, 1, 3]
  , strideSlice (Just (-4)) (Just 5) (Just 2) `yields1`
    zip [0..] [-4, -2, 0, 2, 4]

    -- Test first boundary with negative stride
  , strideSlice (Just 5) (Just (-50)) (Just (-3)) `yields1`
    zip [0..] [5, 2, -1, -4]
  , strideSlice (Just 6) (Just (-50)) (Just (-3)) `yields1`
    zip [0..] [3, 0, -3]
  , strideSlice (Just 7) (Just (-50)) (Just (-3)) `yields1`
    zip [0..] [4, 1, -2, -5]
  
    -- Test second boundary with negative stride
  , strideSlice (Just 5) (Just (-5)) (Just (-2)) `yields1`
    zip [0..] [5, 3, 1, -1, -3]
  , strideSlice (Just 4) (Just (-5)) (Just (-2)) `yields1`
    zip [0..] [4, 2, 0, -2, -4]
  , strideSlice (Just 5) (Just (-6)) (Just (-2)) `yields1`
    zip [0..] [5, 3, 1, -1, -3, -5]
  , strideSlice (Just 4) (Just (-6)) (Just (-2)) `yields1`
    zip [0..] [4, 2, 0, -2, -4]
  ]
  where
    -- Test a slice on the range [-5, 5]
    x `yields1` y = TestCase (sliceAssocs x (-5) 6 @?= y)
    
    -- Test a slice on the range [-inf, 49]
    x `yields2` y = TestCase (intersectSliceWithRange x NegInfty (Finite 50) @?= y)

    -- Test a slice on the range [0, inf]
    x `yields3` y = TestCase (intersectSliceWithRange x (Finite 0) PosInfty @?= y)

main = runTestTT tests