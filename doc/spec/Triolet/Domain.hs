{-|

This is a reference implementation of integer linear transformations and
range operations.  These operations are used in slicing, zips, and domain
transfromations.
-}

{-# LANGUAGE GADTs, TypeFamilies #-}
module Triolet.Domain where

import Data.Maybe
import Test.QuickCheck

-------------------------------------------------------------------------------
-- Domains

-- | Domains of sequences.

--   Exists in coremodule, named "list_dim"
data ListDim = ListDim !(Maybe Int)
             deriving(Eq, Show)

-- | The domain of nonempty subsets of 'Bool'
data ChainDim = ChainBoth | ChainFirst | ChainLast

-- | The domain of a guarded term; holds zero or one value
data GuardDim = GuardKeep | GuardSkip

boolToGuard :: Bool -> GuardDim
boolToGuard True = GuardKeep
boolToGuard False = GuardSkip

guardToBool :: GuardDim -> Bool
guardToBool GuardKeep = True
guardToBool GuardSkip = False

-- Exists in coremodule, named "dim0"
data Dim0 = Dim0

-- Exists in coremodule, named "dim1"
data Dim1 = Dim1 !Interval !LinearMap
          deriving(Eq, Show)

-- Exists in coremodule, named "dim2"
data Dim2 = Dim2 !Dim1 !Dim1

-- Exists in coremodule, named "dim3"
data Dim3 = Dim3 !Dim1 !Dim1 !Dim1

-- Exists in coremodule, named "index"
type family Index d

type instance Index ListDim = Int
type instance Index ChainDim = Bool
type instance Index GuardDim = ()
type instance Index Dim0 = ()
type instance Index Dim1 = Int
type instance Index Dim2 = (Int, Int)
type instance Index Dim3 = (Int, Int, Int)

type family Offset d

type instance Offset ListDim = Int
type instance Offset ChainDim = ()
type instance Offset GuardDim = ()
type instance Offset Dim0 = ()
type instance Offset Dim1 = ()
type instance Offset Dim2 = ()
type instance Offset Dim3 = ()

-------------------------------------------------------------------------------
-- Slices and integer linear algebra

-- | A slice has optional lower and upper bounds.  Optionally, a slice
--   has an optional stride.
data SliceObject = SliceObject (Maybe Int) (Maybe Int) (Maybe (Maybe Int))

-- | An integer linear mapping @{x |-> s*x + a | x <- Z}@.
data LinearMap =
  LinearMap
  { lsStride :: !Int
  , lsAlignment :: !Int
  }
  deriving(Eq, Show)

reversing m = lsStride m < 0

identityMap = LinearMap 1 0
negationMap = LinearMap (-1) 0

-- | Decide whether the int is in the range of the linear map
inRange :: Int -> LinearMap -> Bool
n `inRange` LinearMap s a = n `mod` s == a `mod` s

class Linear a where
  -- | Apply a linear mapping to a value
  (+>) :: a -> LinearMap -> a
  -- | Un-apply a linear mapping to a value.  The result is undefined if the 
  -- value is not in the range of the mapping.
  (+<) :: a -> LinearMap -> a

instance Linear Int where
  n +> LinearMap s a = s * n + a
  n +< LinearMap s a = (n - a) `div` s

-- | Linear mappings can be composed
instance Linear LinearMap where
  LinearMap t b +> LinearMap s a =
    LinearMap (t * s) (b * s + a)

  LinearMap t b +< LinearMap s a =
    LinearMap (t `div` s) ((b - a) `div` s)

-- | An interval @{x | l <= x < u}@.  The upper bound is
--   greater than or equal to the lower bound.  'Nothing' represents negative
--   infinity for the lower bound, or positive infinity for the upper bound.
data Interval = Interval !(Maybe Int) !(Maybe Int)
              deriving(Eq, Show)

isEmptyInterval (Interval (Just l) (Just u)) = l == u
isEmptyInterval _ = False

emptyInterval = Interval (Just 0) (Just 0)

inInterval :: Int -> Interval -> Bool
i `inInterval` Interval l u = inL && inU
  where
    inL = maybe True (i >=) l
    inU = maybe True (i <) u

intersectInterval :: Interval -> Interval -> Interval
intersectInterval (Interval l1 l2) (Interval h1 h2) = let
  l = case l1
      of Nothing -> l2
         Just x -> case l2
                   of Nothing -> l1
                      Just y -> Just (max x y)
  h = case h1
      of Nothing -> h2
         Just x -> case h2
                   of Nothing -> h1
                      Just y -> Just (min x y)
  nonempty = Interval l h

  -- Ensure that l is less than or equal to h
  in case l
     of Just x ->
          case h
          of Just y ->
               if x > y
               then emptyInterval
               else nonempty
             _ -> nonempty
        _ -> nonempty

instance Linear Interval where
  Interval l h +> m =
    if reversing m
    then Interval (fmap (+> m) h) (fmap (+> m) l)
    else Interval (fmap (+> m) l) (fmap (+> m) h)

  Interval l h +< m =
    if reversing m
    then Interval (fmap (+< m) h) (fmap (+< m) l)
    else Interval (fmap (+< m) l) (fmap (+< m) h)

{-
-- | A list domain is described by its size only.  The size may be infinite.
newtype ListDomain = ListDomain (Maybe Int)
                   deriving(Eq, Show)

-- | An array domain is descibed by its bounds, stride, and alignment.
--   The stride is greater than zero.  The alignment is greater than zero
--   and less than the stride.  The bounds are in the range of the linear map.
data ArrayDomain = ArrayDomain !Interval !LinearMap
                 deriving(Eq, Show)
-}

emptyDim1 :: Dim1
emptyDim1 = Dim1 emptyInterval identityMap

intersectDim1 :: Dim1 -> Dim1 -> Dim1
intersectDim1 (Dim1 i1 m1) (Dim1 i2 m2) =
  case intersectLinearMaps m1 m2
  of Nothing -> emptyDim1
     Just m3 -> let i3 = trimInterval (intersectInterval i1 i2) m3
                in Dim1 i3 m3

-- | Slice a list.  Return a new list domain and a map from an element of the 
--   slice to the original domain.
sliceList :: SliceObject -> ListDim -> (ListDim, LinearMap)
sliceList (SliceObject m_slice_lo m_slice_hi m_m_stride) (ListDim list_size) = let
  -- Direction is 'True' if slice counts upward, 'False' if slice
  -- counts downward.  Inclusiveness of the slice bounds depends on 
  -- the direction.
  -- It is an error for the stride to be zero.  That error is checked later.
  stride =
    case m_m_stride
    of Nothing -> 1
       Just m_stride ->
         case m_stride
         of Nothing -> 1
            Just n -> n

  counting_up = stride > 0

  -- Get the slice's inclusive lower bound.  The lower bound is the
  -- tighter of the bounds determined by the slice and the domain.
  -- 'Nothing' represents infinity.
  slice_lo =
    if counting_up
    then -- Maximum of slice's lower bound and range's lower bound
         case m_slice_lo
         of Nothing -> Just 0
            Just l  -> Just $ max 0 l
    else -- Minimum of slice's lower bound and range's upper bound
         case m_slice_lo
         of Just h -> case list_size 
                      of Just n -> Just $ min h (n - 1)
                         Nothing -> Just h
            Nothing -> case list_size
                            of Just n -> Just (n - 1)
                               Nothing -> Nothing

  -- Get the slice's exclusive upper bound.  The upper bound is the
  -- tighter of the bounds determined by the slice and the domain.
  -- 'Nothing' represents infinity.
  slice_hi =
    if counting_up
    then -- Minimum of slice's upper bound and range's upper bound
         case m_slice_hi
         of Nothing -> list_size
            Just h  -> case list_size
                       of Nothing -> Just h
                          Just n  -> Just $ min h n
    else -- Maximum of slice's upper bound and range's lower bound
         case m_slice_hi
         of Nothing -> Just (-1)
            Just h  -> Just $ max h (-1)

  in case ()
     of _
          -- Stride must be nonzero
          | stride == 0 -> error "Invalid stride"

          -- There must be a lower bound from one of the inputs, either
          -- the slice or the domain
          | isNothing slice_lo -> error "Slice has no lower bound"

          -- Return an empty interval if the input range is empty
          | Just l <- slice_lo -> let
            -- The slice consists of the sequence
            -- A[l], A[l + s], A[l + 2s], ...
            linear_map = LinearMap stride l
              
            -- The size of the slice is ceil(abs (hi - lo) / abs stride)
            size = case slice_hi
                   of Nothing -> Nothing
                      Just h  -> let 
                        abs_stride = abs stride
                        abs_delta = abs $ h - l
                        in Just $ (abs_delta + abs_stride - 1) `div` abs_stride

            in case size 
               of Just n | n < 0 -> (ListDim (Just 0), identityMap)
                  _ -> (ListDim size, linear_map)

-- | Convert a slice to an array domain.
sliceToDomain :: SliceObject -> Dim1
sliceToDomain (SliceObject m_slice_lo m_slice_hi m_m_stride) = let
  stride = fromMaybe 1 $ fromMaybe Nothing m_m_stride
  alignment = fromMaybe 0 m_slice_lo `mod` stride
  map = LinearMap stride alignment
  interval = trimInterval (Interval m_slice_lo m_slice_hi) map
  in if stride <= 0 
     then error "Array slice must have positive stride"
     else Dim1 interval map

-- | Coerce the interval's bounds to members of the linear map.  The
--   intersection of the input interval with the linear map's range is equal
--   to the intersection of the output interval with the linear map's range.
trimInterval :: Interval -> LinearMap -> Interval
trimInterval (Interval l u) m =
  -- Coerce the bounds to multiples of the alignment.
  -- The bounds are both rounded up.
  Interval (round_up l) (round_up u)
  where
    round_up Nothing = Nothing
    round_up (Just n) = Just $ n + (lsAlignment m - n) `mod` lsStride m

-- | Compute a linear map whose range is the intersection of two linear maps:
--
--   > { x | exists y z. A y + B = C z + D = x }
--
--   The linear maps must have positive stride.
intersectLinearMaps :: LinearMap -> LinearMap -> Maybe LinearMap
intersectLinearMaps (LinearMap s1 a1) (LinearMap s2 a2)
  | s1 <= 0 || s2 <= 0 = error "intersectLinearMaps: Stride must be positive"
  | s1 == 1 = Just (LinearMap s2 a2)
  | s2 == 1 = Just (LinearMap s1 a1)
  | otherwise =
      -- The answer is the set of values that are in the range of both maps:
      -- { s1 * y + a1 | exist x y. s1 * y - s2 * x = a2 - a1 }
      --
      -- First, divide both sides of the equation by GCD(s1, s2).
      -- If they don't divide evenly, there's no soution.
      let g = gcd s1 s2
      in if (a2 - a1) `mod` g /= 0
         then Nothing
         else let
           s1' = s1 `div` g
           s2' = s2 `div` g
           s3 = s1' * s2        -- s3 = lcm s1 s2
           c = (a2 - a1) `div` g
           -- Now find solutions to  s1' * y - s2' * x = c.

           -- Subproblem: solve  s1' * y' - s2' * x' = 1.
           -- Use the Extended Euclidean algorithm.
           -- Only a solution for y' is needed.
           y' = extgcd_x s1' s2'

           -- Multiply by 'c' to find a solution for y.
           y = c * y'

           -- Compute one member of the result map as
           -- s1 * y + a1.  Use this to find the alignment of the result.
           a3 = (s1 * y + a1) `mod` s3
           in Just (LinearMap s3 a3)

-- | Extended GCD algorithm.  Given @a, b@, find @(x, y, r)@ such that
--   @a*x + b*y = a b@ and @r = gcd a b@.
extgcd :: Int -> Int -> (Int, Int, Int)
extgcd a b = step 0 1 1 0 a b
  where
    step x y lastx lasty gcd 0 = (lastx, lasty, gcd)

    step x y lastx lasty a b = let
      q   = a `div` b
      r   = a `mod` b
      x'  = lastx - q * x
      y'  = lasty - q * y
      in step x' y' x y b r

-- | Simplified extended GCD algorithm for finding @x@ such that
--   @a*x + b*y = gcd x y@.  Given @a, b@, find @(x, y, r)@ such that
--   @a*x + b*y = r@ and @r = gcd a b@.
extgcd_x :: Int -> Int -> Int
extgcd_x a b = step 0 1 a b
  where
    step x lastx _ 0 = lastx

    step x lastx a b = let
      q   = a `div` b
      r   = a `mod` b
      x'  = lastx - q * x
      in step x' x b r

{-
instance Domain Dim1 where
  emptyDomain = Dim1 emptyDomain identityMap
  intersection (Dim1 i1 m1) (Dim1 i2 m2) =
    case intersectLinearMaps m1 m2
    of Nothing -> emptyDomain
       Just m3 -> let i3 = trimInterval (intersection i1 i2) m3
                  in Dim1 i3 m3
-}

-- | Slice an array.  Return the domain of the sliced subarray.
sliceArray :: SliceObject -> Dim1 -> Dim1
sliceArray slice d = intersectDim1 (sliceToDomain slice) d


-------------------------------------------------------------------------------
-- For testing

-- | A linear transformation between two strided sequences consists of
--   un-applying one transformation, then applying another.
data Transform = Transform !LinearMap !LinearMap
              deriving(Show)

invertTransform :: Transform -> Transform
invertTransform (Transform s t) = Transform t s

instance Linear Transform where
  Transform s1 s2 +> s3 = Transform s1 (s2 +> s3)
  Transform s1 s2 +< s3 = Transform s1 (s2 +< s3)

instance Arbitrary LinearMap where
  arbitrary = do
    -- The magic number 610 is less than the cube root of 2^31.  This choice
    -- is to avoid numeric overflow.
    a <- choose (-610, 610)
    -- Choose a nonzero stride
    s <- do x <- choose (-610, 609)
            return $! if x < 0 then x else x + 1
    return $! LinearMap s a

