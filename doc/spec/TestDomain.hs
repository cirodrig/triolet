
import Triolet.Domain

import Control.Monad
import Data.Maybe
import Debug.Trace
import Test.HUnit
import Test.QuickCheck
import Test.QuickCheck.Test

tests :: Test
tests = TestList
  [ let prop :: LinearMap -> LinearMap -> Bool
        prop s1 s2 = s1 == s1 +> s2 +< s2
    in TestCase $ (fmap isSuccess $ quickCheckResult prop) @?
       "Invertibility of (+>)"
  , TestCase $ assertBool "range(100)[1:]" $
    sliceList (SliceObject (Just 1) Nothing Nothing) (ListDim (Just 100)) ==
    (ListDim (Just 99), LinearMap 1 1)

    -- List slice tests
  , TestCase $ assertBool "range(100)[::-1]" $
    sliceList (SliceObject Nothing Nothing (Just (Just (-1)))) (ListDim (Just 100)) ==
    (ListDim (Just 100), LinearMap (-1) 99)
  , TestCase $ assertBool "range(100)[::-2]" $
    sliceList (SliceObject Nothing Nothing (Just (Just (-2)))) (ListDim (Just 100)) ==
    (ListDim (Just 50), LinearMap (-2) 99)
  , TestCase $ assertBool "range(100)[::-3]" $
    sliceList (SliceObject Nothing Nothing (Just (Just (-3)))) (ListDim (Just 100)) ==
    (ListDim (Just 34), LinearMap (-3) 99)
  
    -- Array slice tests
  , TestCase $ assertBool "array stride (::1)" $
    sliceToDomain (SliceObject Nothing Nothing (Just (Just 1))) ==
    Dim1 (Interval Nothing Nothing) (LinearMap 1 0)
  , TestCase $ assertBool "array stride (0:100:3)" $
    sliceToDomain (SliceObject (Just 0) (Just 100) (Just (Just 3))) ==
    Dim1 (Interval (Just 0) (Just 102)) (LinearMap 3 0)
    
    -- Trim test.
    -- The intersection of I and M is the same as the intersection
    -- of (trimInterval I M) and M.
  , let prop :: Gen Property
        prop = do
          l <- choose (-50, 50)
          n <- choose (0, 20)
          s <- choose (1, 20)
          a <- choose (0, s - 1)
          let i = Interval (Just l) (Just (l + n))
              m = LinearMap s a
              i' = trimInterval i m
          return $ forAll (choose (-100, 100)) $ \x ->
            (x `inInterval` i && x `inRange` m) ==
            (x `inInterval` i' && x `inRange` m)
    in TestCase $ (fmap isSuccess $ quickCheckResult prop) @?
       "Trimming does not change interval membership"

    -- Intersection test.
    -- X is a member of (intersectLinearMaps m1 m2)
    -- iff X is a member of both m1 and m2.
  , let prop :: Gen (Int -> Bool)
        prop = do
          s1 <- arbitrary `suchThat` \s -> lsStride s > 0
          s2 <- arbitrary `suchThat` \s -> lsStride s > 0
          let s3 = intersectLinearMaps s1 s2
          return $ \n ->
            (n `inRange` s1 && n `inRange` s2) ==
            (case s3
             of Nothing -> False
                Just s -> n `inRange` s)
    in TestCase $ (fmap isSuccess $ quickCheckResult prop) @?
       "Intersection of linear maps is a subset"
  ]

main = runTestTT tests