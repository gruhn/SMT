{-# LANGUAGE ScopedTypeVariables #-}
module Theory.NonLinearRealArithmatic.Interval where

-- TODO: extend to multivariate intervals

import qualified Data.Vector as V
import Data.Vector (Vector)
import Data.Function (on)
import Data.List (sortBy)

data Interval a = (:..:) { lowerBound :: a, upperBound :: a }

-- >>> diameter $ (-5) :..: 10
-- 15

diameter :: Num a => Interval a -> a
diameter (lb :..: ub) = ub - lb

empty :: Num a => Interval a
empty = 1 :..: 0

isEmpty :: (Ord a, Num a) => Interval a -> Bool
isEmpty int = diameter int < 0

greatest :: Bounded a => Interval a 
greatest = minBound :..: maxBound

singleton :: a -> Interval a
singleton a = a :..: a

instance Show a => Show (Interval a) where
  show (lb :..: ub) = show lb <> " :..: " <> show ub

instance (Ord a, Num a) => Num (Interval a) where
  int1@(lb1 :..: ub1) + int2@(lb2 :..: ub2) 
    | isEmpty int1 || isEmpty int2 = empty
    | otherwise = (lb1+lb2) :..: (ub1+ub2)

  negate (lb1 :..: ub1) = negate ub1 :..: negate lb1

  int1@(lb1 :..: ub1) * int2@(lb2 :..: ub2) 
    | isEmpty int1 || isEmpty int2 = empty
    | otherwise = minimum pairs :..: maximum pairs
      where
        pairs = [ lb1*lb2, lb1*ub2, ub1*lb2, ub1*ub2 ]

  fromInteger x = fromInteger x :..: fromInteger x

  abs int@(lb :..: ub)
    | isEmpty int = empty
    | 0 <= lb     = lb :..: ub
    | ub <= 0     = 0 :..: (-lb)
    | otherwise   = 0 :..: max (-lb) ub

  -- FIXME: law `abs x * signum x == x` is not satisfied
  signum (lb :..: ub) = signum lb :..: signum ub

intersection :: (Num a, Ord a) => Interval a -> Interval a -> Interval a
intersection int1@(lb1 :..: ub1) int2@(lb2 :..: ub2)
  | isEmpty int1 = empty
  | isEmpty int2 = empty
  | ub1 < lb2 = empty
  | ub2 < lb1 = empty
  | otherwise = max lb1 lb2 :..: min ub1 ub2

-- >>> square $ (-1) :..: 5 :: Interval Int
-- 0 :..: 25

-- >>> square $ (-6) :..: (-1) :: Interval Int
-- 1 :..: 36

square :: (Ord a, Num a, Bounded a) => Interval a -> Interval a
square int = (int * int) `intersection` (0 :..: maxBound)
--
-- >>> squareRoot $ 0 :..: 4
-- [-2.0 :..: -0.0,0.0 :..: 2.0]

-- >>> squareRoot $ (-4)  :..: 4
-- [-2.0 :..: 2.0]

-- >>> squareRoot $ 1 :..: 4
-- [-2.0 :..: -1.0,1.0 :..: 2.0]

squareRoot :: (Ord a, Floating a) => Interval a -> [Interval a]
squareRoot (lb :..: ub) 
  | 0 <= lb = [ (-sqrt ub) :..: (-sqrt lb), sqrt lb :..: sqrt ub ]
  | lb <= 0 && 0 <= ub = [ (-sqrt ub) :..: sqrt ub ]
  | otherwise = [ empty ]

-- >>> reduce [ 4 :..: 8, 0 :..: 3, 5 :..: 6, 7 :..: 12, 1 :..: 3 ]
-- [0 :..: 3,4 :..: 12]

-- merge overlapping intervals

reduce :: forall a. Ord a => [Interval a] -> [Interval a]
reduce = go . sortBy (compare `on` lowerBound)
  where
    go :: [Interval a] -> [Interval a]
    go [] = []
    go [int] = [int]
    go (int1 : int2 : ints)
      | upperBound int1 < lowerBound int2 = int1 : go (int2 : ints)
      | otherwise = go (merged_int : ints)
      where
        merged_int = lowerBound int1 :..: max (upperBound int1) (upperBound int2)

-- newtype IntervalUnion a = IntervalUnion { getIntervals :: [Interval a] }

-- instance (Ord a, Num a) => Num (IntervalUnion a) where
--   ints1 + ints2 = IntervalUnion . reduce $ do
--     int1 <- getIntervals ints1
--     int2 <- getIntervals ints2
--     return (int1 + int2)

--   ints1 * ints2 = IntervalUnion . reduce $ do
--     int1 <- getIntervals ints1
--     int2 <- getIntervals ints2
--     return (int1 + int2)

--   fromInteger x = IntervalUnion [fromInteger x]

--   negate = IntervalUnion . fmap negate . getIntervals
--   abs = IntervalUnion . fmap abs . getIntervals
--   signum = IntervalUnion . fmap signum . getIntervals

reciprocal :: (Ord a, Bounded a, Fractional a) => Interval a -> [Interval a]
reciprocal (lb :..: ub) 
  | ub < lb          = [ empty ]
  | 0 < lb || ub < 0 = [ recip ub :..: recip lb ]
  | otherwise        = [ minBound :..: recip lb, recip ub :..: maxBound ]

-- instance (Ord a, Bounded a, Fractional a) => Fractional (IntervalUnion a) where
--   fromRational x = IntervalUnion [ fromRational x :..: fromRational x ]

--   recip = IntervalUnion . concatMap reciprocal . getIntervals

