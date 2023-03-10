module Theory.NonLinearRealArithmatic.IntervalUnion where

import qualified Data.IntMap as M
import Data.Function (on)
import Data.List (sortBy)
import qualified Theory.NonLinearRealArithmatic.Interval as Interval
import Theory.NonLinearRealArithmatic.Interval (Interval(..))

newtype IntervalUnion a = IntervalUnion { getIntervals :: [Interval a] }
  deriving (Eq, Ord)

instance Show a => Show (IntervalUnion a) where
  show = show . getIntervals

diameter :: (Num a, Ord a) => IntervalUnion a -> a
diameter = sum . fmap Interval.diameter . getIntervals . reduce

elem :: Ord a => a -> IntervalUnion a -> Bool
elem el = any (Interval.elem el) . getIntervals

isSubsetOf :: Ord a => IntervalUnion a -> IntervalUnion a -> Bool
isSubsetOf (IntervalUnion intervals1) (IntervalUnion intervals2) =
  all (\int -> any (int `Interval.isSubsetOf`) intervals2) intervals1

isEmpty :: (Ord a, Num a) => IntervalUnion a -> Bool
isEmpty = all Interval.isEmpty . getIntervals

empty :: IntervalUnion a
empty = IntervalUnion []

singleton :: a -> IntervalUnion a
singleton a = IntervalUnion [Interval.singleton a]

intersection :: forall a. (Num a, Ord a) => IntervalUnion a -> IntervalUnion a -> IntervalUnion a
intersection union1 union2 = reduce $ IntervalUnion $ do 
  int1 <- getIntervals union1
  int2 <- getIntervals union2
  return (int1 `Interval.intersection` int2)

power :: forall a. (Ord a, Num a, Bounded a) => IntervalUnion a -> Int -> IntervalUnion a
power union n = reduce $ modifyIntervals (fmap (`Interval.power` n)) union

modifyIntervals :: ([Interval a] -> [Interval a]) -> IntervalUnion a -> IntervalUnion a
modifyIntervals f = IntervalUnion . f . getIntervals

-- >>> squareRoot $ 0 :..: 4
-- [-2.0 :..: -0.0,0.0 :..: 2.0]

-- >>> squareRoot $ (-4) :..: 4
-- [-2.0 :..: 2.0]

-- >>> squareRoot $ 1 :..: 4
-- [-2.0 :..: -1.0,1.0 :..: 2.0]

squareRoot :: (Ord a, Floating a) => Interval a -> [Interval a]
squareRoot (lb :..: ub) 
  | 0 <= lb            = [ (-sqrt ub) :..: (-sqrt lb), sqrt lb :..: sqrt ub ]
  | lb <= 0 && 0 <= ub = [ (-sqrt ub) :..: sqrt ub ]
  | otherwise          = [ ]
  
root :: (Ord a, Floating a) => IntervalUnion a -> Int -> IntervalUnion a
root union 1 = union
root union 2 = reduce $ IntervalUnion $ concatMap squareRoot $ getIntervals union
root union n = error "TODO: extend interval arithmatic to arbitrary integer roots"

-- >>> reduce [ 4 :..: 8, 0 :..: 3, 5 :..: 6, 7 :..: 12, 1 :..: 3 ]
-- [0 :..: 3,4 :..: 12]

-- | merge overlapping intervals
reduce :: forall a. (Ord a, Num a) => IntervalUnion a -> IntervalUnion a
reduce = modifyIntervals (go . sortBy (compare `on` lowerBound) . filter (not . Interval.isEmpty))
  where
    go :: [Interval a] -> [Interval a]
    go [] = []
    go [int] = [int]
    go (int1 : int2 : ints)
      | upperBound int1 < lowerBound int2 = int1 : go (int2 : ints)
      | otherwise = go (merged_int : ints)
      where
        merged_int = lowerBound int1 :..: max (upperBound int1) (upperBound int2)

instance (Ord a, Num a) => Num (IntervalUnion a) where
  union1 + union2 = reduce $ IntervalUnion $ do
    interval1 <- getIntervals union1
    interval2 <- getIntervals union2    
    return (interval1 + interval2)

  union1 * union2 = reduce $ IntervalUnion $ do
    interval1 <- getIntervals union1
    interval2 <- getIntervals union2
    return (interval1 * interval2)

  fromInteger x = IntervalUnion [fromInteger x]
  negate = modifyIntervals (fmap negate)
  abs = modifyIntervals (fmap abs)
  signum = modifyIntervals (fmap signum)

reciprocal :: (Ord a, Bounded a, Fractional a) => Interval a -> [Interval a]
reciprocal (lb :..: ub) 
  | lb == 0  && ub == 0  = [ ]                                                 -- 1 / (0 :..: 0)    = [ ]
  | lb == 0  && 0 < ub   = [ recip ub :..: maxBound ]                          -- 1 / (0 :..: 5)    = [ 1/5 :..: +Inf ]
  | lb < 0   && ub == 0  = [ minBound :..: recip lb ]                          -- 1 / (-5 :..: 0)   = [ -Inf :..: -1/5 ]
  | lb < 0   && 0 < ub   = [ minBound :..: recip lb, recip ub :..: maxBound ]  -- 1 / (-5 :..: 5)   = [ -Inf :..: -1/5, 1/5 :..: Inf ]
  | 0 < lb   && lb <= ub = [ recip ub :..: recip lb ]                          -- 1 / (5 :..: 10)   = [ 1/10 :..: 1/5 ]
  | lb <= ub && ub < 0   = [ recip ub :..: recip lb ]                          -- 1 / (-10 :..: -5) = [ -1/5 :..: -1/10 ]
  | otherwise            = [ ]                                                 -- 1 / (1 :..: 0)    = []

instance (Ord a, Bounded a, Fractional a) => Fractional (IntervalUnion a) where
  fromRational x = IntervalUnion [ fromRational x :..: fromRational x ]

  recip = IntervalUnion . concatMap reciprocal . getIntervals
