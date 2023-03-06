module Theory.NonLinearRealArithmatic.Interval where

-- TODO: extend to multivariate intervals

import qualified Data.IntMap as M
import qualified Data.Vector as V
import Data.Vector (Vector)
import Data.Function (on)
import Data.List (sortBy)

data Interval a = (:..:) { lowerBound :: a, upperBound :: a }

-- TODO: is this a good operator precedence? It should at least be lower then 6, otherwise
-- (-3 :..: 4) is read as -(3 :..: 4) == (-4 :..: -3).
infixr 5 :..:

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

elem :: Ord a => a -> Interval a -> Bool
elem el (lb :..: ub) = lb <= el && el <= ub

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

power :: (Num a, Ord a, Bounded a) => Interval a -> Int -> Interval a
power interval n
  | even n    = (interval ^ n) `intersection` (0 :..: maxBound)
  | otherwise = interval ^ n
