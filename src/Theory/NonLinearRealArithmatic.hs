{-# LANGUAGE ScopedTypeVariables #-}
module Theory.IntervalConstraintPropagation where

import qualified Data.Vector as V
import Data.Vector (Vector)
import qualified Data.Set as S
import Data.Set (Set)
import Data.Function (on)
import Data.List (sortBy)

data Interval a = (:..:) { lowerBound :: a, upperBound :: a }

newtype IntervalUnion a = IntervalUnion { getIntervals :: [Interval a] }

-- type IntervalBox a = Vector (Interval a)

diameter :: (Bounded a, Real a) => Interval a -> a
diameter (lb :..: ub) = ub - lb

isEmpty :: Ord a => Interval a -> Bool
isEmpty (lb :..: ub) = ub < lb

-- instance Ord a => Eq (Interval a) where
--   i1@(lb1 :..: ub1) == i2@(lb2 :..: ub2) =
--        (lb1 == lb2 && ub1 == ub2)
--     || (isEmpty i1 && isEmpty i2)

-- instance Ord a => Ord (Interval a) where
--   compare (lb1 :..: ub1) (lb2 :..: ub2) = 
--     q

instance (Ord a, Num a) => Num (Interval a) where
  i1@(lb1 :..: ub1) + i2@(lb2 :..: ub2) 
    | isEmpty i1 || isEmpty i2 = 1 :..: 0
    | otherwise = (lb1+lb2) :..: (ub1+ub2)

  negate (lb1 :..: ub1) = negate ub1 :..: negate lb1

  i1@(lb1 :..: ub1) * i2@(lb2 :..: ub2) 
    | isEmpty i1 || isEmpty i2 = 1 :..: 0
    | otherwise = minimum pairs :..: maximum pairs
      where
        pairs = [ lb1*lb2, lb1*ub2, ub1*lb2, ub1*ub2 ]

  fromInteger x = fromInteger x :..: fromInteger x

  abs (lb :..: ub)
    | ub < lb   = 1 :..: 0
    | 0 <= lb   = lb :..: ub
    | ub <= 0   = 0 :..: (-lb)
    | otherwise = 0 :..: max (-lb) ub

  -- FIXME: law `abs x * signum x == x` is not satisfied
  signum (lb :..: ub) = signum lb :..: signum ub

-- merge intervals with overlap
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

----------------------

newtype Polynomial a = Polynomial { getCoefficients :: [a] }
  deriving Show

derivative :: (Enum a, Num a) => Polynomial a -> Polynomial a
derivative = Polynomial . tail . zipWith (*) [0..] . getCoefficients

