-- |  
-- Cylindrical Algebraic Decomposition
--
module Theory.NonLinearRealArithmatic.CAD where

import Theory.NonLinearRealArithmatic.UnivariatePolynomial (UnivariatePolynomial, viewLeadTerm)
import qualified Theory.NonLinearRealArithmatic.UnivariatePolynomial as Uni
import Utils (adjacentPairs, count)
import Data.Maybe (maybeToList)
import Debug.Trace

data Interval a = Open a a | Closed a a

instance Show a => Show (Interval a) where
  show (Open   start end) = "(" ++ show start ++ "," ++ show end ++ ")"
  show (Closed start end) = "[" ++ show start ++ "," ++ show end ++ "]"

getLowerBound :: Interval a -> a
getLowerBound = \case
  Open   lb _ -> lb
  Closed lb _ -> lb

getUpperBound :: Interval a -> a
getUpperBound = \case
  Open   _ ub -> ub
  Closed _ ub -> ub

isOpen :: Interval a -> Bool
isOpen (Open _ _)   = True
isOpen (Closed _ _) = False

isClosed :: Interval a -> Bool
isClosed = not . isOpen

{-| 
  The Cauchy bound isolates the roots of a univariate polynomial down
  to a closed interval. For example, a Cauchy bound of 15, means that
  all roots are somewhere in the interval:
  
      [-15, 15]

  Returns `Nothing` if the polynomial only has a constant term. 
  Notice, if the polynomial is just a non-zero constant, it has no roots.
  If it is zero, it's nothing but roots.
-} 
cauchyBound :: (Fractional a, Ord a) => UnivariatePolynomial a -> Maybe (Interval a)
cauchyBound polynomial = do
  ((_, max_degree_coeff), rest_polynomial) <- Uni.viewLeadTerm polynomial
  let other_coeffs = map snd $ Uni.toList rest_polynomial
  let bound = 1 + maximum [ abs (coeff / max_degree_coeff) | coeff <- other_coeffs ]
  return $ Closed (-bound) bound

-- | With the Sturm sequence, we can count the number of roots in an interval.
sturmSequence :: forall a. (Fractional a, Ord a) => UnivariatePolynomial a -> [UnivariatePolynomial a]
sturmSequence polynomial = takeWhile (/= 0) $ go polynomial (Uni.derivative polynomial)
  where
    go :: UnivariatePolynomial a -> UnivariatePolynomial a -> [UnivariatePolynomial a]
    go p1 p2 = p1 : go p2 (negate $ snd $ p1 `Uni.divide` p2)

countSignChanges :: (Eq a, Num a) => [a] -> Int
countSignChanges as = count (uncurry (/=)) $ adjacentPairs signs
  where signs = filter (/= 0) $ map signum as

-- | Count the roots of a univariate polynomial using Sturm sequence in a given interval.
countRootsIn :: (Eq a, Num a) => [UnivariatePolynomial a] -> Interval a -> Int
countRootsIn sturm_seq interval =
  let
    polynomial = head sturm_seq

    start = getLowerBound interval
    end   = getUpperBound interval

    sign_changes_start = countSignChanges $ map (Uni.eval start) sturm_seq
    sign_changes_end   = countSignChanges $ map (Uni.eval end)   sturm_seq   

    root_count = sign_changes_start - sign_changes_end
  in
    -- With the Sturm sequence we technically count the roots in the interval
    --
    --     (start, end]
    --
    -- That is, the interval is *open* on the side of the lower bound and *closed*
    -- on the side of the upper bound. 
    case interval of
      -- So to get the root count for the closed interval [start,end] we have to add 
      -- one, if `start` itself is a root. 
      Closed _ _ -> 
        if Uni.eval start polynomial == 0 then
          root_count + 1
        else
          root_count

      -- For the root count of the open interval (start,end) we have to subtract one
      -- if `end` is itself a root.
      Open _ _ -> 
        if Uni.eval end polynomial == 0 then
          root_count - 1
        else
          root_count

split :: Fractional a => Interval a -> [Interval a]
split = \case 
  Open start end -> 
    let mid = (start + end) / 2 in
      [ Open   start mid
      , Closed mid   mid
      , Open   mid   end 
      ]

  Closed start end -> 
    let mid = (start + end) / 2 in
      [ Closed start start
      , Open   start mid
      , Closed mid   mid
      , Open   mid   end
      , Closed end   end 
      ] 

isolateRootsIn :: forall a. (Fractional a, Ord a, Show a) => Interval a -> UnivariatePolynomial a -> [Interval a]
isolateRootsIn initial_interval polynomial = go initial_interval
  where
    sturm_seq = sturmSequence polynomial

    go :: Interval a -> [Interval a]
    go interval
      | root_count == 0 = []
      | root_count == 1 = [ interval ]
      | root_count >= 2 = concatMap go $ split interval
      | otherwise = undefined
      where
        root_count = countRootsIn sturm_seq interval

isolateRoots :: forall a. (Fractional a, Ord a, Show a) => UnivariatePolynomial a -> [Interval a]
isolateRoots polynomial =
  case cauchyBound polynomial of
    Nothing       -> []
    Just interval -> isolateRootsIn interval polynomial
