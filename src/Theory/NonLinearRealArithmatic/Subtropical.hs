{-|
  Subtropical is a fast but incomplete method for solving non-linear real constraints.
-}
module Theory.NonLinearRealArithmatic.Subtropical (subtropical) where

import qualified Data.List as L
import qualified Data.IntMap as M
import qualified Data.IntMap.Merge.Lazy as MM
import Theory.NonLinearRealArithmatic.Constraint (Constraint, ConstraintRelation (..))
import Theory.NonLinearRealArithmatic.Expr (Expr (..), Var, BinaryOp (..), substitute)
import Theory.NonLinearRealArithmatic.Polynomial
    ( Monomial,
      Polynomial(..),
      Assignment,
      Assignable(..),
      Term(..),
      fromExpr,
      toExpr,
      varsIn )
import Control.Arrow ((&&&))
import qualified Theory.NonLinearRealArithmatic.UnivariatePolynomial as Univariate
import Control.Applicative (liftA2)

{-|
  The frame of a polynomial is a set of points, obtained from the 
  exponents of the individual monomials. E.g. for a polynomial over 
  variables x,y like 

   y + 2xy^3 - 3x^2y^2 - x^3 - 4x^4y^4

  we get the following points 

   (0,1), (1,3), (2,2), (4,4) 

  The points are then partitioned by the sign of the coefficient.

   pos: (0,1) 
   neg: (1,3), (2,2), (4,4) 

  Computing the frame is the basis for identifiying a term that
  dominates the polynomial for sufficently large variables values.
  That in turn is sufficient to find solutions to inequality 
  constraints.
-}
frame :: (Ord a, Num a) => Polynomial a -> ([Monomial], [Monomial])
frame polynomial = undefined -- TODO
  where
    (pos_terms, neg_terms)
      = L.partition ((> 0) . getCoeff)
      $ L.filter ((/= 0) . getCoeff) (getTerms polynomial)

findDominatingDirection :: (Num a, Ord a) => Polynomial a -> Maybe (Assignment Int)
findDominatingDirection terms = error "TODO: compute using Simplex"
  where
    pos_terms = filter ((> 0) . getCoeff) (getTerms terms)

-- |
-- Returns True iff the polynomial evaluates to something positive under 
-- the given variable assignment.
isPositiveSolution :: (Num a, Ord a, Assignable a) => Polynomial a -> Assignment a -> Bool
isPositiveSolution polynomial solution = eval solution polynomial > 0

-- |
positiveSolution :: (Num a, Ord a, Assignable a) => Polynomial a -> Maybe (Assignment a)
positiveSolution polynomial = do
  normal_vector <- findDominatingDirection polynomial

  -- For a sufficiently large base the polynomial should evaluate 
  -- to something positive.
  let bases = [ 2^n | n <- [1..] ]
  let candidates = [ M.map (b^) normal_vector | b <- bases ]

  L.find (isPositiveSolution polynomial) candidates

-- newtype Solution a = Sol { getValues :: Assignment a }

-- instance Num a => Num (Solution a) where
--   (Sol s1) + (Sol s2) = Sol $ M.unionWith (+) s1 s2
--   (Sol s1) * (Sol s2) = Sol $ M.unionWith (*) s1 s2
--   abs (Sol s1) = Sol $ M.map abs s1
--   negate (Sol s1) = Sol $ M.map negate s1
--   signum (Sol s1) = Sol $ M.map signum s1
--   fromInteger i = error "TODO: define this"

-- | Returns True if the polynomial evaluates to 0 under the given variable assignment.
isRoot :: (Num a, Ord a, Assignable a) => Polynomial a -> Assignment a -> Bool
isRoot polynomial solution = eval solution polynomial == 0

{-|
  Given a positive and a negative solution, we can find a root to any multivariate polynomial.
  By the intermediate value theorem, a root lies somewhere on the line segment, connecting the 
  two points. For example, consider the polynomial

    x^2 + y^2 - 3

  The points (1,1) and (2,2) give a negative- and positive solution respectively. Intuitively, 
  the roots of the polynomial form a circle of radius 3. The negative solution correspoinds to 
  a point in the interior of the circle and the positive solution to a point on the exterior.
  So the line segment connecting the two points:

    (1,1) + t*((2,2) - (1,1)) = (1+t, 1+t)               (where 0 <= t <= 1)
  
  must intersect the circle. We find the intersection points by substituting `x = 1+2t` / `y = 1+2t`
  and solving the original polynomial, thereby reducing the problem to finding roots of a univariate 
  polynomial in the interval (0 :..: 1).
-}
intermediateRoot :: forall a. (Num a, Ord a, Assignable a, Fractional a, Floating a) => Polynomial a -> Assignment a -> Assignment a -> Assignment a
intermediateRoot polynomial neg_sol pos_sol =
  let
    -- An arbitrary ID for the variable t. The polynomial we construct is univariate in t, so there is no danger of variable ID collision.
    t = 0

    line_segment_component :: Var -> a -> a -> Expr a
    line_segment_component _ neg_sol_component pos_sol_component =
      Const neg_sol_component + Var t * Const (pos_sol_component - neg_sol_component)

    line_segment_components :: Assignment (Expr a)
    line_segment_components = MM.merge MM.dropMissing MM.dropMissing (MM.zipWithMatched line_segment_component) neg_sol pos_sol

    substitute_all :: Assignment (Expr a) -> Expr a -> Expr a
    substitute_all assignment expr = M.foldrWithKey substitute expr assignment

    t_polynomial = fromExpr $ substitute_all line_segment_components $ toExpr polynomial

    t_roots :: [a]
    t_roots =
      case Univariate.toList <$> Univariate.fromPolynomial t_polynomial of
        Nothing -> error "Polynomial should be univariate by construction"
        -- linear polynomial ==> solve directly for t
        Just [ (0, c), (1, b) ] -> [- b/c ]
        -- quadratic polynomial ==> apply quadratic formula
        Just [ (0, c), (1, b), (2, a) ] ->
          [ (-b + sqrt (b^2 - 4*a*c)) / (2*a)
          , (-b - sqrt (b^2 - 4*a*c)) / (2*a) ]
        -- TODO: higher degree polynomial ==> use CAD
        Just higher_degree_polynomial -> error "TODO: subtropical does not support higher degree polynomials yet"

    t_solution :: Assignment a
    t_solution =
      case L.find (\t' -> 0 <= t' && t' <= 1) t_roots of
        Just value -> M.singleton t value
        Nothing -> error "No solution for t between 0 and 1"
  in
    M.map (eval t_solution . fromExpr) line_segment_components

{-| 
  TODO: deal with multiple constraints
-}
subtropical :: forall a. (Ord a, Assignable a, Floating a) => Constraint a -> Maybe (Assignment a)
subtropical (relation, polynomial) =
  let
    -- The assignment that maps all variables to one. We use it as an arbitrary 
    -- starting point. 
    one :: Assignment a
    one = M.fromList $ map (, 1) (varsIn polynomial)

    -- An assignment for which the polynomial evaluates to something positive.
    -- This is a `Maybe` since Polynomals may not have positve solutions. Additionally,
    -- the algorithm implemented in `posiitveSolutions` is incomplete so it might
    -- miss positive solutions, even if there are some.
    pos_solution :: Maybe (Assignment a)
    pos_solution 
      | eval one polynomial > 0 = Just one
      | otherwise = positiveSolution polynomial

    -- An assignment for which the polynomial evaluates to something negative.
    -- We can also use `positiveSolution` here because a positve solution of
    -- the negated polynomial is a negative solution.
    neg_solution :: Maybe (Assignment a)
    neg_solution 
      | eval one polynomial < 0 = Just one
      | otherwise = positiveSolution (negate polynomial)

    -- An assignment for which the polynomial evaluates to zero, i.e. a root.
    -- With a negative solution and a positive solution, a root must lie 
    -- on the line segment between the two points.
    zero_solution :: Maybe (Assignment a)
    zero_solution
      | eval one polynomial == 0 = Just one
      | otherwise = liftA2 (intermediateRoot polynomial) neg_solution pos_solution
  in
    case relation of
      LessThan      -> neg_solution
      LessEquals    -> neg_solution
      GreaterEquals -> pos_solution
      GreaterThan   -> pos_solution
      Equals        -> zero_solution
