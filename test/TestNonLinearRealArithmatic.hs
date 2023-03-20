{-# LANGUAGE FlexibleInstances #-}
module TestNonLinearRealArithmatic (tests) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import qualified Theory.NonLinearRealArithmatic.Expr as Expr
import Theory.NonLinearRealArithmatic.Expr (Expr (BinaryOp, Var, Const), Var, BinaryOp (Mul, Sub))
import qualified Theory.NonLinearRealArithmatic.Polynomial as Polynomial
import Theory.NonLinearRealArithmatic.Polynomial (Polynomial, mkPolynomial, fromExpr, Term (Term), Assignment)
import qualified Data.List.NonEmpty as NonEmpty
import Data.List.NonEmpty ( NonEmpty, nonEmpty )
import Data.Maybe (fromJust)
import Theory.NonLinearRealArithmatic.Interval (Interval((:..:)))
import Theory.NonLinearRealArithmatic.IntervalConstraintPropagation (intervalConstraintPropagation)
import Theory.NonLinearRealArithmatic.Constraint (Constraint, ConstraintRelation (..), varsIn)
import qualified Data.List as NonEmtpy
import Theory.NonLinearRealArithmatic.IntervalUnion (IntervalUnion(IntervalUnion))
import qualified Data.IntMap as M
import Theory.NonLinearRealArithmatic.BoundedFloating (BoundedFloating (Val))
import qualified Theory.NonLinearRealArithmatic.IntervalUnion as IntervalUnion
import Control.Monad (guard)
import Data.Containers.ListUtils (nubOrd)
import Control.Arrow (second)

tests :: TestTree
tests = testGroup "Theory - Non Linear Real Arithmatic"
  [ testGroup "Polynomial"
      [ testProperty "Coefficients are always non-zero" prop_all_coeffs_non_zero
      , testProperty "Exponents are always non-zero" prop_exponents_always_non_zero
      , testProperty "Monomials are pair-wise distinct" prop_unique_monomials
      ]
  , testGroup "Interval Constraint Propagation"
      [ testProperty "Intervals never widen" prop_intervals_never_widen
      , testProperty "No roots are lost" prop_no_roots_are_lost
      ]
  ]

genTerm :: Arbitrary a => Gen (Term a)
genTerm = do
  -- TODO: only at most quadratic exponents supported at the moment
  let var_with_exponent = (,) <$> chooseInt (0,10) <*> chooseInt (1,2)

  monomial <- M.fromList <$> listOf var_with_exponent
  coeff <- arbitrary

  return $ Term coeff monomial

genPolynomial :: (Arbitrary a, Num a, Ord a) => Gen (Polynomial a)
genPolynomial = mkPolynomial <$> listOf genTerm

prop_all_coeffs_non_zero :: Property
prop_all_coeffs_non_zero = property $ do 
  p1 <- genPolynomial
  p2 <- genPolynomial
  let coeffs :: [Int]
      coeffs = fmap Polynomial.getCoeff $ Polynomial.getTerms $ p1 + p2
  return $ 0 `notElem` coeffs

prop_exponents_always_non_zero :: Property
prop_exponents_always_non_zero = property $ do
  p1 <- genPolynomial :: Gen (Polynomial Int)
  p2 <- genPolynomial :: Gen (Polynomial Int)

  let exponents :: [Int]
      exponents = do 
        term <- Polynomial.getTerms (p1 * p2)
        M.elems $ Polynomial.getMonomial term

  return $ 0 `notElem` exponents

prop_unique_monomials :: Property
prop_unique_monomials = property $ do 
  p1 <- genPolynomial :: Gen (Polynomial Float)
  p2 <- genPolynomial :: Gen (Polynomial Float)

  let monomials = Polynomial.getMonomial <$> Polynomial.getTerms (p1 + p2)

  return $ nubOrd monomials == monomials

instance Arbitrary ConstraintRelation where
  arbitrary = elements [Equals, LessEquals, LessThan, GreaterEquals, GreaterThan]

instance Arbitrary a => Arbitrary (NonEmpty a) where
  arbitrary = NonEmpty.fromList <$> listOf1 arbitrary

allSubsetsOf :: Ord a => Assignment (IntervalUnion a) -> Assignment (IntervalUnion a) -> Bool
allSubsetsOf domains1 domains2 = and $
  M.mergeWithKey
    (\_ dom1 dom2 -> Just $ IntervalUnion.isSubsetOf dom1 dom2)
    (const M.empty)
    (const M.empty)
    domains1
    domains2

genConstraint :: Gen (Constraint Float)
genConstraint = do
  polynomial <- genPolynomial
  relation <- elements [Equals, LessEquals, LessThan, GreaterEquals, GreaterThan]
  return (relation, polynomial)

prop_intervals_never_widen :: Property
prop_intervals_never_widen = property $ do
  constraints <- listOf genConstraint
  initial_bound <- arbitrary :: Gen Float

  let
    constraints' :: [ Constraint (BoundedFloating Float) ]
    constraints' = second (Polynomial.map Val) <$> constraints

    initial_domain = IntervalUnion [ Val (- abs initial_bound) :..: Val (abs initial_bound) ]
    domains_before = M.fromList $ zip (varsIn constraints') (repeat initial_domain)
    domains_after = intervalConstraintPropagation constraints' domains_before

  return $
    domains_after `allSubsetsOf` domains_before

-- | 
-- Make a polynomial from a given list of roots, such as 
--    
--   [ 3, 1/2, 0, -1 ]
--
-- First, We generate an expression in factored from
-- 
--   (3 - x)(1/2 - y)(0 - x)(-1 - y)
--
-- Then we multiply out to obtain a normalized polynomial.
--
-- This is useful for testing the root finding algorithms, 
-- because we can generate random polynomials but with known roots.
polynomialFromRoots :: NonEmpty (Var, Float) -> Polynomial (BoundedFloating Float)
polynomialFromRoots var_root_pairs = fromExpr expr
  where
    factor_from :: Var -> Float -> Expr (BoundedFloating Float)
    factor_from var root = BinaryOp Sub (Const $ Val root) (Var var)

    expr = foldr1 (BinaryOp Mul) (uncurry factor_from <$> var_root_pairs)

prop_no_roots_are_lost :: Property
prop_no_roots_are_lost = property $ do
  var_count <- chooseInt (0, 10)
  let vars = [0 .. var_count]

  root_count <- chooseInt (1, 10)
  -- only generate integer valued floats as roots to reduce numeric issues
  int_roots <- vectorOf root_count arbitrary :: Gen [Int]
  let roots = fmap fromIntegral int_roots :: [Float]
  
  -- TODO: Currently, variables can appear at most quadratic, 
  -- so we have to make sure we are not generating polynomials
  -- with larger powers.
  let var_root_pairs = zip (vars <> vars) roots

  -- TODO: generate more than one constraint and also inequality constraints.
  let constraint = (Equals, polynomialFromRoots $ NonEmpty.fromList var_root_pairs)

  let initial_domain = IntervalUnion [ Val (minimum roots - 1) :..: Val (maximum roots + 1) ]
      domains0 = M.fromList $ zip vars (repeat initial_domain)

      final_domains = intervalConstraintPropagation [constraint] domains0

      no_root_lost :: Var -> Bool
      no_root_lost var = all (`IntervalUnion.elem` domain_of_var) roots_of_var
        where
          domain_of_var = final_domains M.! var
          roots_of_var = do
            (var', root) <- var_root_pairs
            guard (var == var')
            return (Val root)

  return $ all no_root_lost vars
