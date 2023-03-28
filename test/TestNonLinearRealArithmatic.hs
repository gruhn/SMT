module TestNonLinearRealArithmatic 
  ( prop_all_coeffs_non_zero
  , prop_exponents_always_non_zero
  , prop_intervals_never_widen
  , prop_no_roots_are_lost
  , prop_unique_monomials  
  ) where

import Hedgehog hiding (eval)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

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

genTerm :: Gen (Term Float)
genTerm = do
  -- TODO: only at most quadratic exponents supported at the moment
  let var_with_exponent = (,) <$> Gen.int (Range.linear 0 10) <*> Gen.int (Range.linear 1 2)
  monomial <- M.fromList <$> Gen.list (Range.linear 1 10) var_with_exponent
  coeff <- Gen.float $ Range.linearFrac (-1000) 1000
  return $ Term coeff monomial

genPolynomial :: Gen (Polynomial Float)
genPolynomial = mkPolynomial <$> Gen.list (Range.linear 0 100) genTerm

prop_all_coeffs_non_zero :: Property
prop_all_coeffs_non_zero = property $ do 
  p1 <- forAll genPolynomial
  p2 <- forAll genPolynomial
  let coeffs = fmap Polynomial.getCoeff $ Polynomial.getTerms $ p1 + p2
  assert $ 0 `notElem` coeffs

prop_exponents_always_non_zero :: Property
prop_exponents_always_non_zero = property $ do
  p1 <- forAll genPolynomial
  p2 <- forAll genPolynomial

  let exponents = do 
        term <- Polynomial.getTerms (p1 * p2)
        M.elems $ Polynomial.getMonomial term

  assert $ 0 `notElem` exponents

prop_unique_monomials :: Property
prop_unique_monomials = property $ do 
  p1 <- forAll genPolynomial
  p2 <- forAll genPolynomial

  let monomials = Polynomial.getMonomial <$> Polynomial.getTerms (p1 + p2)

  nubOrd monomials === monomials

genConstraintRelation :: Gen ConstraintRelation 
genConstraintRelation = 
  Gen.element [Equals, LessEquals, LessThan, GreaterEquals, GreaterThan]

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
  relation <- genConstraintRelation
  return (relation, polynomial)

prop_intervals_never_widen :: Property
prop_intervals_never_widen = property $ do
  constraints <- forAll $ Gen.list (Range.linear 1 20) genConstraint
  initial_bound <- forAll $ Gen.float (Range.linearFrac (-1000) 1000)

  let
    constraints' :: [ Constraint (BoundedFloating Float) ]
    constraints' = second (Polynomial.map Val) <$> constraints

    initial_domain = IntervalUnion [ Val (- abs initial_bound) :..: Val (abs initial_bound) ]
    domains_before = M.fromList $ zip (varsIn constraints') (repeat initial_domain)
    domains_after = intervalConstraintPropagation constraints' domains_before

  assert $ domains_after `allSubsetsOf` domains_before

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
polynomialFromRoots :: NonEmpty (Expr.Var, Float) -> Polynomial (BoundedFloating Float)
polynomialFromRoots var_root_pairs = fromExpr expr
  where
    factor_from :: Expr.Var -> Float -> Expr (BoundedFloating Float)
    factor_from var root = BinaryOp Sub (Const $ Val root) (Expr.Var var)

    expr = foldr1 (BinaryOp Mul) (uncurry factor_from <$> var_root_pairs)

prop_no_roots_are_lost :: Property
prop_no_roots_are_lost = property $ do
  var_count <- forAll $ Gen.int (Range.linear 0 10)
  let vars = [0 .. var_count]

  root_count <- forAll $ Gen.int (Range.linear 1 10)
  -- only generate integer valued floats as roots to reduce numeric issues
  int_roots <- forAll $ Gen.list (Range.singleton root_count) $ Gen.int (Range.linear (-1000) 1000)
  let roots = fmap fromIntegral int_roots  

  -- TODO: Currently, variables can appear at most quadratic, 
  -- so we have to make sure we are not generating polynomials
  -- with larger powers.
  let var_root_pairs = zip (vars <> vars) roots

  -- TODO: generate more than one constraint and also inequality constraints.
  let constraint = (Equals, polynomialFromRoots $ NonEmpty.fromList var_root_pairs)

  let initial_domain = IntervalUnion [ Val (minimum roots - 1) :..: Val (maximum roots + 1) ]
      domains0 = M.fromList $ zip vars (repeat initial_domain)

      final_domains = intervalConstraintPropagation [constraint] domains0

      no_root_lost :: Expr.Var -> Bool
      no_root_lost var = all (`IntervalUnion.elem` domain_of_var) roots_of_var
        where
          domain_of_var = final_domains M.! var
          roots_of_var = do
            (var', root) <- var_root_pairs
            guard (var == var')
            return (Val root)

  assert $ all no_root_lost vars
