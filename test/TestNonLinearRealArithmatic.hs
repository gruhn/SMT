{-# LANGUAGE FlexibleInstances #-}
module TestNonLinearRealArithmatic (tests) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import qualified Theory.NonLinearRealArithmatic.Expr as Expr
import Theory.NonLinearRealArithmatic.Expr (Expr (BinaryOp, Var, Const), Var, BinaryOp (Mul, Sub))
import qualified Theory.NonLinearRealArithmatic.Polynomial as Polynomial
import Theory.NonLinearRealArithmatic.Polynomial (Polynomial (Polynomial), fromExpr)
import qualified Data.List.NonEmpty as NonEmpty
import Data.List.NonEmpty ( NonEmpty, nonEmpty )
import Data.Maybe (fromJust)
import Theory.NonLinearRealArithmatic.Interval (Interval((:..:)))
import Theory.NonLinearRealArithmatic.IntervalConstraintPropagation (Constraint, ConstraintRelation (Equals), VarDomains, intervalConstraintPropagation)
import qualified Data.List as NonEmtpy
import Theory.NonLinearRealArithmatic.IntervalUnion (IntervalUnion(IntervalUnion))
import qualified Data.IntMap as M
import Theory.NonLinearRealArithmatic.BoundedFloating (BoundedFloating (Val))
import qualified Theory.NonLinearRealArithmatic.IntervalUnion as IntervalUnion
import Control.Monad (guard)

-- TODO: property test "expression is equivalent to polynomial"
--       property test "all coeffitients are always non-zero"
--       property test "key set of all monomials is the same"

tests :: TestTree
tests = testGroup "Interval Constraint Propagation"
  [ testProperty "No roots are lost" prop_no_roots_are_lost 
  , testProperty "Interval diameters never increase" prop_interval_diameters_never_increase 
  ]

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
mkPolynomial :: NonEmpty (Var, Float) -> Polynomial (BoundedFloating Float)
mkPolynomial var_root_pairs = fromExpr expr
  where
    factor_from :: Var -> Float -> Expr (BoundedFloating Float)
    factor_from var root = BinaryOp Sub (Const $ Val root) (Var var)

    expr = foldr1 (BinaryOp Mul) (uncurry factor_from <$> var_root_pairs)

newtype ConstraintWithSolution = CWS 
  { getCWS :: (Constraint (BoundedFloating Float), [(Var, Float)]) }
    deriving Show

mkCWS :: [Var] -> [Float] -> ConstraintWithSolution
mkCWS vars roots = CWS (constraint, var_root_pairs)
  where
    -- TODO: Currently, variables can appear at most quadratic, 
    -- so we have to make sure we are not generating polynomials
    -- with larger powers.
    var_root_pairs = zip (vars <> vars) roots

    -- TODO: generate more than one constraint and also inequality constraints.
    constraint = (Equals, mkPolynomial $ NonEmpty.fromList var_root_pairs)

instance Arbitrary ConstraintWithSolution where
  arbitrary = do
    var_count <- chooseInt (0, 10)
    root_count <- chooseInt (1, 10)
    -- only generate integer valued floats as roots to reduce numeric issues
    roots <- vectorOf root_count arbitrary :: Gen [Int]
    return $ mkCWS [0 .. var_count] (fromIntegral <$> roots)

prop_no_roots_are_lost :: ConstraintWithSolution -> Bool
prop_no_roots_are_lost (CWS (constraint, var_root_pairs)) = all no_root_lost vars
  where
    (vars, roots) = unzip var_root_pairs

    initial_domain = IntervalUnion [ Val (minimum roots - 1) :..: Val (maximum roots + 1) ]
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

allSubsetsOf :: Ord a => VarDomains a -> VarDomains a -> Bool
allSubsetsOf domains1 domains2 = and $
  M.mergeWithKey
    (\_ dom1 dom2 -> Just $ IntervalUnion.isSubsetOf dom1 dom2) 
    (const M.empty)
    (const M.empty)
    domains1
    domains2

prop_interval_diameters_never_increase :: ConstraintWithSolution -> Bool
prop_interval_diameters_never_increase (CWS (constraint, var_root_pairs)) =
  let
    (vars, roots) = unzip var_root_pairs

    initial_domain = IntervalUnion [ Val (minimum roots - 1) :..: Val (maximum roots + 1) ]
    domains_before = M.fromList $ zip vars (repeat initial_domain)
    domains_after = intervalConstraintPropagation [constraint] domains_before
  in 
    domains_after `allSubsetsOf` domains_before
