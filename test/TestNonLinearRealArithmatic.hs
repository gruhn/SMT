{-# LANGUAGE FlexibleInstances #-}
module TestNonLinearRealArithmatic (tests, prop_icp_does_not_loose_roots, mkCWS) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import qualified Theory.NonLinearRealArithmatic.Expr as Expr
import Theory.NonLinearRealArithmatic.Expr (Expr (BinaryOp, Var, Const), Var, BinaryOp (Mul, Sub))
import qualified Theory.NonLinearRealArithmatic.Polynomial as Polynomial
import Theory.NonLinearRealArithmatic.Polynomial (Polynomial, fromExpr)
import qualified Data.List.NonEmpty as NonEmpty
import Data.List.NonEmpty ( NonEmpty, nonEmpty )
import Data.Maybe (fromJust)
import Theory.NonLinearRealArithmatic.Interval (Interval((:..:)))
import Theory.NonLinearRealArithmatic.IntervalConstraintPropagation (Constraint, ConstraintRelation (Equals), VarDomains, icp)
import qualified Data.List as NonEmtpy
import Theory.NonLinearRealArithmatic.IntervalUnion (IntervalUnion(IntervalUnion))
import qualified Data.IntMap as M
import Theory.NonLinearRealArithmatic.BoundedFloating (BoundedFloating (Val))
import qualified Theory.NonLinearRealArithmatic.IntervalUnion as IntervalUnion
import Control.Monad (guard)
import Debug.Trace

-- TODO: property test "expression is equivalent to polynomial"
--       property test "all coeffitients are always non-zero"
--       property test "key set of all monomials is the same"

tests :: TestTree
tests = testGroup "Theory - Non Linear Real Arithmatic"
  [ testProperty "No roots are lost through interval constraint propagation" prop_icp_does_not_loose_roots ]

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
    roots <- vectorOf root_count arbitrary
    return $ mkCWS [0 .. var_count] roots

prop_icp_does_not_loose_roots :: ConstraintWithSolution -> Bool
prop_icp_does_not_loose_roots (CWS (constraint, var_root_pairs)) = all no_root_lost vars
  where
    (vars, roots) = unzip var_root_pairs

    initial_domain = IntervalUnion [ Val (minimum roots - 1) :..: Val (maximum roots + 1) ]
    domains0 = M.fromList $ zip vars (repeat initial_domain)

    -- TODO: arbitrarily number of contraction iterations here. What would be more principled?
    --       Also don't contract all contraction condidates. It seems to be too expensive.
    final_domains = traceShowId $ icp [constraint] domains0 !! 10

    no_root_lost :: Var -> Bool
    no_root_lost var = all (`IntervalUnion.elem` domain_of_var) roots_of_var
      where
        domain_of_var = final_domains M.! var
        roots_of_var = do
          (var', root) <- var_root_pairs          
          guard (var == var')
          return (Val root)
