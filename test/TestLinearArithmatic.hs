module TestLinearArithmatic 
  ( prop_simplex_sound
  , prop_fourier_motzkin_sound
  , prop_fourier_motzkin_equiv_simplex  
  ) where

import Hedgehog hiding (eval)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Theory.LinearArithmatic.Simplex
import qualified Data.IntMap as M
import Theory.LinearArithmatic.Constraint
import Theory.LinearArithmatic.FourierMotzkin (fourierMotzkin)
import Data.Maybe (isJust)

-- TODO: generate more representative constraint sets 
genConstraints :: Int -> Int -> Gen [Constraint]
genConstraints max_vars max_constraints =  Gen.list (Range.linear 1 max_constraints) $ do
  linear_expr <- fmap M.fromList $ Gen.list (Range.linear 0 10) $ do 
    coeff <- toRational <$> Gen.int (Range.linearFrom 0 (-100) 100)
    var <- Gen.int (Range.linear 0 max_vars)
    return (var, coeff)

  -- TODO: extend to all constraint types
  rel <- Gen.element [LessEquals, GreaterEquals]  

  constant <- toRational <$> Gen.int (Range.linearFrom 0 (-100) 100)

  -- TODO: make sure that constraints are always normalized by construction.  
  return $ normalize (AffineExpr constant linear_expr, rel)

prop_simplex_sound :: Property
prop_simplex_sound = property $ do
  constraints <- forAll (genConstraints 20 50)
  case simplex constraints of
    Nothing         -> success
    Just assignment -> do 
      annotate $ show assignment 
      assert $ all (assignment `isModel`) constraints

-- TODO
-- invariant: non basic variables always satisfy their bounds

-- TODO:
-- invariant: assignment always satisfies `A*x = 0`

prop_fourier_motzkin_sound :: Property
prop_fourier_motzkin_sound = property $ do
  constraints <- forAll (genConstraints 5 5)
  case fourierMotzkin constraints of
    Nothing         -> success
    Just assignment -> do 
      annotate $ show assignment 
      assert $ all (assignment `isModel`) constraints

-- TODO: gets "stuck" on some inputs. Too slow? Memory leak?
prop_fourier_motzkin_equiv_simplex :: Property
prop_fourier_motzkin_equiv_simplex = property $ do
  constraints <- forAll (genConstraints 5 5)
  isJust (fourierMotzkin constraints) === isJust (simplex constraints)
