{-# LANGUAGE ScopedTypeVariables #-}
module TestLinearArithmatic 
  ( prop_simplex_sound
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

isModel :: Assignment -> Constraint -> Bool
isModel assignment (rel, affine_expr) = 
  case rel of 
    LessThan      -> eval assignment affine_expr < 0
    LessEquals    -> eval assignment affine_expr <= 0
    Equals        -> eval assignment affine_expr == 0
    GreaterEquals -> eval assignment affine_expr >= 0
    GreaterThan   -> eval assignment affine_expr > 0

-- TODO: generate more representative constraint sets 
-- newtype Constraint' a = Constraint' (Constraint a)

-- instance Arbitrary a => Arbitrary (Constraint' a) where
--   arbitrary = do
--     var <- chooseInt (0, 10)
--     coeff <- arbitrary
--     _
--     return $ Constraint'

genConstraints :: Int -> Gen [Constraint]
genConstraints max_constraints =  Gen.list (Range.linear 1 max_constraints) $ do
  linear_expr <- fmap M.fromList $ Gen.list (Range.linear 0 10) $ do 
    -- coeff <- Gen.float (Range.linearFrac (-1000.0) 1000.0)
    coeff <- toRational <$> Gen.int (Range.linearFrom 0 (-100) 100)
    var <- Gen.int (Range.linear 0 20)
    return (var, coeff)

  -- TODO: extend Simplex to all constraint relation types
  rel <- Gen.element [LessEquals, GreaterEquals]  

  constant <- toRational <$> Gen.int (Range.linearFrom 0 (-100) 100)
  -- constant <- Gen.float (Range.linearFrac (-100.0) 100.0)

  return (rel, AffineExpr constant linear_expr)

prop_simplex_sound :: Property
prop_simplex_sound = property $ do
  constraints <- forAll (genConstraints 50)
  case simplex constraints of
    Nothing         -> success
    Just assignment -> do 
      annotate $ show assignment 
      assert $ all (assignment `isModel`) constraints

-- TODO
-- invariant: non basic variables always satisfy their bounds

-- TODO:
-- invariant: assignment always satisfies `A*x = 0`

-- TODO
-- prop_fourier_motzkin_sound :: Property
-- prop_fourier_motzkin_sound = _

-- TODO: gets "stuck" on some inputs. Too slow? Memory leak?
prop_fourier_motzkin_equiv_simplex :: Property
prop_fourier_motzkin_equiv_simplex = property $ do
  constraints <- forAll (genConstraints 10)
  fourierMotzkin constraints === isJust (simplex constraints)
