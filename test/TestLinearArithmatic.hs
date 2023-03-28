{-# LANGUAGE ScopedTypeVariables #-}
module TestLinearArithmatic (prop_simplex_sound) where

import Hedgehog hiding (eval)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Theory.LinearArithmatic.Simplex
import qualified Data.IntMap as M

isModel :: Assignment -> [Constraint] -> Bool
isModel assignment constraints =
  let
    check :: Constraint -> Bool
    check (linear_term, rel, bound) = 
      case rel of 
        LessThan      -> eval assignment linear_term < bound
        LessEquals    -> eval assignment linear_term <= bound
        Equals        -> eval assignment linear_term == bound
        GreaterEquals -> eval assignment linear_term >= bound
        GreaterThan   -> eval assignment linear_term > bound
  in
    all check constraints

-- TODO: generate more representative constraint sets 
-- newtype Constraint' a = Constraint' (Constraint a)

-- instance Arbitrary a => Arbitrary (Constraint' a) where
--   arbitrary = do
--     var <- chooseInt (0, 10)
--     coeff <- arbitrary
--     _
--     return $ Constraint'

prop_simplex_sound :: Property
prop_simplex_sound = property $ do
  constraints <- forAll $ Gen.list (Range.linear 1 50) $ do
    linear_term <- fmap M.fromList $ Gen.list (Range.linear 0 10) $ do 
      -- coeff <- Gen.float (Range.linearFrac (-1000.0) 1000.0)
      coeff <- toRational <$> Gen.int (Range.linear (-100) 100)
      var <- Gen.int (Range.linear 0 20)
      return (var, coeff)

    -- TODO: extend Simplex to all constraint relation types
    rel <- Gen.element [LessEquals, GreaterEquals]  

    constant <- toRational <$> Gen.int (Range.linear (-100) 100)
    -- constant <- Gen.float (Range.linearFrac (-100.0) 100.0)

    return (linear_term, rel, constant)

  case simplex constraints of
    Nothing         -> success
    Just assignment -> do 
      annotate $ show assignment 
      assert $ assignment `isModel` constraints
