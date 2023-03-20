{-# LANGUAGE ScopedTypeVariables #-}
module TestLinearArithmatic (tests) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import Theory.LinearArithmatic.Simplex
import qualified Data.IntMap as M

tests :: TestTree
tests = testGroup "Theory - Linear Arithmatic"
  [ testProperty "Simplex method is sound" prop_simplex_sound
  ]

-- TODO: extend Simplex to all constraint relation types
instance Arbitrary ConstraintRelation where
  arbitrary = elements [LessEquals, GreaterEquals]

isModel :: forall a. (Eq a, Num a, Ord a) => Assignment a -> [Constraint a] -> Bool
isModel assignment constraints =
  let
    check :: Constraint a -> Bool
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
  constraints <- listOf $ do
    linear_term <- fmap M.fromList $ listOf $ do 
      coeff <- arbitrary :: Gen Float
      var <- chooseInt (0, 20)
      return (var, coeff)

    -- TODO: extend Simplex to all constraint relation types
    rel <- elements [LessEquals, GreaterEquals]  

    constant <- arbitrary :: Gen Float

    return (linear_term, rel, constant)

  return $ case simplex constraints of
    Nothing         -> True
    Just assignment -> assignment `isModel` constraints
