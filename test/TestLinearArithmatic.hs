{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
module TestLinearArithmatic (testGroups) where

import Hedgehog hiding (eval)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Theory.LinearArithmatic.Simplex
import qualified Data.IntMap as M

testGroups = 
  [ Group "Theory - Linear Arithmatic"
    [ ("Simplex method is sound", prop_simplex_sound)
    ]
  ]

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
  constraints <- forAll $ Gen.list (Range.linear 1 50) $ do
    linear_term <- fmap M.fromList $ Gen.list (Range.linear 0 20) $ do 
      coeff <- Gen.float (Range.linearFrac (-1000.0) 1000.0)
      var <- Gen.int (Range.linear 0 20)
      return (var, coeff)

    -- TODO: extend Simplex to all constraint relation types
    rel <- Gen.element [LessEquals, GreaterEquals]  

    constant <- Gen.float (Range.linearFrac (-1000.0) 1000.0)

    return (linear_term, rel, constant)

  case simplex constraints of
    Nothing         -> success
    Just assignment -> assert $ assignment `isModel` constraints
