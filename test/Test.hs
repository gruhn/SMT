module Main where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

-- import qualified TestPropositions as TestProp
import qualified TestNonLinearRealArithmatic as TestNRA

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "All tests"
  [ TestNRA.tests 
  -- , TestProp.tests
  ]