module Main where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import qualified TestNonLinearRealArithmatic as TestNRA
import qualified TestLinearArithmatic as TestLA

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "All tests"
  [ TestNRA.tests 
  , TestLA.tests
  ]