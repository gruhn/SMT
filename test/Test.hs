module Main where

-- import Test.Tasty
-- import Test.Tasty.HUnit
-- import Test.Tasty.QuickCheck
import Hedgehog
import Hedgehog.Main (defaultMain)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import qualified TestNonLinearRealArithmatic as TestNRA
import qualified TestLinearArithmatic as TestLA

main :: IO ()
main = defaultMain $ checkParallel <$> 
  TestLA.testGroups ++ TestNRA.testGroups
  