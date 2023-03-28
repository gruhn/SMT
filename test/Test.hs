{-# LANGUAGE OverloadedStrings #-}
module Main where

import Hedgehog
import Hedgehog.Main (defaultMain)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import TestNonLinearRealArithmatic
import TestLinearArithmatic

main :: IO ()
main = defaultMain $ checkParallel <$>
  [ Group "Polynomial"
      [ ("Coefficients are always non-zero", prop_all_coeffs_non_zero)
      , ("Exponents are always non-zero", prop_exponents_always_non_zero)
      , ("Monomials are pair-wise distinct", prop_unique_monomials)
      ]
  , Group "Interval Constraint Propagation"
      [ ("Intervals never widen", prop_intervals_never_widen)
      , ("No roots are lost", prop_no_roots_are_lost)
      ]
  , Group "Theory - Linear Arithmatic"
    [ ("Simplex method is sound", withTests 1000 $ prop_simplex_sound)
    ]
  ]

-- TODO: Simplex seems still incorrect. Some runs spin forever/consume a 
-- lot of memory, e.g:

-- main :: IO ()
-- main = do
--   recheckAt (Seed 6028160336680363614 11864191702326251993) "1667:" prop_simplex_sound
