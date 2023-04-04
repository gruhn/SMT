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
  , Group "Simplex / Fourier-Motzkin"
    [ ("Fourier-Motzkin is sound", prop_fourier_motzkin_sound)
    , ("Fourier-Motzkin equivalent to Simplex", prop_fourier_motzkin_equiv_simplex)
    , ("Invariant: non-basic variables always satisfy their bounds", prop_invariant_non_basic_vars_satisfy_bounds)
    , ("Invariant: assignment matches basis evaluation", prop_invariant_assignment_matches_basis_evaluation)
    , ("Simplex does not cycle", withTests 10000 $ prop_simplex_no_cycle)
    , ("Simplex is sound", withTests 10000 $ prop_simplex_sound)
    ]
  ]
