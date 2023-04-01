module Theory.LinearArithmatic.FourierMotzkin (fourierMotzkin) where

import Theory.LinearArithmatic.Constraint
import qualified Data.IntMap.Strict as M
import qualified Data.IntSet as S
import Control.Monad (guard)
import qualified Data.Vector as V
import Data.Maybe (fromMaybe, mapMaybe)
import Data.List (partition)
import Debug.Trace

{-|
  Trivial constraints have no variables and are satisfied, such as 0 < 1.
-}
isTrivial :: Constraint -> Bool
isTrivial (rel, AffineExpr constant coeff_map) = 
  S.null (M.keysSet coeff_map) && case rel of
    LessThan      -> constant <  0
    LessEquals    -> constant <= 0
    Equals        -> constant == 0
    GreaterEquals -> constant >= 0
    GreaterThan   -> constant >  0

eliminate :: Var -> [Constraint] -> [Constraint]
eliminate var constraints =
  let 
    (constraints_with_var, constraints_without_var) = 
      partition (var `appearsIn`) constraints

    constraints_with_var_eliminated :: [Constraint]
    constraints_with_var_eliminated = do
      -- c1: x - 1 >= 0
      -- c2: 2x + 4 <= 0
      let constraints_with_var' =
            mapMaybe (`solveFor` var) constraints_with_var

      -- c1: x <= 1
      (upper_bound_rel, AffineExpr ub_const ub_coeffs) <- constraints_with_var'
      guard (upper_bound_rel == LessEquals)

      -- c2: x >= -2
      (lower_bound_rel, AffineExpr lb_const lb_coeffs) <- constraints_with_var'
      guard (lower_bound_rel == GreaterEquals)

      -- -2 <= x <= 1
      -- -2     <= 1
      -- -2 - 1 <= 0
      return 
        ( LessEquals
        , AffineExpr 
            (lb_const - ub_const)
            (M.unionWith (-) lb_coeffs ub_coeffs) 
        )
  in
   constraints_without_var <> constraints_with_var_eliminated

fourierMotzkin :: [Constraint] -> Bool
fourierMotzkin = go . fmap reject_zero_coeffs
  where
    reject_zero_coeffs :: Constraint -> Constraint
    reject_zero_coeffs (rel, AffineExpr constant expr) = 
      (rel, AffineExpr constant $ M.filter (/= 0) expr)

    go :: [Constraint] -> Bool
    go constraints
      | not (all isTrivial constraints_no_vars) = False
      | null constraints_with_vars = True
      | otherwise = fourierMotzkin (eliminate next_var constraints_with_vars)
      where
        (constraints_no_vars, constraints_with_vars) = 
          partition (S.null . varsIn) constraints

        next_var = fst 
          $ M.findMin 
          $ getCoeffMap . snd 
          $ head constraints_with_vars

-- linearDependent :: Constraint -> Constraint -> Bool
-- linearDependent vs ws = coeff /= 0 && V.map (* coeff) vs == ws
--   where
--     div' x y
--       | y == 0    = 0
--       | otherwise = x/y
--     coeff =
--       fromMaybe 0 $ V.find (/=0) $ V.zipWith div' ws vs 

--------------------------------------

-- SAT
example1 = 
  [ ( GreaterEquals
    , AffineExpr 1 (M.singleton 0 (-1)) 
    )
  , ( GreaterEquals
    , AffineExpr 0 (M.singleton 0 7)
    )
  ]

example2 = 
  [ (LessEquals, AffineExpr 0 $ M.singleton 0 (-1))
  , (GreaterEquals, AffineExpr 1 $ M.singleton 0 (-1))
  ]
