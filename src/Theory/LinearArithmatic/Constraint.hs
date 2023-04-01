module Theory.LinearArithmatic.Constraint where

import qualified Data.IntMap.Strict as M
import qualified Data.IntSet as S
import Control.Monad (guard)
import qualified Data.IntMap.Merge.Lazy as MM
import Data.List (intercalate)
import Data.Ratio (denominator, numerator)

type Var = Int

data ConstraintRelation = LessThan | LessEquals | Equals | GreaterEquals | GreaterThan
  deriving (Show, Eq)

flipRelation :: ConstraintRelation -> ConstraintRelation
flipRelation = \case 
  LessThan      -> GreaterThan
  LessEquals    -> GreaterEquals
  Equals        -> Equals
  GreaterEquals -> LessEquals
  GreaterThan   -> LessThan

-- | Map from variable IDs to assigned values
type Assignment = M.IntMap Rational

-- |
-- For example, constraint such as `3x + y + 3 <= 0` is represented as:
--
--     (LessEquals, AffineExpr 3 (3x+y))
-- 
type Constraint = (ConstraintRelation, AffineExpr)

-- | Map from variable IDs to coefficients 
type LinearExpr = M.IntMap Rational

data AffineExpr = AffineExpr
  { getConstant :: Rational  
  , getCoeffMap :: LinearExpr }

instance Show AffineExpr where
  show (AffineExpr constant coeff_map) =
    let 
      show_ratio ratio =
        show (numerator ratio) ++
        if denominator ratio == 1 then
          ""
        else 
          "/" ++ show (denominator ratio)

      show_signed ratio =
        if ratio < 0 then
          "(" ++ show_ratio ratio ++ ")"
        else 
          show_ratio ratio

      show_var (var, coeff) = 
        show_signed coeff ++ "*x" ++ show var
        
     in 
      intercalate " + " (fmap show_var (M.toList coeff_map) ++ [show_signed constant])

varsIn :: Constraint -> S.IntSet
varsIn (_, AffineExpr _ coeff_map) = M.keysSet coeff_map

appearsIn :: Var -> Constraint -> Bool
appearsIn var = M.member var . getCoeffMap . snd

{-|
  Solve a constraint for a variable. For example solving

    0 <= 3x + 10y - 1

  for x, yields

    x >= -10/3y + 1/3

  Returns `Nothing`, if the given variable does not appear in the 
  expression or the coefficient is zero. 
-}
solveFor :: Constraint -> Var -> Maybe Constraint
solveFor (rel, AffineExpr constant coeffs) x = do
  coeff_of_x <- M.lookup x coeffs
  guard (coeff_of_x /= 0)

  let rel' = if coeff_of_x < 0 then flipRelation rel else rel

  return 
    -- flip the relation:             x >= -10/3y + 1/3
    $ (rel', )
    -- also divide constant term:     x <= -10/3y + 1/3
    $ AffineExpr (- constant / coeff_of_x)
    -- divide coefficients:           x <= -10/3y - 1
    $ M.map (/ (-coeff_of_x))
    -- get x on the other side:     -3x <= 10y - 1
    $ M.delete x coeffs

eval :: Assignment -> AffineExpr -> Rational
eval assignment (AffineExpr constant coeff_map) =
  (constant +) $ sum $
    MM.merge
      MM.dropMissing
      MM.dropMissing
      (MM.zipWithMatched (const (*)))
      assignment
      coeff_map

