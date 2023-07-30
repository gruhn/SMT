module Theory.LinearArithmatic.Constraint where

import qualified Data.IntMap.Strict as M
import qualified Data.IntSet as S
import Control.Monad (guard)
import qualified Data.IntMap.Merge.Lazy as MM
import Data.List (intercalate)
import Data.Ratio (denominator, numerator)
import Debug.Trace
import Theory (Assignment)

type Var = Int

data ConstraintRelation = LessThan | LessEquals | GreaterEquals | GreaterThan
  deriving (Show, Eq, Ord)

flipRelation :: ConstraintRelation -> ConstraintRelation
flipRelation = \case 
  LessThan      -> GreaterThan
  LessEquals    -> GreaterEquals
  GreaterEquals -> LessEquals
  GreaterThan   -> LessThan

negateRelation :: ConstraintRelation -> ConstraintRelation
negateRelation = \case 
  LessThan      -> GreaterEquals
  LessEquals    -> GreaterThan
  GreaterEquals -> LessThan
  GreaterThan   -> LessEquals

-- |
-- For example, constraint such as `3x + y + 3 <= 0` is represented as:
--
--     (AffineExpr 3 (3x+y), LessEquals)
-- 
data Constraint = Constr { getExpr :: AffineExpr, getRaltion :: ConstraintRelation }
  deriving (Eq, Ord)

modifyExpr :: (AffineExpr -> AffineExpr) -> Constraint -> Constraint
modifyExpr f (Constr expr rel) = Constr (f expr) rel

{-|
  Remove variables with zero coefficient.
  TODO: ensure that constraints are always normalized.
-}
normalize :: Constraint -> Constraint
normalize (Constr (AffineExpr constant expr) rel) = 
  Constr (AffineExpr constant $ M.filter (/= 0) expr) rel

-- | Map from variable IDs to coefficients 
type LinearExpr = M.IntMap Rational

data AffineExpr = AffineExpr
  { getConstant :: Rational  
  , getCoeffMap :: LinearExpr }
  deriving (Eq, Ord)

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
      intercalate " + " (fmap show_var (M.toList coeff_map) ++ [ show_signed constant | constant /= 0 ])

varsIn :: Constraint -> S.IntSet
varsIn (Constr (AffineExpr _ coeff_map) _) = M.keysSet coeff_map

varsInAll :: [Constraint] -> S.IntSet
varsInAll = foldr (S.union . varsIn) S.empty

appearsIn :: Var -> Constraint -> Bool
appearsIn var = M.member var . getCoeffMap . getExpr

modifyConstant :: (Rational -> Rational) -> AffineExpr -> AffineExpr
modifyConstant f (AffineExpr constant coeffs) = AffineExpr (f constant) coeffs

{-|
  Solve a constraint for a variable. For example solving

    0 <= 3x + 10y - 1

  for x, yields

    x >= -10/3y + 1/3

  Returns `Nothing`, if the given variable does not appear in the 
  expression or the coefficient is zero. 
-}
solveFor :: Constraint -> Var -> Maybe (Var, ConstraintRelation, AffineExpr)
solveFor (Constr (AffineExpr constant coeffs) rel) x = do
  coeff_of_x <- M.lookup x coeffs
  guard (coeff_of_x /= 0)

  let rel' = if coeff_of_x < 0 then flipRelation rel else rel

  return 
    -- flip the relation:             x >= -10/3y + 1/3
    $ (x, rel', )
    -- also divide constant term:     x <= -10/3y + 1/3
    $ AffineExpr (- constant / coeff_of_x)
    -- divide coefficients:           x <= -10/3y - 1
    $ M.map (/ (-coeff_of_x))
    -- get x on the other side:     -3x <= 10y - 1
    $ M.delete x coeffs

substitute :: Assignment Rational -> AffineExpr -> AffineExpr
substitute partial_assignment (AffineExpr constant coeff_map) = 
  let 
    constant' = (constant +) $ sum $
      MM.merge
        MM.dropMissing
        MM.dropMissing
        (MM.zipWithMatched (const (*)))
        partial_assignment
        coeff_map

    coeff_map' = coeff_map `M.withoutKeys` M.keysSet partial_assignment
  in 
    AffineExpr constant' coeff_map'

{-|
  Evaluate an expression by substituting all variables 
  using the given assignment. Returns `Nothing` if the 
  assignment is partial.
-}
eval :: Assignment Rational -> AffineExpr -> Maybe Rational
eval assignment expr
  | M.null coeff_map = Just constant
  | otherwise        = Nothing
  where
    AffineExpr constant coeff_map = substitute assignment expr


-- linearDependent :: Constraint -> Constraint -> Bool
-- linearDependent vs ws = coeff /= 0 && V.map (* coeff) vs == ws
--   where
--     div' x y
--       | y == 0    = 0
--       | otherwise = x/y
--     coeff =
--       fromMaybe 0 $ V.find (/=0) $ V.zipWith div' ws vs 

{-|
  Checks if the assignment satisfies the constraints.
-}
isModel :: Assignment Rational -> Constraint -> Bool
isModel assignment (Constr affine_expr rel) = 
  case (eval assignment affine_expr, rel) of 
    (Just value, LessThan     ) -> value <  0
    (Just value, LessEquals   ) -> value <= 0
    (Just value, GreaterEquals) -> value >= 0
    (Just value, GreaterThan  ) -> value >  0
    (Nothing   , _            ) -> False

-- | True iff constraint contains no free variables
isGround :: Constraint -> Bool
isGround = M.null . getCoeffMap . getExpr 

-- | True iff constraint contains at least one free variable.
isOpen :: Constraint -> Bool
isOpen = not . isGround
