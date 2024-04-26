module Theory.LinearArithmatic.Constraint where

import qualified Data.IntMap.Strict as M
import qualified Data.IntSet as S
import Control.Monad (guard)
import qualified Data.IntMap.Merge.Lazy as MM
import Data.List (intercalate)
import Data.Ratio (denominator, numerator)
import Debug.Trace

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
--     (AffineExpr 3 (3x+y), LessEquals)
-- 
type Constraint = (AffineExpr, ConstraintRelation) 

{-|
  Remove variables with zero coefficient.
  TODO: ensure that constraints are always normalized.
-}
normalize :: Constraint -> Constraint
normalize (AffineExpr constant expr, rel) = 
  (AffineExpr constant $ M.filter (/= 0) expr, rel)


-- | Map from variable IDs to coefficients 
type LinearExpr = M.IntMap Rational

data AffineExpr = AffineExpr
  { getConstant :: Rational  
  , getCoeffMap :: LinearExpr }

instance Num AffineExpr where
  AffineExpr constA coeffsA + AffineExpr constB coeffsB = 
    AffineExpr (constA+constB) (M.unionWith (+) coeffsA coeffsB)
  (*) = error "AffineExpr not closed under multiplication"
  abs = error "TODO"
  signum = error "TODO"
  fromInteger n = AffineExpr (fromInteger n) M.empty
  negate (AffineExpr constant coeffs) = 
    AffineExpr (negate constant) (M.map negate coeffs)

-- | Construct `Equals` constraint.
(.==) :: AffineExpr -> AffineExpr -> Constraint
(.==) lhs_expr rhs_expr = (lhs_expr - rhs_expr, Equals)

-- | Construct `LessEquals` constraint.
(.<=) :: AffineExpr -> AffineExpr -> Constraint
(.<=) lhs_expr rhs_expr = (lhs_expr - rhs_expr, LessEquals)

-- | Construct `GreaterEquals` constraint.
(.>=) :: AffineExpr -> AffineExpr -> Constraint
(.>=) lhs_expr rhs_expr = (lhs_expr - rhs_expr, GreaterEquals)

-- | Construct `GreaterThan` constraint.
(.>) :: AffineExpr -> AffineExpr -> Constraint
(.>) lhs_expr rhs_expr = (lhs_expr - rhs_expr, GreaterThan)

-- | Construct `LessThan` constraint.
(.<) :: AffineExpr -> AffineExpr -> Constraint
(.<) lhs_expr rhs_expr = (lhs_expr - rhs_expr, LessThan)

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
        if coeff == 1 then
          "x" ++ show var
        else 
          show_signed coeff ++ "*x" ++ show var
        
      terms_showed :: [String]
      terms_showed = fmap show_var (M.toList coeff_map) ++ [ show_signed constant | constant /= 0 ]
     in 
      case terms_showed of
        [] -> "0"
        _  -> intercalate "+" terms_showed

varsIn :: Constraint -> S.IntSet
varsIn (AffineExpr _ coeff_map, _) = M.keysSet coeff_map

varsInAll :: [Constraint] -> S.IntSet
varsInAll = foldr (S.union . varsIn) S.empty

appearsIn :: Var -> Constraint -> Bool
appearsIn var = M.member var . getCoeffMap . fst

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
solveFor (AffineExpr constant coeffs, rel) x = do
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

substitute :: Assignment -> AffineExpr -> AffineExpr
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
eval :: Assignment -> AffineExpr -> Maybe Rational
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
isModel :: Assignment -> Constraint -> Bool
isModel assignment (affine_expr, rel) = 
  case (eval assignment affine_expr, rel) of 
    (Just value, LessThan     ) -> value <  0
    (Just value, LessEquals   ) -> value <= 0
    (Just value, Equals       ) -> value == 0
    (Just value, GreaterEquals) -> value >= 0
    (Just value, GreaterThan  ) -> value >  0
    (Nothing   , _            ) -> False

-- | True iff constraint contains no free variables
isGround :: Constraint -> Bool
isGround = M.null . getCoeffMap . fst 

-- | True iff constraint contains at least one free variable.
isOpen :: Constraint -> Bool
isOpen = not . isGround
