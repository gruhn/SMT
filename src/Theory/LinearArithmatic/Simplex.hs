{-|
  The Simplex method is sound, complete, and in pratice efficient for finding solutions
  to sets of linear constraints. All coefficients, bounds, and solutions are of type 
  `Rational` to avoid having to deal with numeric issues at the cost of performance.
-}
module Theory.LinearArithmatic.Simplex 
  ( simplex
  , simplexSteps
  , initTableau
  , Tableau(..)
  , isBoundViolated
  , BoundType(..)
  , isSatisfied
  ) where

import Control.Monad (guard)
import Data.Bifunctor (bimap)
import qualified Data.IntMap.Strict as M
import qualified Data.IntMap.Merge.Strict as MM
import qualified Data.IntSet as S
import Data.Maybe (fromMaybe, mapMaybe, isJust)
import Theory.LinearArithmatic.Constraint
import Debug.Trace
import Data.Foldable (find)
import Data.List (intercalate)
import Data.Ratio (numerator, denominator)

data BoundType = UpperBound | LowerBound
  deriving (Show, Eq)

data Tableau = Tableau
  { getBasis :: M.IntMap LinearExpr
  , getBounds :: M.IntMap (BoundType, Rational)
  , getAssignment :: Assignment
  }

instance Show Tableau where
  show (Tableau basis bounds assignment) = 
    let
      show_row (var, linear_expr) =
        "x" ++ show var ++ " = " ++ show (AffineExpr 0 linear_expr)

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

      show_bound (Just (UpperBound, bound_value)) = 
        " <= " ++ show_signed bound_value
      show_bound (Just (LowerBound, bound_value)) = 
        " >= " ++ show_signed bound_value
      show_bound Nothing = ""

      show_value (var, value) = 
           "x" 
        ++ show var 
        ++ ": " 
        ++ show_signed value
        ++ show_bound (M.lookup var bounds)
    in 
      intercalate "\n"
        $  "----------------"
        :  (show_row <$> M.toList basis)
        ++ ""
        :  (show_value <$> M.toList assignment)

{-|
  Transform constraints to "General From" and initialize Simplex tableau.
-}
initTableau :: [Constraint] -> Maybe Tableau
initTableau constraints =
  let 
    fresh_vars = 
      case S.maxView $ varsInAll constraints of
        Nothing           -> [0 ..]
        Just (max_var, _) -> [max_var + 1 ..]

    (basis, bounds) = bimap M.fromList M.fromList $ unzip $ do
      (slack_var, (affine_expr, relation)) <- zip fresh_vars constraints

      let bound_type =
            case relation of
              LessEquals    -> UpperBound
              GreaterEquals -> LowerBound
              other_rels    -> error "TODO: extend Simplex to all constraint relations"

      return
        ( (slack_var, getCoeffMap affine_expr)
        , (slack_var, (bound_type, - getConstant affine_expr))
        )

    original_vars = varsInAll constraints
    slack_vars = M.keys bounds

    assignment :: Assignment
    assignment =
      M.fromList $
        zip (S.toList original_vars ++ slack_vars) $
          repeat 0
   in 
    eliminateZeroRows $ Tableau basis bounds assignment

data BoundViolation = MustIncrease | MustDecrease

boundViolation :: Tableau -> Var -> Maybe BoundViolation
boundViolation (Tableau basis bounds assignment) var = do
  let current_value = assignment M.! var
  bound <- M.lookup var bounds
  case bound of 
    (UpperBound, bound_value) ->
      if current_value <= bound_value then
        Nothing
      else 
        Just MustDecrease
    (LowerBound, bound_value) -> do
      if bound_value <= current_value then
        Nothing
      else
        Just MustIncrease

isBoundViolated :: Tableau -> Var -> Bool
isBoundViolated tableau var = isJust $ boundViolation tableau var

violatedBasicVars :: Tableau -> [(Var, BoundViolation)]
violatedBasicVars tableau = do
  basic_var <- M.keys $ getBasis tableau
  case boundViolation tableau basic_var of
    Nothing -> []
    Just violation -> [ (basic_var, violation) ]

pivotCandidates :: Tableau -> [(Var, Var)]
pivotCandidates tableau@(Tableau basis bounds assignment) = do
  -- Following "Bland's Rule" by enumerating variables in ascending order.
  -- Only consider the first violated basic variable. 
  (basic_var, violation) <- take 1 $ violatedBasicVars tableau

  let expr = basis M.! basic_var
      non_basis = M.keysSet assignment S.\\ M.keysSet basis

  non_basic_var <- S.toAscList non_basis

  let non_basic_var_coeff = M.findWithDefault 0 non_basic_var expr
      non_basic_var_current_value = assignment M.! non_basic_var

      non_basic_var_lower_bound = do
        (bound_type, bound_value) <- M.lookup non_basic_var bounds
        guard $ bound_type == LowerBound
        return bound_value

      non_basic_var_upper_bound = do
        (bound_type, bound_value) <- M.lookup non_basic_var bounds
        guard $ bound_type == UpperBound
        return bound_value

      can_pivot =
        case (signum non_basic_var_coeff, violation) of
          -- If the coefficient of the non basic variable is 0, then the value of the variable
          -- is not affected by pivoting, so it can't resolve the bound violation.
          (0, _) -> False

          -- The value of the basic variable must be decreased. The coefficient of the non-basic
          -- variable is positive, so we need to decrease it's value. This is only possible if 
          -- non-basic variable is above it's lower bound (or has none).
          (1, MustDecrease) -> 
            case non_basic_var_lower_bound of
              Nothing -> True
              Just lower_bound -> lower_bound < non_basic_var_current_value

          -- The value of the basic variable must be increased. The coefficient of the non-basic
          -- variable is negative, so we need to decrease it's value. This is only possible if 
          -- non-basic variable is above it's lower bound (or has none).
          (-1, MustIncrease) ->
            case non_basic_var_lower_bound of
              Nothing          -> True
              Just lower_bound -> lower_bound < non_basic_var_current_value

          -- The value of the basic variable must be increased. The coefficient of the non-basic
          -- variable is positive, so we need to increase it's value. This is only possible if 
          -- non-basic variable is below it's upper bound (or has none).
          (1, MustIncrease) ->
            case non_basic_var_upper_bound of
              Nothing          -> True
              Just upper_bound -> upper_bound > non_basic_var_current_value

          -- The value of the basic variable must be decreased. The coefficient of the non-basic
          -- variable is negative, so we need to increase it's value. This is only possible if 
          -- non-basic variable is below it's upper bound (or has none).          
          (-1, MustDecrease) ->
            case non_basic_var_upper_bound of
              Nothing          -> True
              Just upper_bound -> upper_bound > non_basic_var_current_value

          -- In all other cases the bound of the non-basic variable would be violated by pivoting.
          all_other_cases -> False

  guard can_pivot
  return (basic_var, non_basic_var)

type Equation = (Var, LinearExpr)

{-|
  Given two equations, such as

    e1: x = w + 2z
    e2: y = 3x + 4z

  rewrite x in e2 using e1:

    y = 3(w + 2z) + 4z
      = 3w + 10z
-}
rewrite :: Equation -> Equation -> Equation
rewrite (x, expr_x) (y, expr_y) =
  let coeff_of_x = M.findWithDefault 0 x expr_y
      expr_x' = M.map (* coeff_of_x) expr_x
      expr_y' = M.unionWith (+) (M.delete x expr_y) expr_x'
   in (y, expr_y')

{-|
  Specialization of `solveFor` for linear equations, instead of affine constraints, i.e. 
  no constant terms and no inequalities.
-}
solveFor' :: Equation -> Var -> Maybe Equation
solveFor' (x, expr_x) y = do
  let constraint = (AffineExpr 0 $ M.insert x (-1) expr_x, Equals)
  (_, _, AffineExpr _ expr_y) <- solveFor constraint y
  return (y, expr_y)

{-|
  TODO: make sure:

    - only slack variables are pivoted
    - non-basic variables must violate bound
    - basic variable is suitable for pivoting
-}
pivot :: Var -> Var -> Tableau -> Tableau
pivot basic_var non_basic_var (Tableau basis bounds assignment) =
  let 
    from_just msg (Just a) = a
    from_just msg Nothing = error msg

    expr =
      from_just "Given variable is not actually in the basis ==> invalid pivot pair" $
        M.lookup basic_var basis

    (_, expr') =
      from_just "Can't solve for non-basic variable ==> invalid pivot pair" $
        solveFor' (basic_var, expr) non_basic_var

    basis' =
        M.insert non_basic_var expr'
      $ M.mapWithKey (\y expr_y -> snd $ rewrite (non_basic_var, expr') (y, expr_y))
      $ M.delete basic_var basis

    old_value_basic_var = assignment M.! basic_var
    new_value_basic_var =
      from_just "Basic variable doesn't have a bound so it's not actually violated" $
        snd <$> M.lookup basic_var bounds

    non_basic_var_coeff = expr M.! non_basic_var

    old_value_non_basic_var = assignment M.! non_basic_var
    new_value_non_basic_var = old_value_non_basic_var + (old_value_basic_var - new_value_basic_var) / non_basic_var_coeff

    assignment' =
        M.insert non_basic_var new_value_non_basic_var 
      $ M.insert basic_var new_value_basic_var assignment

    assignment'' = 
      M.union 
        ( from_just "Can't evaluate expression, because assignment is partial" 
            $ traverse (eval assignment' . AffineExpr 0) basis' )
        assignment' 
   in 
    Tableau basis' bounds assignment''

{-| 
  Tableau rows with only zero entries correspond to constant constraints 
  like 0 < 1. These rows can be ignored during simplex. Also, if the 
  bound of the corresponding slack variable is violated, then there is
  a constant constraint that is unsatisfiable, such as 1 < 0, and we can
  immediately terminate.
-}
eliminateZeroRows :: Tableau -> Maybe Tableau
eliminateZeroRows tableau@(Tableau basis bounds assignment)
  | any (isBoundViolated tableau) (S.toList zero_row_slack_vars) = Nothing
  | otherwise = Just tableau'
  where
    (zero_rows, basis') = M.partition (all (== 0)) basis
    zero_row_slack_vars = M.keysSet zero_rows
    tableau' =  Tableau
      basis' 
      (bounds `M.withoutKeys` zero_row_slack_vars)
      (assignment `M.withoutKeys` zero_row_slack_vars)

isSatisfied :: Tableau -> Bool
isSatisfied = null . violatedBasicVars

simplexSteps :: Tableau -> [Tableau]
simplexSteps tableau = 
  case pivotCandidates tableau of
    [] -> [tableau]
    ((basic_var, non_basic_var) : _) ->
      tableau : simplexSteps (pivot basic_var non_basic_var tableau)

{-|
  TODO:
    in case of UNSAT include explanation, i.e. minimal infeasible subset of constraints.
-}
simplex :: [Constraint] -> Maybe Assignment
simplex constraints = do
  tableau_0 <- initTableau constraints
  let tableau_n = last $ simplexSteps tableau_0
  guard $ isSatisfied tableau_n

  let original_vars = varsInAll constraints
      assignment = M.restrictKeys (getAssignment tableau_n) original_vars

  return assignment