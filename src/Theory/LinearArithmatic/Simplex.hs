{-|
  The Simplex method is sound, complete, and in pratice efficient for finding solutions
  to sets of linear constraints. All coefficients, bounds, and solutions are of type 
  `Rational` to avoid having to deal with numeric issues at the cost of performance.
-}
module Theory.LinearArithmatic.Simplex 
  ( simplex
  , steps
  , initTableau
  -- WARN: don't expose the Tableau type constructor to protect all the delicate invariants:
  , Tableau(getBasis, getBounds, getAssignment, getMaxOriginalVar, getMaxVar)
  , isBoundViolated
  , BoundType(..)
  , isSatisfied
  , addConstraint
  , addTableauRow
  ) where

import Control.Monad (guard)
import Data.Bifunctor (bimap)
import qualified Data.IntMap.Strict as M
import qualified Data.IntMap.Merge.Strict as MM
import qualified Data.IntSet as S
import Data.Maybe (fromMaybe, mapMaybe, isJust, fromJust)
import Theory.LinearArithmatic.Constraint
import Debug.Trace
import Data.Foldable (find, foldl')
import Data.List (intercalate, partition, sort, sortOn)
import Data.Ratio (numerator, denominator)
import Data.Function ((&))
import Control.Exception (assert)

data BoundType = UpperBound | LowerBound
  deriving (Show, Eq)

data Tableau = Tableau
  { getBasis          :: M.IntMap LinearExpr
  , getBounds         :: M.IntMap (BoundType, Rational)
  , getAssignment     :: Assignment
  , getMaxOriginalVar :: Var
  , getMaxVar         :: Var
  }

{-| 
  Every variable (slack or original / basic or non-basic) has an assigned value, 
  so we can obtain the set of all used variables from the key set of the assignment map.
-}
allVars :: Tableau -> S.IntSet
allVars = M.keysSet . getAssignment

basicVars :: Tableau -> S.IntSet
basicVars = M.keysSet . getBasis

nonBasicVars :: Tableau -> S.IntSet
nonBasicVars tableau = allVars tableau S.\\ basicVars tableau

instance Show Tableau where
  show tableau = 
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
           (if isBoundViolated tableau var then " ✗ " else " ✓ ")
        ++ "x" ++ show var 
        ++ ": " 
        ++ show_signed value
        ++ show_bound (M.lookup var (getBounds tableau))
    in 
      intercalate "\n"
        $  ["------ Simplex Tableau ----------"]
        ++ (show_row <$> M.toList (getBasis tableau))
        ++ [""]
        ++ ["bounds: "]
        ++ (show_value <$> M.toList (getAssignment tableau))
        ++ ["---------------------------------"]

{-|
  Add a constraint to a Tableau. Either during setup of an initial 
  Tableau or to add cutting planes to a Tableau after a few Simplex steps.
  Also used in Branch-and-Bound to add integrality constraints.

  WARN: All referenced variables must already be in the Tableau. 
        Otherwise this throws an error. 
-}
addConstraint :: Constraint -> Tableau -> Tableau
addConstraint (affine_expr, relation) tableau =
  case relation of
    LessEquals -> 
      addTableauRow affine_expr UpperBound tableau
    GreaterEquals -> 
      addTableauRow affine_expr LowerBound tableau
    Equals -> 
      addTableauRow affine_expr UpperBound $ addTableauRow affine_expr LowerBound tableau
    LessThan -> 
      error "TODO: LessThan constraints not supported in Simplex"
    GreaterThan -> 
      error "TODO: GreaterThan constraints not supported in Simplex"

{-| 
  Checks that a set of variables is only composed of original variables
  with respect to a tableau. That is: 
  
  (1) It contains no slack variables (with negative index). Is necessary 
      because when dynamic constraints (aka. cutting planes) are added to a 
      tableau after initialization, then we need to generate fresh slack 
      variables. By following the convention that slack variables have negative
      index and original variables a have non-negative index, fresh slack variables
      can be created by decrementing the smallest used slack variable. 
      However, we have to make sure that added cutting planes don't already 
      contain negative index variables to enforce this invariant.

  (2) It only contains variables that are already in the tableau. If 
      cutting planes introduce previously unused variables we would also
      generate columns (instead of just rows). Maybe that's not a problem.
      (TODO: investigate)
-}
assertOnlyOriginalVars :: Tableau -> S.IntSet -> S.IntSet
assertOnlyOriginalVars tableau vars = 
  let
    no_slack_vars = all (<= getMaxOriginalVar tableau) $ S.toList vars
    only_known_vars = vars `S.isSubsetOf` M.keysSet (getAssignment tableau)
  in
    if no_slack_vars && only_known_vars then
      vars
    else
      error "Simplex: expected only original"

{-|
  Add a constraint to a Tableau. Either during setup of an initial 
  Tableau or to add cutting planes to a Tableau after a few Simplex steps.
  Also used in Branch-and-Bound to add integrality constraints.

  WARN: All referenced variables must already be in the Tableau. 
        Otherwise this throws an error. 

  FIXME: Make sure no zero rows are added (@see `eliminateZeroRows`)
-}
addTableauRow :: AffineExpr -> BoundType -> Tableau -> Tableau
addTableauRow affine_expr bound_type tableau =
  let
    -- | Set of all original- variables that are referenced anywhere in the constraint expression.
    --   This set can't contain slack variables, since 
    affine_expr_vars :: S.IntSet
    affine_expr_vars = assertOnlyOriginalVars tableau $ M.keysSet $ getCoeffMap affine_expr

    -- | Each constraint has an associated slack variable, so we need a fresh variable.
    fresh_slack_var :: Var
    fresh_slack_var = getMaxVar tableau + 1

    -- | TODO explain
    substitute_basic_var :: Var -> Equation -> Equation
    substitute_basic_var var equation = 
      case M.lookup var (getBasis tableau) of
        Just expr -> rewrite (var, expr) equation
        Nothing   -> equation

    -- | We can't use the given `affine_expr` as-is to construct a new tableau row,
    -- because it might contain basic variables, and tableau "cells" may only contain
    -- non-basic variables. So we need to substitute every basic variable with non-basic 
    -- variables:
    new_tableau_row :: Equation
    new_tableau_row = 
      S.fold 
        substitute_basic_var 
        (fresh_slack_var, getCoeffMap affine_expr) 
        affine_expr_vars

    fresh_slack_var_value :: Rational
    fresh_slack_var_value = 
      fromMaybe (error "Simplex: got partial assignment")
        $ eval (getAssignment tableau) (AffineExpr 0 (snd new_tableau_row))
  in
    tableau 
      { getBasis = M.insert fresh_slack_var (snd new_tableau_row) (getBasis tableau)
      , getBounds = M.insert fresh_slack_var (bound_type, -getConstant affine_expr) (getBounds tableau)
      , getAssignment = M.insert fresh_slack_var fresh_slack_var_value (getAssignment tableau)
      , getMaxVar = fresh_slack_var
      }

{-|
  Transform constraints to "General From" and initialize Simplex tableau.
-}
initTableau :: [Constraint] -> Maybe Tableau
initTableau constraints = 
  let 
    original_vars :: S.IntSet
    original_vars = varsInAll constraints

    max_original_var :: Var
    max_original_var 
      | S.null original_vars = -1
      | otherwise = S.findMax original_vars

    tableau_0 :: Tableau
    tableau_0 = Tableau 
      { getBasis = M.empty 
      , getBounds = M.empty 
      , getAssignment = M.fromSet (const 0) original_vars
      , getMaxOriginalVar = max_original_var 
      , getMaxVar = max_original_var
      }
  in 
    eliminateZeroRows $ foldr addConstraint tableau_0 constraints

data BoundViolation = MustIncrease | MustDecrease

boundViolation :: Tableau -> Var -> Maybe BoundViolation
boundViolation tableau var = do
  let current_value = getAssignment tableau M.! var
  bound <- M.lookup var (getBounds tableau)
  case bound of 
    (UpperBound, bound_value) 
      | current_value <= bound_value -> Nothing
      | otherwise                    -> Just MustDecrease
    (LowerBound, bound_value)
      | bound_value <= current_value -> Nothing
      | otherwise                    -> Just MustIncrease

isBoundViolated :: Tableau -> Var -> Bool
isBoundViolated tableau var = isJust $ boundViolation tableau var

violatedBasicVars :: Tableau -> [(Var, BoundViolation)]
violatedBasicVars tableau = do
  -- toAscList because of "Bland's Rule"
  basic_var <- S.toAscList (basicVars tableau)
  case boundViolation tableau basic_var of
    Nothing -> []
    Just violation -> [ (basic_var, violation) ]

pivotCandidates :: Tableau -> [(Var, Var)]
pivotCandidates tableau = do
  -- Bland's Rule to prevent Simplex from getting into cycles: 
  --
  --   1. Determine a total order on the variables
  --   2. Choose the first basic variable that violates its bound,
  --      and the first non-basic suitable variable for pivoting.
  --   3. It can be shown that this guarantees that no base is repeated,
  --      which implies termination.  
  --
  -- Since we model variables as `Int` we just have to make sure to pick
  -- them in order (0 < 1 < 2 < ...):
  (basic_var, violation) <- take 1 $ violatedBasicVars tableau
  non_basic_var <- S.toAscList (nonBasicVars tableau)

  let expr = getBasis tableau M.! basic_var

      non_basic_var_coeff = M.findWithDefault 0 non_basic_var expr
      non_basic_var_current_value = getAssignment tableau M.! non_basic_var

      non_basic_var_lower_bound = do
        (bound_type, bound_value) <- M.lookup non_basic_var $ getBounds tableau
        guard $ bound_type == LowerBound
        return bound_value

      non_basic_var_upper_bound = do
        (bound_type, bound_value) <- M.lookup non_basic_var $ getBounds tableau
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
pivot basic_var non_basic_var tableau =
  let 
    from_just msg (Just a) = a
    from_just msg Nothing = error msg

    expr =
      from_just "Given variable is not actually in the basis ==> invalid pivot pair" $
        M.lookup basic_var (getBasis tableau)

    (_, expr') =
      from_just "Can't solve for non-basic variable ==> invalid pivot pair" $
        solveFor' (basic_var, expr) non_basic_var

    basis' =
        M.insert non_basic_var expr'
      $ M.mapWithKey (\y expr_y -> snd $ rewrite (non_basic_var, expr') (y, expr_y))
      $ M.delete basic_var 
      $ getBasis tableau

    old_value_basic_var = getAssignment tableau M.! basic_var

    new_value_basic_var =
      from_just "Basic variable doesn't have a bound so it's not actually violated" $
        snd <$> M.lookup basic_var (getBounds tableau)

    non_basic_var_coeff = expr M.! non_basic_var

    old_value_non_basic_var = getAssignment tableau M.! non_basic_var
    new_value_non_basic_var = old_value_non_basic_var + (old_value_basic_var - new_value_basic_var) / non_basic_var_coeff

    assignment' =
        M.insert non_basic_var new_value_non_basic_var 
      $ M.insert basic_var new_value_basic_var
      $ getAssignment tableau

    assignment'' = 
      M.union 
        ( from_just "Can't evaluate expression, because assignment is partial" 
            $ traverse (eval assignment' . AffineExpr 0) basis' )
        assignment' 
   in 
    tableau
      { getBasis = basis'
      , getAssignment = assignment''       
      }

{-| 
  Tableau rows with only zero entries correspond to constant constraints 
  like 0 < 1. These rows can be ignored during simplex. Also, if the 
  bound of the corresponding slack variable is violated, then there is
  a constant constraint that is unsatisfiable, such as 1 < 0, and we can
  immediately terminate.
-}
eliminateZeroRows :: Tableau -> Maybe Tableau
eliminateZeroRows tableau
  | any (isBoundViolated tableau) (S.toList zero_row_slack_vars) = Nothing
  | otherwise = Just tableau'
  where
    (zero_rows, basis') = M.partition (all (== 0)) (getBasis tableau)
    zero_row_slack_vars = M.keysSet zero_rows
    tableau' = tableau
      { getBasis = basis'
      , getBounds = getBounds tableau `M.withoutKeys` zero_row_slack_vars
      , getAssignment = getAssignment tableau`M.withoutKeys` zero_row_slack_vars
      }

isSatisfied :: Tableau -> Bool
isSatisfied = null . violatedBasicVars

steps :: Tableau -> [Tableau]
steps tableau = 
  case pivotCandidates tableau of
    [] -> [tableau]
    ((basic_var, non_basic_var) : _) ->
      tableau : steps (pivot basic_var non_basic_var tableau)

{-|
  TODO: in case of UNSAT include explanation, i.e. minimal infeasible subset of constraints.
-}
simplex :: [Constraint] -> Maybe Assignment
simplex constraints = do
  tableau_0 <- initTableau constraints
  let tableau_n = last $ steps tableau_0
  guard $ isSatisfied tableau_n

  let original_vars = varsInAll constraints
      assignment = M.restrictKeys (getAssignment tableau_n) original_vars

  return assignment
