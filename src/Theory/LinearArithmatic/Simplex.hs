module Theory.LinearArithmatic.Simplex () where

import qualified Data.IntMap as M
import qualified Data.IntSet as S
import qualified Control.Monad.State as State
import Control.Monad.State (State)
import Control.Monad (unless, guard)

type Var = Int

-- | Map from variable IDs to assigned values
type Assignment a = M.IntMap a

-- | Map from variable IDs to coefficients
type Constraint a = M.IntMap a

data BoundType = UpperBound | LowerBound

data Tableau a = Tableau
  { getNonBasis :: M.IntMap (Constraint a)
  , getBounds :: M.IntMap (BoundType, a)
  , getAssignment :: Assignment a
  }

data BoundViolation = MustIncrease | MustDecrease

pivot :: forall a. (Num a, Ord a) => Tableau a -> Tableau a
pivot (Tableau non_basis bounds assignment) = 
  let
    basis = M.keysSet assignment S.\\ M.keysSet non_basis

    violated_basic_vars :: [ (Var, BoundViolation) ]
    violated_basic_vars = do
      -- Following "Blend's Rule" by enumerating variables in ascending order.
      basic_var <- S.toAscList basis

      let current_value = assignment M.! basic_var

      case M.lookup basic_var bounds of
        Just (UpperBound bound) -> do
          guard (current_value > bound)
          return (basic_var, MustDecrease)
        Just (LowerBound bound) -> do
          guard (current_value < bound)
          return (basic_var, MustIncrease)
        Nothing -> []

    pivot_candidates :: [ (Var, Var) ]
    pivot_candidates = do
      (basic_var, violation) <- violated_basic_vars
      (non_basic_var, constraint) <- M.toAscList non_basis

      let basic_var_coeff = M.findWithDefault 0 basic_var constraint
          bound_type = fst <$> M.lookup non_basic_var bounds
          can_pivot = 
            case (bound_type, signum basic_var_coeff, violation) of
              -- If the coefficient of the basic variable is 0, then the value of the variable 
              -- is not affected by pivoting, so it can't resolve the bound violation.
              (_, 0, _) -> False

              -- If the coefficient of the basic variable is non-zero and the non-basic 
              -- variable is not bounded, pivot is always possible. 
              (Nothing,  1, _) -> True
              (Nothing, -1, _) -> True

              -- The non-basic variable is at it's upper bound so we can only decrease it, 
              -- without violating it. The value of the basic variable must be decreased, 
              -- and since the the coefficient is postive, decreasing it makes the non-basic
              -- variable value smaller.
              (Just UpperBound, 1, MustDecrease) -> True

              -- The non-basic variable is at it's upper bound so we can only decrease it, 
              -- without violating it. The value of the basic variable must be increased,
              -- but the coefficient is negative, so increasing it actually makes the non-basic
              -- variable value smaller.
              (Just UpperBound, -1, MustIncrease) -> True

              -- The non-basic variable is at it's lower bound so we can only increase it, 
              -- without violating it. The value of the basic variable must be increased,
              -- and since the the coefficient is postive, decreasing it makes the non-basic
              -- variable value larger.
              (Just LowerBound, 1, MustIncrease) -> True

              -- The non-basic variable is at it's lower bound so we can only increase it, 
              -- without violating it. The value of the basic variable must be decreased,
              -- but the coefficient is negative, so decreasing it actually makes the non-basic
              -- variable value larger.
              (Just LowerBound, -1, MustDecrease) -> True

              -- In all other cases the bound of the non-basic variable would be vioalted by 
              -- pivoting.
              all_other_cases -> False

      guard can_pivot
      return (basic_var, non_basic_var)

  in undefined

