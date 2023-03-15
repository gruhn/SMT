{-# LANGUAGE TupleSections #-}
module Theory.LinearArithmatic.Simplex () where

import qualified Data.IntMap as M
import qualified Data.IntMap.Merge.Lazy as MM
import qualified Data.IntSet as S
import Control.Monad (unless, guard)

type Var = Int

-- | Map from variable IDs to assigned values
type Assignment a = M.IntMap a

-- | Map from variable IDs to coefficients
type LinearTerm a = M.IntMap a

data BoundType = UpperBound | LowerBound

data Tableau a = Tableau
  { getNonBasis :: M.IntMap (LinearTerm a)
  , getBounds :: M.IntMap (BoundType, a)
  , getAssignment :: Assignment a
  }

data BoundViolation = MustIncrease | MustDecrease

type Equation a = (Var, LinearTerm a)

{-|
  Solve an equation for a given variable. For example solving

    y = 3x + 10  

  for x, yields
    
    x = 1/3 y - 10/3

-}
solveFor :: Equation a -> Var -> Maybe (Equation a)
solveFor (y, right_hand_side) x = do
  coeff_of_x <- M.lookup x right_hand_side
  guard (coeff_of_x /= 0)
  return $ (x,)
    -- divide by coefficient: x = -1/3y - 10/3
    $ M.map (/ (-coeff_of_x))
    -- exchange x and y: -3x = -y + 10
    $ M.insert y (-1)
    $ M.delete x right_hand_side

{-|
  Given two equations, such as

    e1: x = w + 2z
    e2: y = 3x + 4z

  rewrite x in e2 using e1:
  
    y = 3(w + 2z) + 4z
      = 3w + 10z
-}
rewrite :: Equation a -> Equation a -> Equation a
rewrite (x, term_x) (y, term_y) =
  let
    coeff_of_x = M.findWithDefault 0 x term_y
    term_x' = M.map (* coeff_of_x) term_x
    term_y' = M.unionWith (+) (M.delete x term_y) term_x'
  in
    (y, term_y')

eval :: Assignment a -> LinearTerm a -> a
eval assignment term = sum . MM.zipWithMatched (const (*)) assignment term

{-|
  TODO: make sure:

    - only slack variables are pivoted
    - non-basic variables must violate bound
    - basic variable is suitable for pivoting
-}
pivot' :: Var -> Var -> Tableau a -> Tableau a
pivot' basic_var non_basic_var (Tableau non_basis bounds assignment) =
  let 
    from_just msg (Just a) = a
    from_just msg Nothing = error msg

    term = from_just "Given variable is not actually in the non-basis ==> invalid pivot pair" 
      $ M.lookup non_basic_var non_basis 

    equation = from_just "Can't solve for basic variable ==> invalid pivot pair"
      $ solveFor (non_basic_var, term) basic_var

    non_basis' = M.fromList $ rewrite equation <$> M.toList non_basis

    old_value_basic_var = assignment M.! basic_var
    new_value_basic_var = from_just "Basic variable doesn't have a bound so it's not actually violated"
      $ snd <$> M.lookup basic_var bounds

    basic_var_coeff = snd equation M.! basic_var

    old_value_non_basic_var = non_basis M.! non_basic_bar
    new_value_non_basic_var = old_value_non_basic_var + (old_value_basic_bar - new_value_basic_var) / basic_var_coeff

    assignment' = M.union (eval <$> non_basis')
      $ M.insert non_basic_var new_value_non_basic_var
      $ M.insert basic_var new_value_basic_var assignment
  in
    Tableau non_basis' bounds assignment'

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
      (non_basic_var, term) <- M.toAscList non_basis

      let basic_var_coeff = M.findWithDefault 0 basic_var term
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

              -- In all other cases the bound of the non-basic variable would be violated by 
              -- pivoting.
              all_other_cases -> False

      guard can_pivot
      return (basic_var, non_basic_var)

  in undefined

