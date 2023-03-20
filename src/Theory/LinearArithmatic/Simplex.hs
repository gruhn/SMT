module Theory.LinearArithmatic.Simplex ( simplex, Assignment, Constraint, ConstraintRelation(..), eval ) where

import qualified Data.IntMap as M
import qualified Data.IntMap.Merge.Lazy as MM
import qualified Data.IntSet as S
import Control.Monad (unless, guard)
import Data.Bifunctor (bimap)
import Data.Maybe (fromMaybe)

type Var = Int

data ConstraintRelation = LessThan | LessEquals | Equals | GreaterEquals | GreaterThan
  deriving Show

{-| 
  For example, constraint such as `3x + y <= 3` is represented as:

     (3x+y, LessEquals, 3)

-}
type Constraint a = (LinearTerm a, ConstraintRelation, a)

-- | Map from variable IDs to assigned values
type Assignment a = M.IntMap a

-- | Map from variable IDs to coefficients
type LinearTerm a = M.IntMap a

data BoundType = UpperBound | LowerBound
  deriving Show

data Tableau a = Tableau
  { getBasis :: M.IntMap (LinearTerm a)
  , getBounds :: M.IntMap (BoundType, a)
  , getAssignment :: Assignment a
  } deriving Show

varsIn :: [Constraint a] -> S.IntSet
varsIn constraints = S.unions $ do
  (linear_term, _, _) <- constraints
  return $ M.keysSet linear_term

{-|  
  Transform constraints to "General From" and initialize Simplex tableau.

-}
initTableau :: forall a. Num a => [Constraint a] -> Tableau a
initTableau constraints = 
  let 
    original_vars = varsIn constraints
    max_original_var = if S.null original_vars then -1 else S.findMax original_vars
    fresh_vars = [max_original_var+1 ..]

    (basis, bounds) = bimap M.fromList M.fromList $ unzip $ do 
      (slack_var, (linear_term, relation, bound)) <- zip fresh_vars constraints

      let bound_type = 
            case relation of
              LessEquals    -> UpperBound
              GreaterEquals -> LowerBound
              other_rels -> error "TODO: extend Simplex to all constraint relations"
      
      return 
        ( (slack_var, linear_term)
        , (slack_var, (bound_type, bound)))

    slack_vars = M.keys bounds

    assignment :: Assignment a
    assignment = M.fromList 
      $ zip (S.toList original_vars ++ slack_vars) 
      $ repeat 0

  in 
    Tableau basis bounds assignment

data BoundViolation = MustIncrease | MustDecrease

violatedBasicVars :: Ord a => Tableau a ->  [ (Var, BoundViolation) ]
violatedBasicVars (Tableau basis bounds assignment) = do
  -- Following "Blend's Rule" by enumerating variables in ascending order.
  basic_var <- M.keys basis

  let current_value = assignment M.! basic_var

  case M.lookup basic_var bounds of
    Just (UpperBound, bound) -> do
      guard (current_value > bound)
      return (basic_var, MustDecrease)
    Just (LowerBound, bound) -> do
      guard (current_value < bound)
      return (basic_var, MustIncrease)
    Nothing -> []

pivotCandidates :: (Ord a, Num a) => Tableau a ->  [ (Var, Var) ]
pivotCandidates tableau@(Tableau basis bounds assignment) = do
  (basic_var, violation) <- violatedBasicVars tableau

  let term = basis M.! basic_var
      non_basis = M.keysSet assignment S.\\ M.keysSet basis

  non_basic_var <- S.toAscList non_basis

  let non_basic_var_coeff = M.findWithDefault 0 non_basic_var term
      non_basic_bound_type = fst <$> M.lookup non_basic_var bounds
      can_pivot =
        case (non_basic_bound_type, signum non_basic_var_coeff, violation) of
          -- If the coefficient of the non basic variable is 0, then the value of the variable 
          -- is not affected by pivoting, so it can't resolve the bound violation.
          (_, 0, _) -> False

          -- If the non-basic variable is not bounded and it's coefficient is non-zero, 
          -- then pivot is always possible. 
          (Nothing,  1, _) -> True
          (Nothing, -1, _) -> True

          -- The value of the basic variable must be decreased. The coefficient of the non-basic
          -- variable is positive, so we need to decrease it's value. The non-basic variable is 
          -- at it's upper bound so decreasing it is possible.
          (Just UpperBound, 1, MustDecrease) -> True

          -- The value of the basic variable must be increased. The coefficient of the non-basic
          -- variable is negative, so we need to decrease it's value. The non-basic variable is 
          -- at it's upper bound so decreasing it is possible.
          (Just UpperBound, -1, MustIncrease) -> True

          -- The value of the basic variable must be increased. The coefficient of the non-basic
          -- variable is positive, so we need to increase it's value. The non-basic variable is 
          -- at it's lower bound so increasing it is possible.
          (Just LowerBound, 1, MustIncrease) -> True

          -- The value of the basic variable must be decreased. The coefficient of the non-basic
          -- variable is negative, so we need to increase it's value. The non-basic variable is 
          -- at it's lower bound so increasing it is possible.
          (Just LowerBound, -1, MustDecrease) -> True

          -- In all other cases the bound of the non-basic variable would be violated by pivoting.
          all_other_cases -> False

  guard can_pivot
  return (basic_var, non_basic_var)

type Equation a = (Var, LinearTerm a)

{-|
  Solve an equation for a given variable. For example solving

    y = 3x + 10  

  for x, yields
    
    x = 1/3 y - 10/3

-}
solveFor :: (Fractional a, Eq a) => Equation a -> Var -> Maybe (Equation a)
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
rewrite :: Num a => Equation a -> Equation a -> Equation a
rewrite (x, term_x) (y, term_y) =
  let
    coeff_of_x = M.findWithDefault 0 x term_y
    term_x' = M.map (* coeff_of_x) term_x
    term_y' = M.unionWith (+) (M.delete x term_y) term_x'
  in
    (y, term_y')

eval :: Num a => Assignment a -> LinearTerm a -> a
eval assignment term = sum $ 
  MM.merge 
    MM.dropMissing 
    MM.dropMissing 
    (MM.zipWithMatched (const (*))) 
    assignment 
    term

{-|
  TODO: make sure:

    - only slack variables are pivoted
    - non-basic variables must violate bound
    - basic variable is suitable for pivoting
-}
pivot :: (Fractional a, Eq a) => Var -> Var -> Tableau a -> Tableau a
pivot basic_var non_basic_var (Tableau basis bounds assignment) =
  let 
    from_just msg (Just a) = a
    from_just msg Nothing = error msg

    term = from_just "Given variable is not actually in the basis ==> invalid pivot pair" 
      $ M.lookup basic_var basis

    equation = from_just "Can't solve for non-basic variable ==> invalid pivot pair"
      $ solveFor (basic_var, term) non_basic_var

    basis' = M.fromList $ rewrite equation <$> M.toList basis

    old_value_basic_var = assignment M.! basic_var
    new_value_basic_var = from_just "Basic variable doesn't have a bound so it's not actually violated"
      $ snd <$> M.lookup basic_var bounds

    non_basic_var_coeff = term M.! non_basic_var

    old_value_non_basic_var = assignment M.! non_basic_var
    new_value_non_basic_var = old_value_non_basic_var + (old_value_basic_var - new_value_basic_var) / non_basic_var_coeff

    assignment' = 
        M.insert non_basic_var new_value_non_basic_var
      $ M.insert basic_var new_value_basic_var assignment

    assignment'' = M.union (eval assignment' <$> basis') assignment'
  in
    Tableau basis' bounds assignment''

{-| 
  TODO: 
    in case of UNSAT include explanation, i.e. minimal infeasible subset of constraints.
-}
simplex :: forall a. (Num a, Ord a, Fractional a) => [Constraint a] -> Maybe (Assignment a)
simplex constraints =
  let
    go :: Tableau a -> Tableau a
    go tableau = 
      case pivotCandidates $ tableau of 
        [] -> tableau
        ((basic_var, non_basic_var) : _) ->
          go (pivot basic_var non_basic_var tableau)

    tableau_0 = initTableau constraints
    tableau_n = go tableau_0

    original_vars = varsIn constraints
    assignment = M.restrictKeys (getAssignment tableau_n) original_vars
  in
    if null (violatedBasicVars tableau_n) then 
      Just assignment
    else
      Nothing

-----------------------------------------------------------

example1 = simplex 
  [ (M.fromList [(0,1), (1,1)], LessEquals, 3)   
  , (M.fromList [(0,1), (1,1)], GreaterEquals, 1)  
  , (M.fromList [(0,1), (1,-1)], LessEquals, 3) 
  , (M.fromList [(0,1), (1,-1)], GreaterEquals, 1)
  -- , (M.fromList [(0,1), (1,-1)], LessEquals, -1)
  ]
    
example2 = simplex 
  [ (M.fromList [(0,1), (1,1)], GreaterEquals, 2) ]
    
