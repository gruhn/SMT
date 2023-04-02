{-| 
  Fourier-Motzkin is a sound and complete method for solving linear
  constraints. The method is simpler but less efficient then Simplex. 
  We use it only for testing the Simplex implementation.
-}
module Theory.LinearArithmatic.FourierMotzkin (fourierMotzkin) where

import Theory.LinearArithmatic.Constraint
import qualified Data.IntMap.Strict as M
import qualified Data.IntSet as S
import Control.Monad (guard)
import qualified Data.Vector as V
import Data.Maybe (fromMaybe, mapMaybe, maybeToList, listToMaybe, fromJust)
import Data.List (partition)
import Debug.Trace
import Control.Arrow (Arrow (first))
import Control.Exception (assert)
import Data.Either (partitionEithers)
import Data.Foldable (asum)
import Control.Applicative ((<|>))
import Utils (fixpoint)

partitionByBound :: [Constraint] -> Var -> ([Constraint], [Constraint], [Constraint])
partitionByBound constraints var = 
  let
    go :: Constraint -> ([Constraint], [Constraint], [Constraint])
    go constraint = 
      case constraint `solveFor` var of
        Nothing -> -- constraint does not include var
          ([], [], [constraint])
        Just c@(expr, GreaterEquals) -> -- lower bound
          ([c], [], [])
        Just c@(expr, LessEquals) -> -- upper bound
          ([], [c], [])
        Just (expr, not_supported_yet) -> 
          error "TODO: support all constraint types in Fourier Motzkin"

    combine (as1, as2, as3) (bs1, bs2, bs3) =
      (as1 ++ bs1, as2 ++ bs2, as3 ++ bs3)
  in
    foldr combine ([], [], []) $ go <$> constraints

{-|
  Identifies a variable that has both upper- and lower bounds, if one exists, as in

    x <= 2y - 1      (upper bound)
    3 <= x           (lower bound)

  Then constructs new constraints, where the variable is eliminated, by pairing 
  each upper- with each lower bound: 

    3 <= x <= 2y - 1      ==>     3 <= 2y - 1

  and rearranging to make right-hand-side zero.

    -2y + 2 <= 0    

-}
eliminate :: [Constraint] -> Maybe (Var, [Constraint])
eliminate constraints = listToMaybe $ do
  var <- S.toList $ S.unions $ varsIn <$> constraints

  let (lower_bounds, upper_bounds, constraints_without_var) = 
        partitionByBound constraints var

  guard $ not (null lower_bounds) && not (null upper_bounds)

  let constraints_with_var_eliminated :: [Constraint]
      constraints_with_var_eliminated = do
        AffineExpr ub_const ub_coeffs <- fst <$> upper_bounds
        AffineExpr lb_const lb_coeffs <- fst <$> lower_bounds
        let left_hand_side = AffineExpr (lb_const - ub_const) (M.unionWith (+) lb_coeffs $ negate <$> ub_coeffs)
        return (left_hand_side, LessEquals)

  return (var, constraints_without_var ++ constraints_with_var_eliminated)

fourierMotzkin :: [Constraint] -> Maybe Assignment
fourierMotzkin = go . fmap normalize
  where
    go :: [Constraint] -> Maybe Assignment
    go constraints = do
      let (constraints_no_vars, constraints_with_vars) = 
            partition (S.null . varsIn) constraints

      -- otherwise `constraints_no_vars` contains a constraint like 1 <= 0
      guard $ all (M.empty `isModel`) constraints_no_vars

      if null constraints_with_vars then
        Just M.empty
      else 
        case eliminate constraints_with_vars of
          Nothing -> do
            let unassigned_vars = S.unions $ varsIn <$> constraints_with_vars
                initial_assignment = M.fromSet (const 0) unassigned_vars 
            return $ fixpoint (`refine` constraints_with_vars) initial_assignment

          Just (next_var, constraints_without_var) -> do
            partial_assignment <- go constraints_without_var
            let constraints' = first (substitute partial_assignment) <$> constraints_with_vars
            return $ refine (M.insert next_var 0 partial_assignment) constraints'

    refine_with :: Constraint -> Var -> Assignment -> Assignment
    refine_with (expr, rel) var assignment = 
      let 
        current_value = assignment M.! var
        assignment' = M.delete var assignment 
      in
        case (substitute assignment' expr, rel) `solveFor` var of
          Nothing -> assignment
          Just (AffineExpr new_value _, LessEquals) -> 
            if new_value < current_value then
              M.insert var new_value assignment
            else
              assignment
          Just (AffineExpr new_value _, GreaterEquals) -> 
            if new_value > current_value then
              M.insert var new_value assignment
            else
              assignment

    refine :: Assignment -> [Constraint] -> Assignment
    refine = foldr accum
      where
        accum :: Constraint -> Assignment -> Assignment
        accum constraint assignment = 
          foldr (refine_with constraint) assignment (S.toList $ varsIn constraint)    

---------------------------

example1 =
  [ (AffineExpr 0 $ M.fromList [ (0, -1), (1, -1) ], LessEquals)
  , (AffineExpr 1 $ M.fromList [ (0, 1) ], LessEquals) ]

example2 = 
  [ (AffineExpr 0 $ M.singleton 0 (-1), LessEquals)
  , (AffineExpr 1 $ M.singleton 0 1, LessEquals) ]
