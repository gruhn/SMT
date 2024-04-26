module TestLinearArithmatic
  ( prop_simplex_sound
  , prop_fourier_motzkin_sound
  , prop_fourier_motzkin_equiv_simplex
  , prop_simplex_no_cycle
  , prop_invariant_non_basic_vars_satisfy_bounds
  , prop_invariant_assignment_matches_basis_evaluation
  , prop_invariant_disjoint_basic_and_nonbasic_vars
  , prop_simplex_sound_with_cutting_plane
  , prop_branch_and_bound_sound
  , prop_branch_and_bound_terminates_quickly
  ) where

import Hedgehog hiding (Var, eval)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import qualified Theory.LinearArithmatic.Simplex as Simplex
import Theory.LinearArithmatic.Simplex (Tableau, simplex)
import qualified Data.IntMap as M
import qualified Data.IntSet as S
import qualified Data.Set as Set
import Theory.LinearArithmatic.Constraint
import Theory.LinearArithmatic.FourierMotzkin (fourierMotzkin)
import Data.Maybe (isJust, fromMaybe, mapMaybe)
import Data.Set (Set)
import Theory.LinearArithmatic.BranchAndBound ( branchAndBound, isIntegral )
import qualified Theory.LinearArithmatic.BranchAndBound as BranchAndBound
import Control.Monad (guard)
import Data.List (tails)

-- TODO: generate more representative constraint sets 
genConstraint :: [ConstraintRelation] -> Gen Var -> Gen Constraint
genConstraint relations gen_var = do
  linear_expr <- fmap M.fromList $ Gen.list (Range.linear 0 10) $ do
    coeff <- toRational <$> Gen.int (Range.linearFrom 0 (-10) 10)
    var <- gen_var
    return (var, coeff)

  rel <- Gen.element relations

  constant <- toRational <$> Gen.int (Range.linearFrom 0 (-10) 10)

  -- TODO: make sure that constraints are always normalized by construction.  
  return $ normalize (AffineExpr constant linear_expr, rel)

genConstraints ::[ConstraintRelation] -> Gen Var -> Range Int -> Gen [Constraint]
genConstraints relations gen_var range = Gen.list range (genConstraint relations gen_var)

prop_simplex_sound :: Property
prop_simplex_sound = withDiscards 300 $ property $ do
  constraints <- forAll $ genConstraints [LessEquals, GreaterEquals, Equals]
    (Gen.int $ Range.linear 0 20)
    (Range.linear 1 50)

  case simplex constraints of
    Nothing         -> discard
    Just assignment -> do
      annotate $ show assignment
      assert $ all (assignment `isModel`) constraints

prop_simplex_sound_with_cutting_plane :: Property
prop_simplex_sound_with_cutting_plane = withDiscards 300 $ property $ do
  constraints <- forAll $ genConstraints [LessEquals, GreaterEquals, Equals]
    (Gen.int $ Range.linear 0 20)
    (Range.linear 1 50)

  let original_vars = varsInAll constraints

  case Simplex.initTableau constraints of
    Nothing        -> discard
    Just tableau_0 -> do
      let tableau_1 = last $ Simplex.steps tableau_0
      guard $ Simplex.isSatisfied tableau_1

      -- FIXME: will probably crash if random cutting plane has new original variables.
      cutting_plane <- forAll $ genConstraint 
        [LessEquals, GreaterEquals, Equals] 
        (Gen.int $ Range.linear 0 20)

      let tableau_2 = last $ Simplex.steps tableau_1
      guard $ Simplex.isSatisfied tableau_2

      let assignment = M.restrictKeys (Simplex.getAssignment tableau_2) original_vars
      annotate $ show assignment
      assert $ all (assignment `isModel`) constraints

prop_fourier_motzkin_sound :: Property
prop_fourier_motzkin_sound = property $ do
  constraints <- forAll $ genConstraints [LessEquals, GreaterEquals, Equals]
    (Gen.int $ Range.linear 0 4)
    (Range.linear 1 5)

  case fourierMotzkin constraints of
    Nothing         -> discard
    Just assignment -> do
      annotate $ show assignment
      assert $ all (assignment `isModel`) constraints

prop_fourier_motzkin_equiv_simplex :: Property
prop_fourier_motzkin_equiv_simplex = property $ do
  constraints <- forAll $ genConstraints [LessEquals, GreaterEquals, Equals]
    (Gen.int $ Range.linear 0 5)
    (Range.linear 1 5)

  isJust (fourierMotzkin constraints) === isJust (simplex constraints)

prop_simplex_no_cycle :: Property
prop_simplex_no_cycle = withDiscards 300 $ property $ do
  constraints <- forAll $ genConstraints [LessEquals, GreaterEquals, Equals]
    (Gen.int $ Range.linear 0 1)
    (Range.linear 1 50)

  let has_duplicate :: Set S.IntSet -> [S.IntSet] -> Bool
      has_duplicate seen [] = False
      has_duplicate seen (current_basis : next_steps) =
         Set.member current_basis seen || has_duplicate (Set.insert current_basis seen) next_steps

  case fmap (M.keysSet . Simplex.getBasis) . Simplex.steps <$> Simplex.initTableau constraints of
    Nothing -> discard
    Just steps -> assert $ not $ has_duplicate Set.empty steps

prop_invariant_non_basic_vars_satisfy_bounds :: Property
prop_invariant_non_basic_vars_satisfy_bounds = withDiscards 300 $ property $ do
  constraints <- forAll $ genConstraints [LessEquals, GreaterEquals, Equals]
    (Gen.int $ Range.linear 0 20)
    (Range.linear 1 50)

  let check :: Tableau -> Bool
      check tableau =
        let all_vars = M.keysSet $ Simplex.getAssignment tableau
            basic_vars = M.keysSet $ Simplex.getBasis tableau
            non_basic_vars = all_vars S.\\ basic_vars
         in not $ any (Simplex.isBoundViolated tableau) $ S.toList non_basic_vars

  case Simplex.steps <$> Simplex.initTableau constraints of
    Nothing    -> discard
    Just steps -> assert $ all check steps

prop_invariant_assignment_matches_basis_evaluation :: Property
prop_invariant_assignment_matches_basis_evaluation = withDiscards 300 $ property $ do
  constraints <- forAll $ genConstraints [LessEquals, GreaterEquals, Equals]
    (Gen.int $ Range.linear 0 20)
    (Range.linear 1 50)

  let check :: Tableau -> Bool
      check tableau = fromMaybe False $ do
        basis_values <- traverse (eval (Simplex.getAssignment tableau) . AffineExpr 0) (Simplex.getBasis tableau)
        return $ basis_values `M.isSubmapOf` Simplex.getAssignment tableau

  case Simplex.steps <$> Simplex.initTableau constraints of
    Nothing    -> discard
    Just steps -> assert $ all check steps

prop_invariant_disjoint_basic_and_nonbasic_vars :: Property
prop_invariant_disjoint_basic_and_nonbasic_vars = withDiscards 300 $ property $ do
  constraints <- forAll $ genConstraints [LessEquals, GreaterEquals, Equals]
    (Gen.int $ Range.linear 0 20)
    (Range.linear 1 50)

  let check :: Tableau -> Bool
      check tableau =
        let
          basic_vars = M.keysSet $ Simplex.getBasis tableau
          non_basic_vars = S.unions $ map M.keysSet $ M.elems $ Simplex.getBasis tableau
        in
          S.disjoint basic_vars non_basic_vars

  case Simplex.steps <$> Simplex.initTableau constraints of
    Nothing    -> discard
    Just steps -> assert $ all check steps

prop_branch_and_bound_sound :: Property 
prop_branch_and_bound_sound = withDiscards 300 $ property $ do
  -- FIXME: doesn't terminate on equality constraints very well at the moment:
  constraints <- forAll $ genConstraints [LessEquals, GreaterEquals]
    (Gen.int $ Range.linear 0 20)
    (Range.linear 1 50)

  -- Even when branch-and-bound eventually terminates, it might 
  -- take a long time. So let's limit the number of iterations 
  -- in the test:
  let states = take 100 $ BranchAndBound.steps constraints (varsInAll constraints)

  case mapMaybe BranchAndBound.isSat states of
    []               -> discard
    (assignment : _) -> do
      annotate $ show assignment 
      assert $ all (assignment `isModel`) constraints
      assert $ all isIntegral assignment

-- | NOTE: This property is not expected to hold but useful to find 
-- small examples where termination is slow. 
prop_branch_and_bound_terminates_quickly :: Property
prop_branch_and_bound_terminates_quickly = property $ do
  constraints <- forAll $ genConstraints [LessEquals, GreaterEquals]
    (Gen.int $ Range.linear 0 20)
    (Range.linear 1 50)

  let max_iterations = 100
      iterations = take max_iterations $ BranchAndBound.steps constraints (varsInAll constraints)

      terminates_with_sat = any (isJust . BranchAndBound.isSat) iterations
      terminates_with_unsat = length iterations < max_iterations

  assert (terminates_with_sat || terminates_with_unsat)
