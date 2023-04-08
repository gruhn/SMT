module TestLinearArithmatic 
  ( prop_simplex_sound
  , prop_fourier_motzkin_sound
  , prop_fourier_motzkin_equiv_simplex  
  , prop_simplex_no_cycle
  , prop_invariant_non_basic_vars_satisfy_bounds
  , prop_invariant_assignment_matches_basis_evaluation  
  , prop_branch_and_bound_sound
  ) where

import Hedgehog hiding (Var, eval)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Theory.LinearArithmatic.Simplex
import qualified Data.IntMap as M
import qualified Data.IntSet as S
import qualified Data.Set as Set
import Theory.LinearArithmatic.Constraint
import Theory.LinearArithmatic.FourierMotzkin (fourierMotzkin)
import Data.Maybe (isJust, fromMaybe)
import Data.Set (Set)
import Theory.LinearArithmatic.BranchAndBound (branchAndBound, isIntegral)

-- TODO: generate more representative constraint sets 
genConstraints :: Gen Var -> Range Int -> Gen [Constraint]
genConstraints gen_var range =  Gen.list range $ do
  linear_expr <- fmap M.fromList $ Gen.list (Range.linear 0 10) $ do 
    coeff <- toRational <$> Gen.int (Range.linearFrom 0 (-10) 10)
    var <- gen_var
    return (var, coeff)

  -- TODO: extend to all constraint types
  rel <- Gen.element [LessEquals, GreaterEquals]  

  constant <- toRational <$> Gen.int (Range.linearFrom 0 (-10) 10)

  -- TODO: make sure that constraints are always normalized by construction.  
  return $ normalize (AffineExpr constant linear_expr, rel)

prop_simplex_sound :: Property
prop_simplex_sound = property $ do
  constraints <- forAll $ genConstraints 
    (Gen.int $ Range.linear 0 20)
    (Range.linear 1 50)

  case simplex constraints of
    Nothing         -> success
    Just assignment -> do 
      annotate $ show assignment 
      assert $ all (assignment `isModel`) constraints

prop_fourier_motzkin_sound :: Property
prop_fourier_motzkin_sound = property $ do
  constraints <- forAll $ genConstraints 
    (Gen.int $ Range.linear 0 4)
    (Range.linear 1 5)

  case fourierMotzkin constraints of
    Nothing         -> success
    Just assignment -> do 
      annotate $ show assignment 
      assert $ all (assignment `isModel`) constraints

prop_fourier_motzkin_equiv_simplex :: Property
prop_fourier_motzkin_equiv_simplex = property $ do
  constraints <- forAll $ genConstraints 
    (Gen.int $ Range.linear 0 5)
    (Range.linear 1 5)

  isJust (fourierMotzkin constraints) === isJust (simplex constraints)

prop_simplex_no_cycle :: Property
prop_simplex_no_cycle = property $ do
  constraints <- forAll $ genConstraints 
    (Gen.int $ Range.linear 0 1)
    (Range.linear 1 50)

  let has_duplicate :: Set S.IntSet -> [S.IntSet] -> Bool
      has_duplicate seen [] = False
      has_duplicate seen (current_basis : next_steps) =
         Set.member current_basis seen || has_duplicate (Set.insert current_basis seen) next_steps

  case fmap (M.keysSet . getBasis) . simplexSteps <$> initTableau constraints of
    Nothing -> success 
    Just steps -> assert $ not $ has_duplicate Set.empty steps

prop_invariant_non_basic_vars_satisfy_bounds :: Property
prop_invariant_non_basic_vars_satisfy_bounds = property $ do
  constraints <- forAll $ genConstraints 
    (Gen.int $ Range.linear 0 20)
    (Range.linear 1 50)

  let check :: Tableau -> Bool
      check tableau = 
        let all_vars = M.keysSet $ getAssignment tableau
            basic_vars = M.keysSet $ getBasis tableau
            non_basic_vars = all_vars S.\\ basic_vars
         in not $ any (isBoundViolated tableau) $ S.toList non_basic_vars

  case simplexSteps <$> initTableau constraints of
    Nothing    -> success
    Just steps -> assert $ all check steps 

prop_invariant_assignment_matches_basis_evaluation :: Property
prop_invariant_assignment_matches_basis_evaluation = property $ do
  constraints <- forAll $ genConstraints 
    (Gen.int $ Range.linear 0 20)
    (Range.linear 1 50)

  let check :: Tableau -> Bool
      check (Tableau basis _ assignment) = fromMaybe False $ do
        basis_values <- traverse (eval assignment . AffineExpr 0) basis
        return $ basis_values `M.isSubmapOf` assignment

  case simplexSteps <$> initTableau constraints of
    Nothing    -> success
    Just steps -> assert $ all check steps 

prop_branch_and_bound_sound :: Property 
prop_branch_and_bound_sound = property $ do
  constraints <- forAll $ genConstraints 
    (Gen.int $ Range.linear 0 20)
    (Range.linear 1 50)

  case branchAndBound constraints (varsInAll constraints) of
    Nothing         -> success
    Just assignment -> do 
      annotate $ show assignment 
      assert $ all (assignment `isModel`) constraints
      assert $ all isIntegral assignment
