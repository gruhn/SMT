module TestUninterpretedFunctions 
  ( prop_equalities_symmetric
  , prop_infeasible_subsets_are_minimal
  ) where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Expression (Expr)
import Theory.UninterpretedFunctions (Equation (..), FuncTerm(..), subTerms)
import CNF (CNF, Literal (..))
import qualified SAT.CDCL as CDCL
import Theory (SolverResult(..), solve, isUNSAT, isSAT)
import qualified Data.Set as S
import qualified Data.List as List
import Debug.Trace

-- generators

genTerms :: Gen [FuncTerm]
genTerms = subTerms <$> gen_term 10
  where
    gen_term :: Int -> Gen FuncTerm
    gen_term max_args = do
      name <- Gen.element [ "f", "g", "h" ]
      args <- Gen.list (Range.linear 0 max_args) (gen_term $ max_args `div` 2)
      return (FuncTerm name args)

genLiteral :: [FuncTerm] -> Gen (Literal Equation)
genLiteral terms = do
  lhs <- Gen.element terms
  rhs <- Gen.element terms
  polarity <- Gen.element [Pos, Neg]
  return $ polarity (lhs `Equals` rhs)

genLiterals :: [FuncTerm] -> Gen [Literal Equation]
genLiterals terms = Gen.list (Range.linear 1 50) (genLiteral terms)

-- custom show functions

showLiteral :: Literal Equation -> String
showLiteral (Pos (lhs `Equals` rhs)) = show lhs ++ " == " ++ show rhs
showLiteral (Neg (lhs `Equals` rhs)) = show lhs ++ " /= " ++ show rhs

showLiterals :: [Literal Equation] -> String
showLiterals = List.intercalate "; " . map showLiteral

-- properties

prop_equalities_symmetric :: Property
prop_equalities_symmetric = property $ do
  terms <- forAll genTerms

  lits1 <- forAllWith showLiterals (genLiterals terms)
  lits2 <- forAllWith showLiterals (genLiterals terms)

  let flip (t1 `Equals` t2) = t2 `Equals` t1

  let result1 = Theory.solve $ lits1 ++ lits2
  let result2 = Theory.solve $ lits1 ++ map (fmap flip) lits2

  case (result1, result2) of
    (SAT   _, SAT   _) -> success
    (UNSAT _, UNSAT _) -> success
    _                  -> failure

prop_infeasible_subsets_are_minimal :: Property
prop_infeasible_subsets_are_minimal = property $ do
  terms    <- forAll genTerms
  literals <- forAllWith showLiterals (genLiterals terms)

  case Theory.solve literals of
    UNSAT infeasible_subset -> do
      annotate $ showLiterals $ S.toList infeasible_subset
      -- infeasible subset is in fact unsatisfiable
      assert $ isUNSAT $ Theory.solve $ S.toList infeasible_subset
      -- taking away any element makes it satisfiable ==> it's minimal.
      assert $ isSAT $ Theory.solve $ tail $ S.toList infeasible_subset
    SAT _   -> discard
    UNKNOWN -> do
      annotate "The solver is a decision procedure. It should never return UNKNOWN."
      failure  
      
prop_solver_is_sound :: Property
prop_solver_is_sound = error "TODO"

prop_equalities_transitive :: Property
prop_equalities_transitive = error "TODO"

prop_function_congruence :: Property
prop_function_congruence  = error "TODO"

