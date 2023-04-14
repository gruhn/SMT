module TestSAT
  ( prop_dpll_sound,
    prop_cdcl_sound,
    prop_dpll_equiv_cdcl,
  ) where

import Algorithm.CDCL3 (cdcl)
import Algorithm.DPLL (dpll)
import Assignment ((|=))
import CNF (CNF, Clause, Literal (..))
import Data.Maybe (isJust)
import qualified Data.Set as S
import Hedgehog hiding (Var, eval)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

genLiteral :: Int -> Gen (Literal Int)
genLiteral var = do
  polarity <- Gen.element [Pos, Neg]
  return $ polarity var

genClause :: Range Int -> Gen (Clause Int)
genClause var_range = do
  vars <- Gen.set (Range.linear 1 10) $ Gen.int var_range
  S.fromList <$> traverse genLiteral (S.toList vars)

genCNF :: Gen (CNF Int)
genCNF =
  Gen.set (Range.linear 1 20) $ genClause $ Range.linear 0 10

isModel :: forall a. Ord a => [Literal a] -> CNF a -> Bool
isModel assignments cnf = null cnf'
  where
    cnf' = foldr assign cnf assignments

    assign :: Literal a -> CNF a -> CNF a
    assign literal formula = formula'
      where
        delete_clauses_with :: Literal a -> CNF a -> CNF a
        delete_clauses_with literal = S.filter (not . S.member literal)

        delete_literal :: Literal a -> CNF a -> CNF a
        delete_literal literal = S.map (S.delete literal)

        formula' =
          case literal of
            -- If a variable is assigned `true`, then all clauses where it
            -- appears as a positive literal are satisfied, so they can be deleted.
            -- In clauses where it appears negatively, the literal does not contribute
            -- to the satisfiability of that clause, so the literal can be deleted from
            -- that clause.
            Pos var -> delete_literal (Neg var) . delete_clauses_with (Pos var) $ formula
            -- Conversely, if a variable is assigned `false`, then we delete all clauses
            -- where it appears as a negative literal and we delete all positive occurances
            -- of it in all clauses.
            Neg var -> delete_literal (Pos var) . delete_clauses_with (Neg var) $ formula

prop_dpll_sound :: Property
prop_dpll_sound = property $ do
  cnf <- forAll genCNF
  case dpll cnf of
    Nothing -> success
    Just assignments -> do
      annotate $ show assignments
      assert $ isModel assignments cnf

prop_cdcl_sound :: Property
prop_cdcl_sound = property $ do
  cnf <- forAll genCNF
  case cdcl cnf of
    Nothing -> success
    Just assignments -> do
      annotate $ show assignments
      assert $ isModel assignments cnf

prop_dpll_equiv_cdcl :: Property
prop_dpll_equiv_cdcl = property $ do
  cnf <- forAll genCNF
  assert $ isJust (dpll cnf) == isJust (cdcl cnf)
