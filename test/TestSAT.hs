module TestSAT
  ( prop_dpll_sound,
    prop_cdcl_sound,
    prop_dpll_equiv_cdcl,
  ) where

import qualified SAT.CDCL as CDCL
import qualified SAT.DPLL as DPLL

import CNF (CNF, Clause, Literal (..))
import Data.Maybe (isJust)
import qualified Data.Set as S
import Hedgehog hiding (Var, eval)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Theory ((|=), SolverResult (..), isSAT)
import qualified Theory
import Theory.Propositions (Prop(..))

genLiteral :: Int -> Gen (Literal Prop)
genLiteral var = do
  polarity <- Gen.element [Pos, Neg]
  return $ polarity (Prop var)

genClause :: Range Int -> Gen (Clause Prop)
genClause var_range = do
  vars <- Gen.set (Range.linear 1 10) $ Gen.int var_range
  S.fromList <$> traverse genLiteral (S.toList vars)

genCNF :: Gen (CNF Prop)
genCNF =
  Gen.set (Range.linear 1 20) $ genClause $ Range.linear 0 10

prop_dpll_sound :: Property
prop_dpll_sound = property $ do
  cnf <- forAll genCNF
  case DPLL.sat cnf of
    Nothing -> success
    Just assignment -> do
      annotate $ show assignment
      assert $ assignment |= cnf

prop_cdcl_sound :: Property
prop_cdcl_sound = property $ do
  cnf <- forAll genCNF
  case CDCL.sat cnf of
    UNSAT _ -> success
    SAT assignment -> do
      annotate $ show assignment
      assert $ assignment |= cnf

prop_dpll_equiv_cdcl :: Property
prop_dpll_equiv_cdcl = property $ do
  cnf <- forAll genCNF
  assert $ isJust (DPLL.sat cnf) == isSAT (CDCL.sat cnf)
