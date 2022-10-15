module DPLL (sat) where
import Expr (Expr)
import CNF (conjunctiveNormalForm, CNF, Literal (..), complement, Clause, variables, variableName)
import qualified Data.Set as S
import Data.Foldable (toList, find)
import Utils (fixpoint)
import Data.Maybe (fromMaybe)

sat :: Expr -> Bool
sat = dpll . conjunctiveNormalForm

deleteLiteral :: Literal -> CNF -> CNF
deleteLiteral = S.map . S.delete

deleteClausesContainingAny :: CNF -> S.Set Literal -> CNF
deleteClausesContainingAny cnf literals =
  S.filter (\clause -> not $ any (`elem` clause) literals) cnf

unitPropagate :: CNF -> CNF
unitPropagate cnf_0 = fromMaybe cnf_0 $ do
  unit_clause <- find ((==1) . length) cnf_0

  -- Partition CNF formula into unit clauses and non-unit clauses.
  let unit_clause_literal = S.findMin unit_clause

  -- Remove unit clause literals from non-unit clauses
  let cnf_2 = deleteLiteral (complement unit_clause_literal) cnf_0 

  -- Remove non-unit clauses that contain the complement of a unit clause literal
  let cnf_3 = cnf_2 `deleteClausesContainingAny` S.singleton unit_clause_literal

  return cnf_3

pureLiteralElimination :: CNF -> CNF
pureLiteralElimination cnf = cnf `deleteClausesContainingAny` pure_literals
  where
    is_positive :: Literal -> Bool
    is_positive (Pos _) = True
    is_positive (Neg _) = False

    (positive_literals, negative_literals) = S.partition is_positive (S.unions cnf)

    pure_literals = S.union
      (positive_literals S.\\ S.map complement negative_literals)
      (negative_literals S.\\ S.map complement positive_literals)

dpll :: CNF -> Bool
dpll = go . pureLiteralElimination . fixpoint unitPropagate
  where
    go :: CNF -> Bool
    go cnf
      | null cnf     = True  -- derived empty clause set => formula is satisfiable
      | any null cnf = False -- derived empty clause     => formula is unsatifiable
      | otherwise    = dpll cnf_0 || dpll cnf_1
      where
        split_literal = S.findMin $ S.findMin $ cnf
        cnf_0 = S.insert (S.singleton split_literal) cnf 
        cnf_1 = S.insert (S.singleton $ complement split_literal) cnf