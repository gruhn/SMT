module SAT.DPLL (dpll) where

import Expression (Expr)
import CNF (conjunctiveNormalForm, CNF, Literal (..), complement, Clause, variables)
import qualified Data.Set as S
import Data.Foldable (toList, find)
import Data.Maybe (fromMaybe)
import Control.Monad (liftM)
import qualified Data.Map as M
import qualified Assignment as Assign
import Assignment (Assignment)
import Control.Applicative ((<|>))
import Control.Arrow (first)

deleteLiteral :: Ord a => Literal a -> CNF a -> CNF a
deleteLiteral = S.map . S.delete

deleteClausesContainingAny :: Eq a => CNF a -> S.Set (Literal a) -> CNF a
deleteClausesContainingAny cnf literals =
  S.filter (\clause -> not $ any (`elem` clause) literals) cnf

unitPropagate :: Ord a => CNF a -> Maybe (Literal a, CNF a)
unitPropagate cnf_0 = do
  unit_clause <- find ((==1) . length) cnf_0

  -- Partition CNF formula into unit clauses and non-unit clauses.
  let unit_clause_literal = S.findMin unit_clause

  -- Remove unit clause literals from non-unit clauses
  let cnf_2 = deleteLiteral (complement unit_clause_literal) cnf_0

  -- Remove non-unit clauses that contain the complement of a unit clause literal
  let cnf_3 = cnf_2 `deleteClausesContainingAny` S.singleton unit_clause_literal

  return (unit_clause_literal, cnf_3)

convergeUnitPropagation :: Ord a => CNF a -> ([Literal a], CNF a)
convergeUnitPropagation cnf_0 =
  case unitPropagate cnf_0 of
    Nothing -> ([], cnf_0)
    Just (unit_literal, cnf_1) ->
      first (unit_literal:) $ convergeUnitPropagation cnf_1

pureLiteralElimination :: Ord a => CNF a -> ([Literal a], CNF a)
pureLiteralElimination cnf = (toList pure_literals, cnf `deleteClausesContainingAny` pure_literals)
  where
    is_positive :: Literal a -> Bool
    is_positive (Pos _) = True
    is_positive (Neg _) = False

    (positive_literals, negative_literals) = S.partition is_positive (S.unions cnf)

    pure_literals = S.union
      (positive_literals S.\\ S.map complement negative_literals)
      (negative_literals S.\\ S.map complement positive_literals)

dpll :: Ord a => CNF a -> Maybe [Literal a]
dpll cnf_0 = ((unit_literals <> pure_literals) <>) <$> maybe_rest_literals
  where
    (unit_literals, cnf_1) = convergeUnitPropagation cnf_0
    (pure_literals, cnf_2) = pureLiteralElimination cnf_1
    maybe_rest_literals = split_and_recur cnf_2

    -- TODO: use "Dynamic Largest Individual Sum (DLIS)" heuristic 
    pick_literal :: CNF a -> Literal a
    pick_literal = S.findMin . S.findMin

    split_and_recur :: Ord a => CNF a -> Maybe [Literal a]
    split_and_recur cnf
      | null cnf     = Just []      -- derived empty clause set => SAT
      | any null cnf = Nothing      -- derived empty clause     => UNSAT
      | otherwise    = dpll cnf_left <|> dpll cnf_right
      where
        split_literal = pick_literal cnf
        cnf_left  = S.insert (S.singleton split_literal) cnf
        cnf_right = S.insert (S.singleton $ complement split_literal) cnf