module ConflictDrivenClauseLearning (sat) where

import Expression (Expr)
import Assignment (Assignment)
import qualified Assignment as Assign
import CNF (CNF, Literal, Clause, complement)
import DPLL (convergeUnitPropagation)
import qualified Data.Map as M
import qualified Data.Set as S
import Utils (rightToMaybe)

sat :: CNF -> Maybe Assignment
sat cnf = Assign.fromLiteralList <$> rightToMaybe (cdcl cnf)

pickLiteral :: CNF -> Literal
pickLiteral = S.findMin . S.findMin

type ImplGraph = M.Map Literal [Literal]

-- read as: litA implies litB
insertImpl :: Literal -> Literal -> ImplGraph -> ImplGraph
insertImpl litA litB = M.insertWith (<>) litB [litA]

type Conflict = [Literal]

findConflict :: ImplGraph -> Maybe Conflict
findConflict impl_graph = do
  let literals = M.keysSet impl_graph
      conflict_literals = S.intersection literals (S.map complement literals)

  conflict_literal <- S.lookupMin conflict_literals

  let deps1 = impl_graph M.! conflict_literal
      deps2 = impl_graph M.! complement conflict_literal

  return (deps1 <> deps2)

learnClause :: Conflict -> Clause
learnClause = S.fromList . fmap complement

cdcl :: CNF -> Either Conflict [Literal]
cdcl = split_and_recur M.empty
  where
    split_and_recur :: ImplGraph -> CNF -> Either Conflict [Literal]
    split_and_recur impl_graph cnf
      | null cnf     = Right []   -- derived empty clause set => formula is satisfiable
      | any null cnf = Left []    -- derived empty clause     => formula is unsatifiable
      | otherwise = 
        case go split_lit_a impl_graph $ S.insert (S.singleton split_lit_a) cnf of
          Right literals -> Right literals
          Left conflict ->
            if split_lit_a `elem` conflict then
              go split_lit_b impl_graph $ S.insert (S.singleton split_lit_b) $ S.insert (learnClause conflict) $ cnf
            else
              Left conflict
        where
          split_lit_a = pickLiteral cnf
          split_lit_b = complement split_lit_a

    go :: Literal -> ImplGraph -> CNF -> Either Conflict [Literal]
    go literal impl_graph cnf_0 =
      let (unit_literals, cnf_1) = convergeUnitPropagation cnf_0
          impl_graph' = foldr (insertImpl literal) impl_graph unit_literals 
      in  case findConflict impl_graph' of
            Just conflict -> Left conflict
            Nothing       -> (literal :) <$> split_and_recur impl_graph' cnf_1

