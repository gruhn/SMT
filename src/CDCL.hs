module CDCL where

import Expression (Expr)
import Assignment (Assignment)
import qualified Assignment as Assign
import CNF (CNF, Literal, Clause, complement)
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.State (State)
import qualified Control.Monad.State as State
import Data.Foldable (find)

type ImplGraph = String

type State' = State ImplGraph

antecedent :: Literal -> Clause
antecedent = undefined

pickLiteral :: CNF -> State' Literal
pickLiteral = return . S.findMin . S.findMin

extractUnitClause :: CNF -> Maybe (Literal, CNF)
extractUnitClause cnf = extract <$> find is_unit_clause cnf
  where
    is_unit_clause :: Clause -> Bool
    is_unit_clause clause = S.size clause == 1

    extract :: Clause -> (Literal, CNF)
    extract unit_clause = (S.findMin unit_clause, S.delete unit_clause cnf)

propagate :: CNF -> State' ([Literal], CNF)
propagate cnf_0 =
  case extractUnitClause cnf_0 of 
    Nothing              -> return ([], cnf_0)
    Just (literal, cnf_1) -> do
      -- TODO: add literal to implication graph
      (literals, cnf_2) <- propagate cnf_1
      return (literal : literals, cnf_2)

-- analyzeConflict :: CNF -> State' ()
-- analyzeConflict cnf
--   | S.empty `elem` cnf = _ -- conflict!
--   | otherwise          = _

decide :: CNF -> State ImplGraph (Maybe [Literal])
decide cnf = do
  literal <- pickLiteral cnf
  -- TODO : add to graph

  (literals, cnf') <- propagate cnf

  if null cnf' then                    -- all literals assigned => SAT
    return $ Just $ literal : literals    
  else if S.empty `notElem` cnf' then -- no conflict => decide next variable
    decide cnf'
  else                                -- conflict!
    