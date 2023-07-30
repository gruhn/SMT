module Theory where

import CNF (Literal, CNF, Clause)
import Data.IntMap (IntMap)
import qualified Data.Set as S
import Data.Set (Set)
import Expression (Expr)

type Assignment c = IntMap c

(|=) :: forall t c. Theory t c => Assignment c -> CNF t -> Bool
(|=) assignment = null . S.filter (not . satisfies_clause)
  where
    satisfies_clause :: Clause t -> Bool
    satisfies_clause = any (assignment `satisfies`)

{-| 
  A theory solver can prove satisfiability (SAT) of given 
  constraints and return a model. It can also prove that the 
  constraints are unsatisfiable (UNSAT) and return a (preferably minimal) 
  unsatisfiable subset of the constraints as an explanation. If the solver is 
  incomplete it may also make no decision either way and return UNKNOWN.
-}
data SolverResult t c = SAT (Assignment c) | UNSAT (Set (Literal t)) | UNKNOWN
  deriving (Show, Eq)

isSAT :: SolverResult t c -> Bool
isSAT (SAT _) = True
isSAT _       = False

isUNSAT :: SolverResult t c -> Bool
isUNSAT (UNSAT _) = True
isUNSAT _         = False

class Theory t c | t -> c where 
  solve :: [Literal t] -> SolverResult t c

  satisfies :: Assignment c -> Literal t -> Bool
