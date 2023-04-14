module Theory where

import CNF (Literal, CNF, Clause)
import Data.IntMap (IntMap)
import qualified Data.Set as S

type Assignment c = IntMap c

(|=) :: forall t c. Theory t c => Assignment c -> CNF t -> Bool
(|=) assignment = null . S.filter (not . satisfies_clause)
  where
    satisfies_clause :: Clause t -> Bool
    satisfies_clause = any (assignment `satisfies`)

class Theory t c | t -> c where 
  {-| 
    A theory solver either returns a model for the given theory constraints or 
    an (preferably minimal) unsatisfiable subset of the constraints.
  -}
  solve :: [Literal t] -> Either [Literal t] (Assignment c)

  satisfies :: Assignment c -> Literal t -> Bool
