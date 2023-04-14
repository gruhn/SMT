module SAT.CDCL3 where

import Expression (Expr)
import qualified Assignment as Assign
import CNF (CNF, Literal (..), Clause, complement, getVariable)
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Foldable (find, toList)
import Utils (takeWhileJust)
import Control.Arrow (second, Arrow (first))
import Data.List (uncons)
import Data.Maybe (listToMaybe)
import Control.Monad (guard)

data State a = State 
  { getFormula :: CNF a
  , getTrail :: Trail a
  } deriving Show

type Trail a = [(Literal a, Maybe (Clause a))]

isDecision :: (Literal a, Maybe (Clause a)) -> Bool
isDecision (_, Nothing) = True
isDecision (_, Just _)  = False

decisionLevels :: Trail a -> [Trail a]
decisionLevels trail = 
  case break isDecision trail of
    (decision_level_0, []) -> [decision_level_0]
    (decision_level_n, decision : rest_trail) -> 
       (decision_level_n ++ [decision]) : decisionLevels rest_trail

assign :: forall a. Ord a => Literal a -> CNF a -> CNF a
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

assignedLiterals :: State a -> [Literal a]
assignedLiterals = fmap fst . getTrail  

unassignedLiterals :: Ord a => State a -> [Literal a]
unassignedLiterals state = 
  let cnf_after_assignment = foldr assign (getFormula state) (assignedLiterals state)
   in S.toList $ S.unions cnf_after_assignment 

addClause :: Ord a => Clause a -> State a -> State a
addClause clause state = 
  state { getFormula = S.insert clause $ getFormula state }

------------------------------------------

initialize :: CNF a -> State a
initialize cnf = State cnf []

{-|
  After conflict detection, backtrack up to the *second* decision level, where a literal from the 
  current conflict clause was assigned. We don't choose the first decision level because, by 
  by construction, the conflict clause always contains a literal from the decision level where 
  the conflict occured. So backtracking to the first matching decision level, is a no-op.
-}
backtrack :: forall a. Ord a => Clause a -> State a -> State a
backtrack conflict state =
  case decisionLevels $ getTrail state of
    [] -> state
    first_decision_level : rest_decision_levels -> 
      let conflict_vars = S.map getVariable conflict
          decision_level_vars dl = S.fromList $ getVariable . fst <$> dl
  
          no_match :: Trail a -> Bool
          no_match = not . any (`S.member` conflict_vars) . decision_level_vars

       in state { getTrail = concat $ dropWhile no_match rest_decision_levels }

decide :: Ord a => State a -> Maybe (State a)
decide state = listToMaybe $ do
  literal <- unassignedLiterals state
  return $ state { getTrail = (complement literal, Nothing) : getTrail state }

-- TODO: what if resolvent is tautology?
resolvent :: Ord a => Literal a -> Clause a -> Clause a -> Clause a
resolvent literal clause1 clause2 =
    S.delete (complement literal)
  $ S.delete literal
  $ S.union clause1 clause2

resolveConflict :: Ord a => Clause a -> State a -> Maybe (State a)
resolveConflict conflict state
  | not . any isDecision $ getTrail state = Nothing -- conflict at decision level 0 ==> UNSAT
  | isAsserting conflict state = Just $ backtrack conflict $ addClause conflict state
  | otherwise = case getTrail state of
      [] -> Nothing -- conflict at decision level 0 ==> UNSAT
      (literal, Nothing) : rest_propagations -> undefined
      (literal, Just antecedent) : rest_trail -> 
        resolveConflict (resolvent literal conflict antecedent)
          $ state { getTrail = rest_trail }

trailLiterals :: forall a. Ord a => State a -> S.Set (Literal a)
trailLiterals state = S.fromList $ fst <$> getTrail state

isAsserting :: Ord a => Clause a -> State a -> Bool
isAsserting clause state = 
  case decisionLevels $ getTrail state of
    [] -> False
    (current_decision_level : _) -> 
      let literals = S.fromList $ getVariable . fst <$> current_decision_level
       in length (literals `S.intersection` S.map getVariable clause) == 1

propagate :: forall a. Ord a => State a -> (State a, Maybe (Clause a))
propagate state = 
  let go :: [Clause a] -> State a -> (State a, Maybe (Clause a))
      go clauses state = 
        let trail_literals = trailLiterals state

            unassigned_literals :: Clause a -> S.Set (Literal a)
            unassigned_literals clause = clause S.\\ S.map complement trail_literals

            is_sat :: Clause a -> Bool
            is_sat = any (`S.member` trail_literals)

            is_unit :: Clause a -> Bool
            is_unit = (==1) . length . unassigned_literals

            is_conflict :: Clause a -> Bool
            is_conflict = null . unassigned_literals          

            clauses_not_sat :: [Clause a]
            clauses_not_sat = filter (not . is_sat) clauses

            add_propagation :: Literal a -> Clause a -> State a -> State a
            add_propagation literal antecedent state = 
              state { getTrail = (literal, Just antecedent) : getTrail state }

         in case find is_conflict clauses_not_sat of
            Just conflict -> (state, Just conflict)
            Nothing ->
              case find is_unit clauses_not_sat of
                Nothing -> (state, Nothing)
                Just clause -> 
                  let state' = add_propagation (S.findMin $ unassigned_literals clause) clause state
                   in go clauses_not_sat state'

   in go (S.toList $ getFormula state) state

cdcl :: forall a. Ord a => CNF a -> Maybe [Literal a]
cdcl cnf =  
  let go :: State a -> Maybe (State a)
      go state_0 = 
        case propagate state_0 of
          (state_1, Just conflict) -> resolveConflict conflict state_1 >>= go
          (state_1, Nothing)       -> 
            case decide state_1 of
              Nothing      -> Just state_1 -- all variables assinged ==> SAT
              Just state_2 -> go state_2

   in S.toList . trailLiterals <$> go (initialize cnf)