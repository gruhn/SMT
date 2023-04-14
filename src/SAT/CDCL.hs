module SAT.CDCL (sat) where

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
import Control.Monad.State.Strict (State, runState, modify, gets, evalState)
import Control.Monad.Extra (ifM)
import Theory (Theory, Assignment, SolverResult (..))
import qualified Theory

{-| 
  Sequence of literals that are assigned `true` at the current state.
  Each literal is paired with it's antecedent, i.e. the clause that 
  implied the truth of the literal. For "decisions" the antecedent is 
  `Nothing`.
  
  If the given formula is satifiable, the satisfying assignment is 
  obtained from the trail.
-}
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

type CDCLState a = State (CNF a, Trail a)

getFormula :: CDCLState a (CNF a)
getFormula = gets fst

getTrail :: CDCLState a (Trail a)
getTrail = gets snd

modifyFormula :: (CNF a -> CNF a) -> CDCLState a ()
modifyFormula f = modify $ first f

modifyTrail :: (Trail a -> Trail a) -> CDCLState a ()
modifyTrail f = modify $ second f

findUnassignedLiteral :: forall a. Ord a => CNF a -> Trail a -> Maybe (Literal a)
findUnassignedLiteral cnf trail = listToMaybe $ do
  let is_sat :: Clause a -> Bool
      is_sat clause = any (`S.member` clause) (trailLiterals trail)
  clause  <- S.toList $ S.filter (not . is_sat) cnf
  literal <- S.toList $ clause S.\\ S.map complement (trailLiterals trail)
  return $ complement literal

-- TODO: what if resolvent is tautology?
resolvent :: Ord a => Literal a -> Clause a -> Clause a -> Clause a
resolvent literal clause1 clause2 =
    S.delete (complement literal)
  $ S.delete literal
  $ S.union clause1 clause2

trailLiterals :: forall a. Ord a => Trail a -> S.Set (Literal a)
trailLiterals = S.fromList . fmap fst

------------------------------------------

{-|
  After conflict detection, backtrack up to the *second* decision level, where a literal from the 
  current conflict clause was assigned. We don't choose the first decision level because, by 
  by construction, the conflict clause always contains a literal from the decision level where 
  the conflict occured. So backtracking to the first matching decision level, is a no-op.
-}
backtrack :: forall a. Ord a => Clause a -> CDCLState a ()
backtrack conflict = do
  trail <- getTrail
  case decisionLevels trail of
    [] -> return ()
    first_decision_level : rest_decision_levels -> do
      let conflict_vars = S.map getVariable conflict
          decision_level_vars dl = S.fromList $ getVariable . fst <$> dl
  
          no_match :: Trail a -> Bool
          no_match = not . any (`S.member` conflict_vars) . decision_level_vars

      modifyTrail $ const $ concat $ dropWhile no_match rest_decision_levels

resolveConflict :: Ord a => Clause a -> CDCLState a Bool
resolveConflict conflict = do
  trail <- getTrail

  if not $ any isDecision trail then
    -- conflict at decision level 0 ==> UNSAT
    return False
  else if isAsserting conflict trail then do
    backtrack conflict
    modifyFormula (S.insert conflict)
    return True
  else
    case trail of
      (literal, Just antecedent) : rest_trail -> do
        modifyTrail (const rest_trail) 
        resolveConflict (resolvent literal conflict antecedent)
      -- TODO: can these cases occur?
      []                                     -> undefined
      (literal, Nothing) : rest_propagations -> undefined

isAsserting :: Ord a => Clause a -> Trail a -> Bool
isAsserting clause trail =
  case decisionLevels trail of
    [] -> False
    (current_decision_level : _) -> 
      let literals = S.fromList $ getVariable . fst <$> current_decision_level
       in length (literals `S.intersection` S.map getVariable clause) == 1

propagate :: forall a. Ord a => CDCLState a (Maybe (Clause a))
propagate = 
  let go :: [Clause a] -> CDCLState a (Maybe (Clause a))
      go clauses = do
        trail <- getTrail

        let trail_literals = trailLiterals trail

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

        case find is_conflict clauses_not_sat of
          Just conflict -> return $ Just conflict
          Nothing ->
            case find is_unit clauses_not_sat of
              Nothing -> return Nothing
              Just clause -> do
                let new_propagation = (S.findMin $ unassigned_literals clause, Just clause)
                modifyTrail (new_propagation :)
                go clauses_not_sat

   in getFormula >>= go . S.toList

-- TODO: theory sovler has no state and has to recompute everything for each call
cdcl :: (Theory t c, Ord t) => CDCLState t (SolverResult t c)
cdcl = do
  maybe_conflict <- propagate
  case maybe_conflict of
    Just conflict ->
      ifM (resolveConflict conflict) cdcl (return (UNSAT conflict))

    Nothing -> do
      trail <- getTrail
      cnf <- getFormula

      -- invoke theory solver
      case Theory.solve (fst <$> trail) of
        -- theory solver found conflicting subset ==> resolve conflict
        Theory.UNSAT conflict -> 
          ifM (resolveConflict conflict) cdcl (return (UNSAT conflict))

        -- constraints are satisfiable ==> hand back to SAT solver
        Theory.SAT assignment -> 
          case findUnassignedLiteral cnf trail of
            Nothing -> 
              -- all variables assinged ==> SAT              
              return (SAT assignment)

            Just decision -> do
              modifyTrail ((decision, Nothing) :)
              cdcl      

        -- theory solver made no decision ==> ???
        Theory.UNKNOWN -> 
          error "TODO: handle UNKNOWN case in CDCL"

sat :: forall t c. (Theory t c, Ord t) => CNF t -> SolverResult t c
sat formula = evalState cdcl (formula, [])

