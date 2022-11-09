{-# LANGUAGE ScopedTypeVariables #-}
module CDCL (sat) where

import Expression (Expr)
import Assignment (Assignment)
import qualified Assignment as Assign
import CNF (CNF, Literal, Clause, complement, variableName)
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.State (State)
import qualified Control.Monad.State as State
import Data.Foldable (find, toList)
import Utils (takeWhileJust)
import Control.Monad.Reader (Reader)
import Control.Arrow (second, Arrow (first))

type ClauseMap a = M.Map (Literal a) (S.Set (Clause a))

insertClauseMap :: Ord a => Clause a -> ClauseMap a -> ClauseMap a
insertClauseMap clause clause_map =
  M.unionWith S.union clause_map $ M.fromList $ do
    literal <- toList clause
    return (literal, S.singleton clause)

clauseMap :: Ord a => CNF a -> ClauseMap a
clauseMap = foldr insertClauseMap M.empty

data StateData a = SD 
  { getFormula :: CNF a 
  , getClauseMap :: ClauseMap a 
  }

type State' a = State (StateData a)

type Trail a = [(Clause a, Literal a)]

unassignedLiterals :: StateData a -> S.Set (Literal a)
unassignedLiterals = M.keysSet . getClauseMap

clausesContaining :: Ord a => Literal a -> StateData a -> S.Set (Clause a)
clausesContaining literal = M.findWithDefault S.empty literal . getClauseMap

modifyClauseMap :: (ClauseMap a -> ClauseMap a) -> State' a ()
modifyClauseMap f = do 
  state <- State.get
  let new_value = f $ getClauseMap state 
  State.put $ state { getClauseMap = new_value }

modifyFormula :: (CNF a -> CNF a) -> State' a ()
modifyFormula f = do
  state <- State.get
  let new_value = f $ getFormula state 
  State.put $ state { getFormula = new_value }

propagate :: Ord a => Literal a -> State' a (Either (Clause a) (Trail a))
propagate literal = do
  -- `literal is assigned false, so its complement is assigned true.
  -- All clauses that contain the complement are automatically 
  -- satisfied and can noew be ignored.
  satisfied_clauses <- State.gets $ clausesContaining (complement literal)
  modifyFormula (S.\\ satisfied_clauses)

  -- Since `literal` is assigned false, all clauses that contain it, 
  -- have now one less literal that can contribute to the clauses 
  -- satisfiability. Thus, these clauses are now potentially 
  -- unit or conflict clauses.
  propagated_clauses <- State.gets $ clausesContaining literal

  -- The key set of `clause_map` reflects the unassigned literals. 
  -- Since `literal` (and its complement) are now assigned, we remove them.
  modifyClauseMap (M.delete literal . M.delete (complement literal))

  unassigned <- State.gets unassignedLiterals

  let implies antecedent = (antecedent, antecedent `S.intersection` unassigned)

      implications = implies <$> toList propagated_clauses

      is_unit = (1==) . length . snd
      is_conflict = null . snd

  case find is_conflict implications of
    Just (antecedent, _) ->
      return $ Left antecedent
    Nothing -> do
      let units = second S.findMin <$> filter is_unit implications
      return $ Right units

propagateAll :: Ord a => [Literal a] -> State' a (Trail a, Maybe (Clause a))
propagateAll [] = return ([], Nothing)
propagateAll (literal:literals) = do
  result <- propagate literal
  case result of
    Left conflict -> return ([], Just conflict)
    Right trail -> do
      (trail', maybe_conflict) <- propagateAll (literals <> fmap snd trail)
      return (trail <> trail', maybe_conflict)

-- TODO: what if resolvent is tautology?
resolvent :: Ord a => Literal a -> Clause a -> Clause a -> Clause a
resolvent literal clause1 clause2 =
    S.delete (complement literal)
  $ S.delete literal
  $ S.union clause1 clause2

-- TODO: is it possible that no asserting clause is found?
learnClause :: forall a. Ord a => Clause a -> Trail a -> Maybe (Clause a)
learnClause conflict trail = find is_asserting $ scanl resolve conflict trail
  where
    resolve :: Ord a => Clause a -> (Clause a, Literal a) -> Clause a
    resolve clause1 (clause2, literal) =
      resolvent literal clause1 clause2

    trail_vars :: S.Set a
    trail_vars = S.fromList $ variableName . snd <$> trail

    is_asserting :: Clause a -> Bool
    is_asserting clause =
      length (trail_vars `S.intersection` S.map variableName clause) == 1

{-
decide :: Ord a => State' a (Maybe [Literal a])
decide = do
  clause_map <- State.gets snd

  let -- TODO: pick smarter
      pick_literal :: ClauseMap a -> Maybe (Literal a)
      pick_literal = S.lookupMin . M.keysSet

      literal = pick_literal clause_map

  case pick_literal clause_map of
    Nothing -> return $ Just [] -- all variables assigned => SAT
    Just literal -> do
      (trail, maybe_conflict) <- propagateAll [literal]

      case maybe_conflict of
        Nothing       -> do
          result <- decide
          case result of
            Just literals -> -- no conflict => SAT
              return $ Just $ complement literal : literals 
            Nothing -> do
              -- TODO: backtracking
              _
        Just conflict ->
          case learnClause conflict trail of
            Nothing -> error "can this happen?"
            Just conflict_clause -> do
              State.modify (second $ insertClauseMap conflict_clause)
              return Nothing
-}

isSatisfied :: StateData a -> Bool
isSatisfied = null . unassignedLiterals

step :: StateData a -> State' a (Maybe (S.Set (Literal a)))
step state
  | is_satisfied = _
  | has_conflict state = _
  | otherwise = try_literal
  where
    is_satisfied = null $ unassignedLiterals $ state

    has_conflict = _

    try_literal = do
      -- TODO: pick smarter
      let literal = S.findMin $ unassignedLiterals $ state
      _

-- getAssignment :: StateData a -> Assignment a
-- getAssignment

sat :: Ord a => CNF a -> Maybe (Assignment a)
sat formula = _
-- sat cnf = _ do 
--   let inital_state = SD cnf (clauseMap cnf)
--   literal_set <- State.gets step

--   State.evalState initial_state

--   Assign.fromLiteralList $ toList $ State.evalState (State.gets step)