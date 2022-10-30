module ConflictDrivenClauseLearning (sat) where

import Expression (Expr)
import Assignment (Assignment)
import qualified Assignment as Assign
import CNF (CNF, Literal, Clause, complement)
import qualified Data.Map as M
import qualified Data.Set as S
import Utils (rightToMaybe)
import Control.Monad.State (State)
import qualified Control.Monad.State as State
import Data.Foldable (find)

sat :: CNF -> Maybe Assignment
sat cnf = _ -- Assign.fromLiteralList <$> rightToMaybe (cdcl cnf)

-- pickLiteral :: CNF -> Literal
-- pickLiteral = S.findMin . S.findMin

type WatchLists = M.Map Literal (S.Set Clause)

initWatchLists :: CNF -> WatchLists
initWatchLists = M.unions . S.map from_clause
  where
    singleton :: Clause -> Literal -> WatchLists
    singleton clause literal =
      M.singleton literal (S.singleton clause)

    from_clause :: Clause -> WatchLists
    from_clause clause =
      M.unionsWith S.union $ S.map (singleton clause) $ S.take 2 clause

data StateFields = StateFields
  { watchLists     :: WatchLists
  , varsUnassigned :: M.Map Int String
  , assignedLiterals :: S.Set Literal
  , conflictCount  :: Int
  }

type State' = State StateFields

pickVariable :: State' (Maybe String)
pickVariable = do
  state <- get
  case M.maxView (varsUnassigned state) of
    Nothing -> Nothing
    Just (var, rest) -> do
      put $ state { varsUnassigned = rest }
      return var

watchedClausesOf :: Literal -> WatchLists -> Clause
watchedClausesOf = M.findWithDefault S.empty

secondWatchLiteralOf :: Literal -> Clause -> WatchLists -> Literal
secondWatchLiteralOf first_literal clause =
    S.findMin 
  . S.delete first_literal 
  . M.keysSet 
  . M.filter (clause `elem`)

propagateIn :: Literal -> Clause -> State' ()
propagateIn watch_literal1 clause = do
  watch_literal2 <- State.gets (secondWatchLiteralOf watch_literal1 clause . watchLists)
  assigned_literals <- State.gets assignedLiterals
  vars_unassigned <- State.gets varsUnassigned

  let other_clause_literals = S.delete watch_literal2 $ S.delete watch_literal1 $ clause

      false_literals            = S.map complement assigned_literals
      other_clause_literals     = S.delete watch_literal1 $ S.delete watch_literal2 $ clause
      non_false_clause_literals = other_clause_literals S.\\ false_literals

  if watch_literal2 `elem` assigned_literals then
    return () -- clause is satisfied
  else if not $ null non_false_clause_literals then do
    let watch_literal1' = S.findMin non_false_clause_literals
    return () -- conflict!
  else 



  if null other_clause_literals then
    if watch_literal2 `elem` vars_assigned then
      return () -- clause satisfied
  else if (complement watch_literal2) `elem` vars_assigned then
    return () -- 
  else if null other_clause_literals then
    return 


propagate :: Literal -> State' ()
propagate literal = do
  watched_clauses <- watchedClausesOf literal
  foldrM propagateIn literal


decide :: State' Bool
decide state = do
  maybe_var <- pickVariable
  case maybe_var of
    Nothing  -> return True -- all variables assigned => SAT!
    Just var -> do
      result <- propagate (Neg var)
      return _
      -- result <- propagate (Pos var)




-- propagate :: CNF -> ([Literal], CNF)
-- propagate = go 
--   where
--     is_unit_clause clause = S.size clause == 1
--     go :: CNF -> ([Literal], CNF)
--     go cnf = case find is_unit_clause cnf of
--       Nothing          -> ([], cnf)
--       Just unit_clause -> _
--         where

-- type ImplGraph = String

-- type State' = State ImplGraph

-- pickLiteral :: CNF -> State' Literal
-- pickLiteral = return . S.findMin . S.findMin

-- extractUnitClause :: CNF -> Maybe (Literal, CNF)
-- extractUnitClause cnf = find isUnitClause cnf >>= extract
--   where
--     is_unit_clause :: Clause -> Bool
--     is_unit_clause clause = S.size clause == 1

--     extract :: Clause -> (Literal, CNF)
--     extract unit_clause = (S.findMin unit_clause, S.delete unit_clause cnf)

-- propagate :: CNF -> State ImplGraph (Maybe [Literal])
-- propagate cnf = case extractUnitClause cnf of 
--   Nothing      -> decide cnf
--   Just literal -> do
--     -- TODO: add variable

-- decide :: CNF -> State ImplGraph (Maybe [Literal])
-- decide cnf = do
--   literal <- pickLiteral cnf

--   -- add literal to graph
--   let cnf' = _

--   result <- propagate cnf'

--   case result of
--     Just literals -> return $ Just $ literal:literals
--     Nothing       -> do
--       -- TODO analyse conflict
--       return undefined

-- analyseConflict :: State' (Maybe Clause)
-- analyseConflict = undefined


-- propagate :: Literal -> State' -> State'
-- propagate literal state = _
--   where
--     watched_clauses = M.findWithDefault S.empty literal (watchLists state)

--     literals_watched_in :: Clause -> (Literal, Literal)
--     literals_watched_in clause = 

--     go :: Clause -> 

    -- go (Neg var) 
    -- go (Pos var) 

  --   go :: CNF -> State [Literal] CNF
  --   go cnf = do
  --     let literal = pickLiteral cnf


-- cdcl cnf = go (State' watch_lists _ 0)
--   where
--     watch_lists = initWatchLists cnf
--     go :: State' -> State'
--     go = 

-- propagate :: Literal -> State' -> State'
-- propagate literal state = _
--   where
--     watched_clauses = M.findWithDefault S.empty literal $ watchLists state

{-
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
      | null cnf     = Right []   -- derived empty clause set -> formula is satisfiable
      | any null cnf = Left []    -- derived empty clause     -> formula is unsatifiable
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


-}
