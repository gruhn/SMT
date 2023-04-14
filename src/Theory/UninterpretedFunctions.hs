module Theory.UninterpretedFunctions 
  ( Equation(..)
  , FuncTerm(..)
  , subTerms
  ) where

import qualified Data.Set as S
import Data.List (sort)
import qualified Data.Map as M
import Data.Maybe (fromMaybe, listToMaybe, maybeToList)
import Theory (Theory (..))
import qualified Theory
import qualified CNF
import Data.Bifunctor (bimap)
import Data.Containers.ListUtils (nubOrd)
import qualified Data.List as List
import Utils (combinations, fixpoint)
import Control.Monad (guard)
import Algorithm.Search (dijkstra)
import Data.IntMap (empty)
import Debug.Trace

-- | All terms are functions. Constants are functions with arity zero.
data FuncTerm = FuncTerm { getName :: String, getArgs :: [FuncTerm] }
  deriving (Eq, Ord)

instance Show FuncTerm where
  show (FuncTerm name [])   = name
  show (FuncTerm name args) =
    name ++ "(" ++ List.intercalate ", " (map show args) ++ ")"

data Equation = FuncTerm `Equals` FuncTerm
  deriving Show

subTerms :: FuncTerm -> [FuncTerm]
subTerms t@(FuncTerm _ args) =
  t : concatMap subTerms args

isSameFunc :: FuncTerm -> FuncTerm -> Bool
isSameFunc f1 f2 = 
     getName f1 == getName f2 
  && length (getArgs f1) == length (getArgs f2)

instance Eq Equation where
  -- Equation is symmetric so `term1 == term2` is the same equality as `term2 == term1`.
  -- This definition is helpful when making a Data.Set of Equation's so symmetic version
  -- of an equality is recognized as a duplicate and automatically discarded.
  t1 `Equals` t2 == t3 `Equals` t4 =
    sort [t1,t2] == sort [t3,t4]

instance Ord Equation where
  t1 `Equals` t2 <= t3 `Equals` t4 =
    sort [t1,t2] <= sort [t3,t4]

-- | Map from Term to equivalence class identifier.
type EquivalenceClasses = M.Map FuncTerm Int

haveSameClass :: EquivalenceClasses -> FuncTerm -> FuncTerm -> Bool
haveSameClass classes t1 t2 =
  case (M.lookup t1 classes, M.lookup t2 classes) of
    (Just c1, Just c2)   -> c1 == c2
    at_least_one_nothing -> error "given terms are not in any equivalence class"

-- | Rename each occurance of the second given class to the first given class.
mergeClasses :: Int -> Int -> EquivalenceClasses -> EquivalenceClasses
mergeClasses class1 class2 = M.map (\c -> if c == class2 then class1 else c)

-- | Merge classes of the two terms mentioned in the given equation. 
mergeClassesBy :: Equation -> EquivalenceClasses -> EquivalenceClasses
mergeClassesBy (t1 `Equals` t2) classes =
  case (M.lookup t1 classes, M.lookup t2 classes) of
    (Just c1, Just c2)   -> mergeClasses c1 c2 classes
    at_least_one_nothing -> error "given terms are not in any equivalence class"

equivalenceClasses :: [Equation] -> [Equation] -> EquivalenceClasses
equivalenceClasses equalities disequalities = 
  let
    all_terms = nubOrd $ do
      t1 `Equals` t2 <- equalities ++ disequalities
      subTerms t1 ++ subTerms t2

    -- Partition terms into equivalence classes. 
    -- Initially each term is in it's own equivalence class.
    initial_classes = M.fromList $ zip all_terms [0..]

    -- For each equality merge the classes of the two terms on the left- and right-hand-side.
    classes_with_transitivity = foldr mergeClassesBy initial_classes equalities

    -- To respect function congruence (i.e. if x=y then f(x)=f(y)) potentially more classes 
    -- need to be merged. That is, for each combination of function terms f(t1),f(t2) where 
    -- t1,t2 are in the same equivalence class, we merge the classes of f(t1) and f(t2). 
    -- Note, that function terms can also have multiple arguments. We only need to consider
    -- function terms with the same function symbol and arity.
    func_terms = List.groupBy isSameFunc all_terms

    collect_mergeable :: EquivalenceClasses -> [(Int,Int)]
    collect_mergeable classes = do
      -- pick a group of function terms with same name and arity
      func_term_group <- func_terms
      -- go through each combination of terms
      (f1, f2) <- combinations func_term_group
      -- that are not already in the same equivalence class
      let (class1, class2) = (classes M.! f1, classes M.! f2)
      guard $ class1 /= class2 
      -- if all arguments are equal, the terms themselves are equal
      guard $ and $ zipWith (haveSameClass classes) (getArgs f1) (getArgs f2)
      -- get equivalence class identifiers for the two terms.
      return (class1, class2)

    iterate_merge :: EquivalenceClasses -> EquivalenceClasses
    iterate_merge classes = 
      case collect_mergeable classes of
        []        -> classes
        mergeable -> iterate_merge (foldr (uncurry mergeClasses) classes mergeable)
    
    classes_with_congruence = iterate_merge classes_with_transitivity

  in 
    classes_with_congruence

type EqualityGraph = M.Map FuncTerm [FuncTerm]

{-| 
  Given a list of equations, constructs an undirected graph with nodes for
  each term and edges for each equality.
-}
equalityGraphFrom :: [Equation] -> EqualityGraph
equalityGraphFrom = 
  M.map nubOrd . M.fromListWith (++) . concatMap (
    \case t1 `Equals` t2 -> [ (t1, [t2]), (t2, [t1]) ]
  )

shortestPath :: FuncTerm -> FuncTerm -> EqualityGraph -> Maybe [Equation]
shortestPath from to graph = do 
  let neighbors node = M.findWithDefault [] node graph
      cost _ _ = 1

  -- Note, `path` does not include the start node by default
  (_, path) <- dijkstra neighbors cost (==to) from

  return $ zipWith Equals (from : path) path

{-|
  Given a set of equalities/disequalites literals, if possible, 
  computes a minimal subset that are in conflict. 
-}
minimalInfeasibleSubset :: [CNF.Literal Equation] -> Maybe [CNF.Literal Equation]
minimalInfeasibleSubset literals = listToMaybe $ do
  let (equalities, disequalities) = CNF.polarityPartition literals
      equality_graph = equalityGraphFrom equalities
      equivalence_classes = equivalenceClasses equalities disequalities

  -- check each disequality
  diseq@(t1 `Equals` t2) <- disequalities
  -- if the two terms are in the same equivalence class we have a conflict
  guard $ haveSameClass equivalence_classes t1 t2 
  -- there must be a path of equalities that causes the two terms to be in the 
  -- same equivalence class.
  eq_path <- maybeToList $ shortestPath t1 t2 equality_graph
  -- the disequality together with the equality path form a minimial infeasible subset.
  return $ CNF.Neg diseq : map CNF.Pos eq_path

instance Theory Equation Bool where
  solve literals = 
    case minimalInfeasibleSubset literals of
      Just min_inf_subset -> Theory.UNSAT (S.fromList min_inf_subset)
      Nothing             -> Theory.SAT empty -- (error "TODO: implement UE SAT")
  
  satisfies = error "TODO: implement UE satisfies "
