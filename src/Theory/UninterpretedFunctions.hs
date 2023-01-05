{-# LANGUAGE ScopedTypeVariables #-}
module Theory.UninterpretedFunctions where
import qualified Data.Set as S
import Data.List (sort)
import qualified Data.Map as M
import Utils (distinct)
import Data.Maybe (fromMaybe)

data Term a =
    Var a
  | Const String
  | Func String [Term a]
  deriving (Eq, Ord, Show)

data Equality a = (Term a) `Equals` (Term a)
  deriving Show

instance (Eq a, Ord a) => Eq (Equality a) where
  -- Equality is symmetric so `term1 == term2` is the same equality as `term2 == term1`.
  -- This definition is helpful when making a Data.Set of Equality's so symmetic version
  -- of an equality is recognized as a duplicate and automatically discarded.
  t1 `Equals` t2 == t3 `Equals` t4 =
    sort [t1,t2] == sort [t3,t4]

instance (Eq a, Ord a) => Ord (Equality a) where
  t1 `Equals` t2 <= t3 `Equals` t4 =
    sort [t1,t2] <= sort [t3,t4]

subTerms :: Equality a -> [Term a]
subTerms (t1 `Equals` t2) = go t1 <> go t2
  where 
    go :: Term a -> [Term a]
    go t@(Var _) = [t]
    go t@(Const _) = [t]
    go t@(Func name args) =
      t : concatMap go args

type Partition a = M.Map (Term a) Int

equivalenceClasses :: forall a. Ord a => [Equality a] -> Partition a
equivalenceClasses equalities = foldr merge initial_classes equalities
  where
    initial_classes :: Partition a
    initial_classes = M.fromList $ zip (concatMap subTerms equalities) [0..]

    merge :: Equality a -> Partition a -> Partition a
    merge (t1 `Equals` t2) classes = 
      M.insert t2 (classes M.! t1) classes

    assure_congruence = _

    implied_equalities :: Equality a -> [Equality a]
    implied_equalities eq@(t1 `Equals` t2) =
      case (t1, t2) of
        (Func f args_f, Func g args_g) ->
          if f == g && length args_f == length args_g then
            zipWith Equals args_f args_g >>= implied_equalities
          else 
            [eq]
        _ -> [eq]

{-

## Case Study: "Game Unequal"

A game similar to sudoku. Given an n-by-n grid, can the cells be filled with numbers 
from 1 to n such that there are no duplicates in any row or column?
Some cells are prefilled or have an inequality between them (clues).

An example instance looks like this:

     +---------------+
     | 3   _ > _   _ | 
     |             v |
     | _   _ < _   _ |
     |             ^ |
     | _   _   _   _ |
     |               |
     | 1   _   _ > _ |
     +---------------+

A possible solution is:

     +---------------+
     | 3   2 > 1   4 | 
     |             v |
     | 2   1 < 4   3 |
     |             ^ |
     | 4   3   2   2 |
     |               |
     | 1   4   3 > 2 |
     +---------------+

-}

caseStudyGameUnequal :: Expr (Equality (Int,Int))
caseStudyGameUnequal = 
  rules_for_grid 4
    `And` is_equal (1,1) 3
    `And` is_equal (4,1) 1
    `And` is_less_than 4 (1,3) (1,2)
    `And` is_less_than 4 (2,4) (1,4)
    `And` is_less_than 4 (2,2) (2,3)
    `And` is_less_than 4 (2,4) (2,3)
    `And` is_less_than 4 (4,4) (4,3)
  where 
    var :: Int -> Int -> UF.Term (Int,Int)
    var row col num = Atom $ UF.Var (row, col)

    is_equal :: (Int,Int) -> Int -> UF.Term (Int,Int)
    is_equal (y,x) num = var y x `UF.Equals` UF.Const (show num)

    is_less_than :: UF.Term (Int,Int) -> UF.Term (Int,Int) -> UF.Term (Int,Int)
    is_less_than t1 t2 = Func "lessThan" [t1, t2] `Equals` UF.Const "True"

    is_not_less_than :: UF.Term (Int,Int) -> UF.Term (Int,Int) -> UF.Term (Int,Int)
    is_not_less_than t1 t2 = Func "lessThan" [t1, t2] `Equals` UF.Const "False"

    rules_for_grid :: Int -> Expr (Equality (Int,Int))
    rules_for_grid n = 
            cells_contain_exactly_one_number 
      `And` no_duplicate_rows 
      `And` no_duplicate_cols
      `And` less_than_hold
      `And` less_than_does_not_hold
      where
        cells_contain_at_leat_one_number = foldr1 And $ do
          row <- [1..n]
          col <- [1..n]
          return $ foldr1 Or $ is_equal row col <$> [1..n]

        no_duplicate_rows = foldr1 And $ do
          row  <- [1..n]
          col1 <- [1..n]
          col2 <- [col1+1..n]
          return $ Not (var row col1 `Equals` var row col2)

        no_duplicate_cols = foldr1 And $ do
          col  <- [1..n]
          row1 <- [1..n]
          row2 <- [row1+1..n]
          return $ Not (var row1 col `Equals` var row2 col)

        less_than_holds = foldr1 And $ do
          a <- [1   .. n]
          b <- [a+1 .. n]
          return $ is_less_than a b

        less_than_does_not_hold = foldr1 And $ do
          a <- [1 .. n]
          b <- [a .. n]
          return $ is_not_less_than b a

    -- solutionFrom' :: Assignment (Equality (Int,Int)) -> M.Map (Int,Int) Int
    -- solutionFrom' assignment = M.fromList 
    --   $ fmap (\(row,col,val) -> ((row,col),val)) 
    --   $ M.keys 
    --   $ M.filter id assignment

