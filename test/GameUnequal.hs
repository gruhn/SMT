module GameUnequal (example, solutionFrom) where
import Expression (Expr (..))
import Control.Monad (guard)
import Assignment (Assignment)
import qualified Data.Map as M

-- A game similar to sudoku. Given an n-by-n grid, can the cells be filled with numbers 
-- from 1 to n such that there are no duplicates in any row or column?
-- Some cells are prefilled or have an inequality between them (clues).
--
-- An example instance looks like this:
--
--      +---------------+
--      | 3   _ > _   _ | 
--      |             v |
--      | _   _ < _   _ |
--      |             ^ |
--      | _   _   _   _ |
--      |               |
--      | 1   _   _ > _ |
--      +---------------+
--
-- A possible solution is:
--
--      +---------------+
--      | 3   2 > 1   4 | 
--      |             v |
--      | 2   1 < 4   3 |
--      |             ^ |
--      | 4   3   2   2 |
--      |               |
--      | 1   4   3 > 2 |
--      +---------------+
--
example :: Expr (Int,Int,Int)
example = rulesForGrid 4
  `And` isEqual (1,1) 3
  `And` isEqual (4,1) 1
  `And` isLessThan 4 (1,3) (1,2)
  `And` isLessThan 4 (2,4) (1,4)
  `And` isLessThan 4 (2,2) (2,3)
  `And` isLessThan 4 (2,4) (2,3)
  `And` isLessThan 4 (4,4) (4,3)

var :: Int -> Int -> Int -> Expr (Int,Int,Int)
var row col num = Atom (row, col, num)

isEqual :: (Int,Int) -> Int -> Expr (Int,Int,Int)
isEqual (y,x) = var y x

isLessThan :: Int -> (Int,Int) -> (Int,Int) -> Expr (Int,Int,Int)
isLessThan n (y1,x1) (y2,x2) = lower_bounds `And` upper_bounds
  where
    lower_bounds = foldr1 And $ do
      val <- [1..n]
      -- if (y1,x1) has value `val` then (y2,x2) has value in [val+1 .. n]
      return $ foldr Or (Not (var y1 x1 val)) $ var y2 x2 <$> [val+1 .. n]

    upper_bounds = foldr1 And $ do
      val <- [1..n]
      -- if (y2,x2) has value `val` then (y1,x1) has value in [1 .. val-1]
      return $ foldr Or (Not $ var y2 x2 val) $ var y1 x1 <$> [1 .. val-1]

rulesForGrid :: Int -> Expr (Int,Int,Int)
rulesForGrid n = cells_contain_exactly_one_number `And` no_duplicate_rows `And` no_duplicate_cols
  where
    cells_contain_at_leat_one_number = foldr1 And $ do
      row <- [1..n]
      col <- [1..n]
      return $ foldr1 Or $ var row col <$> [1..n]

    cells_contain_at_most_one_number = foldr1 And $ do
      row  <- [1..n]
      col  <- [1..n]
      num1 <- [1..n]
      num2 <- [1..n]
      guard (num1 /= num2)
      return $ Not (var row col num1) `Or` Not (var row col num2)

    cells_contain_exactly_one_number =
      cells_contain_at_leat_one_number `And` cells_contain_at_most_one_number

    no_duplicate_rows = foldr1 And $ do
      row  <- [1..n]
      num  <- [1..n]
      col1 <- [1..n]
      col2 <- [1..n]
      guard (col1 /= col2)
      return $ Not (var row col1 num) `Or` Not (var row col2 num)

    no_duplicate_cols = foldr1 And $ do
      col  <- [1..n]
      num  <- [1..n]
      row1 <- [1..n]
      row2 <- [1..n]
      guard (row1 /= row2)
      return $ Not (var row1 col num) `Or` Not (var row2 col num)

solutionFrom :: Assignment (Int,Int,Int) -> M.Map (Int,Int) Int
solutionFrom assignment = M.fromList 
  $ fmap (\(row,col,val) -> ((row,col),val)) 
  $ M.keys 
  $ M.filter id assignment
