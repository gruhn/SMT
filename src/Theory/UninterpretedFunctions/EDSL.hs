{-| 
  Simple embedded domain specific language (eDSL) to conveniently write 
	constraints in GHCi.
-}
module Theory.UninterpretedFunctions.EDSL () where

import qualified SAT.CDCL

import Prelude hiding ((>=), (/=), (<), (==), const)
import Theory.UninterpretedFunctions (FuncTerm(..), Equation (Equals))
import Expression (Expr (Atom, Not), conjunct, disjunct, (/\), (\/))
import qualified CNF
import Theory (Assignment, SolverResult)

sat :: Expr Equation -> SolverResult Equation Bool
sat expr = SAT.CDCL.sat $ CNF.conjunctiveNormalForm expr

const :: Show a => a -> FuncTerm
const a = FuncTerm (show a) []

x1 = const "x1"
x2 = const "x2"
x3 = const "x3"
x4 = const "x4"
x5 = const "x5"
x6 = const "x6"
x7 = const "x7"
x8 = const "x8"
x9 = const "x9"

var :: (Int, Int) -> FuncTerm
var = const

(==) :: FuncTerm -> FuncTerm -> Expr Equation
(==) t1 t2 = Atom (t1 `Equals` t2)

(/=) :: FuncTerm -> FuncTerm -> Expr Equation
(/=) t1 t2 = Not (t1 == t2)

(<) :: FuncTerm -> FuncTerm -> Expr Equation
(<) t1 t2 = Atom $ FuncTerm "lessThan" [t1, t2] `Equals` const True

(>=) :: FuncTerm -> FuncTerm -> Expr Equation
(>=) t1 t2 = Atom $ FuncTerm "lessThan" [t1, t2] `Equals` const False

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
caseStudyGameUnequal :: Expr Equation
caseStudyGameUnequal =
  rules_for_grid 4
    /\ var (1, 1) == const 3
    /\ var (4, 1) == const 1
    /\ var (1, 3) < var (1, 2)
    /\ var (2, 4) < var (1, 4)
    /\ var (2, 2) < var (2, 3)
    /\ var (2, 4) < var (2, 3)
    /\ var (4, 4) < var (4, 3)
  where
    rules_for_grid :: Int -> Expr Equation
    rules_for_grid n =
      cells_contain_at_leat_one_number
        /\ no_duplicate_rows
        /\ no_duplicate_cols
        /\ less_than_holds
        /\ less_than_does_not_hold
      where
        cells_contain_at_leat_one_number = conjunct $ do
          row <- [1 .. n]
          col <- [1 .. n]
          return $ disjunct $ do
            num <- [1 .. n]
            return $ var (row, col) == const num

        no_duplicate_rows = conjunct $ do
          row <- [1 .. n]
          col1 <- [1 .. n]
          col2 <- [col1 + 1 .. n]
          return $ var (row, col1) /= var (row, col2)

        no_duplicate_cols = conjunct $ do
          col <- [1 .. n]
          row1 <- [1 .. n]
          row2 <- [row1 + 1 .. n]
          return $ var (row1, col) /= var (row2, col)

        less_than_holds = conjunct $ do
          a <- [1 .. n]
          b <- [a + 1 .. n]
          return $ const a < const b

        less_than_does_not_hold = conjunct $ do
          a <- [1 .. n]
          b <- [a .. n]
          return $ const b >= const a
