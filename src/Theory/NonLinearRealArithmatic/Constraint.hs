
module Theory.NonLinearRealArithmatic.Constraint 
  ( Constraint
  , ConstraintRelation(..)
  , varsIn
  ) where

import Theory.NonLinearRealArithmatic.Polynomial (Polynomial)
import Theory.NonLinearRealArithmatic.Expr (Var)
import qualified Theory.NonLinearRealArithmatic.Polynomial as Polynomial
import Data.Containers.ListUtils (nubOrd)

data ConstraintRelation = LessThan | LessEquals | Equals | GreaterEquals | GreaterThan
  deriving (Eq, Show)

{-| 
  Assuming the expression forms the left-hand-side of the relation, 
  while the right-hand-side is always zero, e.g. `x + 3*y - 10 <= 0`
-}
type Constraint a = (ConstraintRelation, Polynomial a)

varsIn :: [Constraint a] -> [Var]
varsIn = nubOrd . concatMap (Polynomial.varsIn . snd)
