module Theory.BitVectors where

import Expression

data Term a
  = Zero
  | One
  | BitNeg (Term a)
  | BitAnd (Term a) (Term a)
  | BitOr (Term a) (Term a)
  | ShiftLeft (Term a)
  | ShiftRight (Term a)
  | Add (Term a) (Term a)
  | Subst (Term a) (Term a)
  | Mult (Term a) (Term a)
  deriving (Eq, Ord, Show)

bitBlasting :: Term a -> Expr a
bitBlasting = undefined 
