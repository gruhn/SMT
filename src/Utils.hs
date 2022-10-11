module Utils where

fixpoint :: Eq a => (a -> a) -> a -> a
fixpoint f a
  | a == f a  = a
  | otherwise = fixpoint f (f a)