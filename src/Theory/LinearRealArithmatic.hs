{-# LANGUAGE OverloadedLists #-}
module Theory.LinearRealArithmatic where

import Data.Ratio (Ratio)
import qualified Data.Vector as V
import Data.Maybe (fromMaybe)
import Control.Monad (guard)
import Data.List ((\\))

-- [a,b,c,d] :<=> (a*x + b*y + c*z + d <= 0)
type Constraint = V.Vector (Ratio Integer)

constraints :: [Constraint]
constraints =
  [ [-2, 4,-5, 4 ]
  , [-4, 5, 2, 1 ]
  , [-5,-4, 0, 3 ]
  , [ 3, 2,-4, 2 ]
  , [ 1, 3, 4,-4 ]
  , [ 4, 1, 1,-5 ] ]

data Bound = Upper Constraint | Lower Constraint | UnBounded
  deriving Show

solveFor :: Int -> Constraint -> Bound
solveFor i vs
  | x > 0 = Upper $ V.imap (\j y -> if j == i then 0 else y/x) vs
  | x < 0 = Lower $ V.imap (\j y -> if j == i then 0 else -y/x) vs
  | otherwise = UnBounded
  where
    x = vs V.! i

partitionByBound :: [Bound] -> ([Constraint], [Constraint])
partitionByBound []     = ([], [])
partitionByBound (b:bs) =
  case b of
    Lower l -> (l:ls, us)
      where (ls, us) = partitionByBound bs
    Upper u -> (ls, u:us)
      where (ls, us) = partitionByBound bs
    UnBounded -> partitionByBound bs

hasNonZeroVars :: Constraint -> Bool
hasNonZeroVars vs = foldl go 0 vs > 1
  where
    go sum x
      | x == 0    = sum
      | otherwise = sum + 1

fourierMotzkin :: [Constraint] -> [Constraint]
fourierMotzkin = go 0
  where
    go :: Int -> [Constraint] -> [Constraint]
    go i constraints =
      if any hasNonZeroVars constraints then
        let bounds = solveFor i <$> constraints
            (lowers, uppers) = partitionByBound bounds
            new_constraints = [ V.zipWith (+) l u | l <- lowers, u <- uppers ]
        in  new_constraints <> go (i+1) new_constraints
      else
        []

linearDependent :: Constraint -> Constraint -> Bool
linearDependent vs ws = coeff /= 0 && V.map (* coeff) vs == ws
  where
    div' x y
      | y == 0    = 0
      | otherwise = x/y

    coeff =
      fromMaybe 0 $ V.find (/=0) $ V.zipWith div' ws vs

f :: [Constraint]
f = do
  let cs' = filter hasNonZeroVars $ fourierMotzkin constraints
      cs = cs' -- <> constraints
  c1 <- cs
  guard (not (any (linearDependent c1) (cs \\ [c1])))
  -- return (V.map realToFrac c1) -- , V.map realToFrac c2]
  return c1 -- , V.map realToFrac c2]

----------------------------------------------------

-- simplexStep :: 

{-

data Term = 
    Var (Ratio Integer) Int    -- variable with rational coefficient
  | Const (Ratio Integer)      -- constant rational value
  | Add Term Term              -- sum of terms

data Atom = Leq Term Term

type Constraint' = V.Vector (Ratio Integer)

variables :: Term -> [Int]
variables (Var _ v) = [v]
variables (Const _) = []
variables (Add t1 t2) = 
  variables t1 <> variables t2

toConstraint :: Atom -> Constraint'
toConstraint (Leq t1 t2) = V.generate vector_size go
  where
    vector_size = 1 + maximum (variables t1 <> variables t2)

    go :: Int -> Ratio Integer
    go i = undefined

-}
