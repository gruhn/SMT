{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
module CNF where

import Expression (Expr (..), negationNormalForm, eliminateConstants)
import qualified Data.Set as S
import Utils (fixpoint)
import Data.Foldable (toList)
import qualified Data.Map as M

data Literal a = Pos a | Neg a
  deriving (Eq, Ord, Show)

instance Functor Literal where
  fmap f (Pos a) = Pos (f a)
  fmap f (Neg a) = Neg (f a)

instance Foldable Literal where
  foldr f b (Pos a) = f a b
  foldr f b (Neg a) = f a b

instance Traversable Literal where
  traverse f (Pos a) = Pos <$> f a
  traverse f (Neg a) = Neg <$> f a

type Clause a = S.Set (Literal a)

type CNF a = S.Set (Clause a)

data WithAux a = AuxVar Int | Var a
  deriving (Show, Ord, Eq)

getVariable :: Literal a -> a
getVariable (Pos name) = name
getVariable (Neg name) = name

complement :: Literal a -> Literal a
complement (Pos name) = Neg name
complement (Neg name) = Pos name

-- Partition literals based on polarity, i.e. collect all positive and all negative 
-- literals and return as separate sets.
polarityPartition :: Ord a => CNF a -> (S.Set a, S.Set a)
polarityPartition cnf = (positives, negatives)
  where
    literals = toList $ S.unions $ toList cnf

    positives = S.fromList $ literals >>= \case 
      Pos a -> [a]
      Neg _ -> []

    negatives = S.fromList $ literals >>= \case 
      Neg a -> [a]
      Pos _ -> []

-- Transforming a formula into CNF might take exponential time and space.
-- However, the Tseytin encoding of a formula can be turned into CNF in
-- linear time and space (nested equivalences still blow up though) at the 
-- cost of introducing additional variables. Any satisfying assignment to
-- the Tseytin encoding also satifies the original formula.
tseytin :: Eq a => Expr a -> Expr (WithAux a)
tseytin = foldr And (aux_var 1) . snd . go 1 . eliminateConstants
  where
    -- To avoid naming collisions, use separate namespace for original varables 
    -- and auxiliary variables 
    aux_var i = Atom (AuxVar i)
    var atom = Atom (Var atom)

    go :: Int -> Expr a -> (Int, [Expr (WithAux a)])
    go i expr = case expr of
      T       -> (i, [T])
      F       -> (i, [F])
      Atom at -> (i, [var at])
      Not (Atom at) -> (i, [aux_var i `Equiv` Not (var at)])
      Not ex -> 
        let eq = aux_var i `Equiv` Not (aux_var $ i+1)
            (j, sub_ex) = go (i+1) ex
        in  (j, eq : sub_ex)
      And ex1 ex2   -> go_binary i And ex1 ex2
      Or ex1 ex2    -> go_binary i Or ex1 ex2
      Impl ex1 ex2  -> go_binary i Impl ex1 ex2
      Equiv ex1 ex2 -> go_binary i Equiv ex1 ex2

    go_binary :: Int 
              -> (Expr (WithAux a) -> Expr (WithAux a) -> Expr (WithAux a)) 
              -> Expr a
              -> Expr a
              -> (Int, [Expr (WithAux a)])
    go_binary i op ex_l ex_r = case (ex_l, ex_r) of
      (Atom at1, Atom at2) ->
        let eq = aux_var i `Equiv` op (var at1) (var at2)
        in  (i, [eq])
      (ex1, Atom at2) -> 
        let eq = aux_var i `Equiv` op (aux_var $ i+1) (var at2)
            (j, sub_ex1) = go (i+1) ex1
        in (j, eq : sub_ex1)
      (Atom at1, ex2) -> 
        let eq = aux_var i `Equiv` op (var at1) (aux_var $ i+1)
            (j, sub_ex2) = go (i+1) ex2
        in  (j, eq : sub_ex2)
      (ex1, ex2) -> 
        let eq = aux_var i `Equiv` op (aux_var $ i+1) (aux_var $ j+1)
            (j, sub_ex1) = go (i+1) ex1
            (k, sub_ex2) = go (j+1) ex2
        in  (k, eq : sub_ex1 ++ sub_ex2)

conjunctiveNormalForm :: forall a. (Show a, Ord a, Eq a) => Expr a -> CNF a
conjunctiveNormalForm =
  clause_set . fixpoint distr . negationNormalForm
  where
    -- Apply distributive property to drag `And` constructors 
    -- outward and push `Or` constructors inward. 
    distr :: Expr a -> Expr a
    distr (Or e1 (And e2 e3)) = And (distr $ Or e1 e2) (distr $ Or e1 e3)
    distr (Or (And e1 e2) e3) = And (distr $ Or e1 e3) (distr $ Or e2 e3)
    distr (Or e1 e2)          = Or  (distr e1) (distr e2)
    distr (And e1 e2)         = And (distr e1) (distr e2)
    distr e                   = e

    clause_set :: Expr a -> CNF a
    clause_set (And e1 e2) = S.union (clause_set e1) (clause_set e2)
    clause_set e           = S.singleton (clause e)

    clause :: Expr a -> Clause a
    clause (Or e1 e2) = S.union (clause e1) (clause e2)
    clause e          = S.singleton (literal e)

    literal :: Expr a -> Literal a
    literal (Atom atom) = Pos atom
    literal (Not (Atom atom)) = Neg atom
    literal _ = undefined

variables :: Ord a => CNF a -> S.Set a
variables = foldMap (S.map getVariable)

-- Convert CNF formula to String in DIMACS format. See:
-- https://jix.github.io/varisat/manual/0.2.0/formats/dimacs.html#dimacs-cnf
showDIMACS :: Ord a => CNF a -> String
showDIMACS cnf = unlines (header_line : clause_lines)
  where
    vars_indexed = M.fromList (zip vars indices)
      where
        vars = toList $ variables cnf
        indices = show <$> [1 ..]

    clause_count = length cnf
    var_count    = length vars_indexed

    header_line = "p cnf " <> show var_count <> " " <> show clause_count

    show_var (Pos name) = vars_indexed M.! name
    show_var (Neg name) = "-" <> vars_indexed M.! name

    show_clause clause = unwords (show_var <$> toList clause)

    clause_lines = (<> " 0") . show_clause <$> toList cnf