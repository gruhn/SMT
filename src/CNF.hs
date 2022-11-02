{-# LANGUAGE ScopedTypeVariables #-}
module CNF where

import Expression (Atom (..), Expr (..))
import qualified Data.Set as S
import Utils (fixpoint)
import Data.Foldable (toList)
import qualified Data.Map as M

data Literal a = Pos a | Neg a
  deriving (Eq, Ord, Show)

instance Functor Literal where
  fmap f (Pos a) = Pos (f a)
  fmap f (Neg a) = Neg (f a)

type Clause a = S.Set (Literal a)

type CNF a = S.Set (Clause a)

variableName :: Literal a -> a
variableName (Pos name) = name
variableName (Neg name) = name

complement :: Literal a -> Literal a
complement (Pos name) = Neg name
complement (Neg name) = Pos name

-- substitute syntax sugar, i.e. implication and equivalence operators, with and/or/not
desugar :: Expr a -> Expr a
desugar (e1 `Impl` e2)  = Not e1 `Or` e2
desugar (e1 `Equiv` e2) = desugar (e1 `Impl` e2) `And` desugar (e2 `Impl` e1)
desugar e = e

negationNormalForm :: Expr a -> Expr a
negationNormalForm = go_id
  where
    go_id :: Expr a -> Expr a
    go_id expr = case expr of
      Not e         -> go_not e
      Atom e        -> Atom e
      e1 `And` e2   -> go_id e1 `And`   go_id e2
      e1 `Or` e2    -> go_id e1 `Or`    go_id e2
      impl_or_equiv -> go_id (desugar impl_or_equiv)

    go_not :: Expr a -> Expr a
    go_not expr = case expr of
      Not e         -> go_id e
      Atom e        -> Not (Atom e)
      -- DeMorgan rules:
      e1 `And` e2   -> go_not e1 `Or`   go_not e2
      e1 `Or` e2    -> go_not e1 `And`    go_not e2
      impl_or_equiv -> go_not (desugar impl_or_equiv)

-- Transforming a formula into CNF might take exponential time and space.
-- However, the Tseytin encoding of a formula can be turned into CNF in
-- linear time and space (nested equivalences still blow up though) at the 
-- cost of introducing additional variables. Any satisfiing assignment to
-- the Tseytin encoding also satifies the original formula.
tseytin :: Expr String -> Expr String
tseytin = foldr And (var 1) . snd . go 1 . fmap escape
  where
    var i = Atom $ V $ 'h' : show i

    -- If expr already contains variables named h* then rename
    -- them to avoid collision with the newly added variables.
    escape ('h':rest) = "hh" <> rest
    escape var = var

    go :: Int -> Expr String -> (Int, [Expr String])
    go i expr = case expr of
      Atom at -> (i, [Atom at])
      Not (Atom at) -> (i, [var i `Equiv` Not (Atom at)])
      Not ex -> (j, eq : sub_ex)
        where
          eq = Equiv (var i) $ Not (var $ i+1)
          (j, sub_ex) = go (i+1) ex
      And ex1 ex2   -> go_binary i And ex1 ex2
      Or ex1 ex2    -> go_binary i Or ex1 ex2
      Impl ex1 ex2  -> go_binary i Impl ex1 ex2
      Equiv ex1 ex2 -> go_binary i Equiv ex1 ex2

    go_binary :: Int -> (Expr String -> Expr String -> Expr String) -> Expr String -> Expr String-> (Int, [Expr String])
    go_binary i op ex_l ex_r = case (ex_l, ex_r) of
      (Atom at1, Atom at2) -> (i, [eq])
        where
          eq = Equiv (var i) $ op (Atom at1) (Atom at2)
      (ex1, Atom at2) -> (j, eq : sub_ex1)
        where
          eq = Equiv (var i) $ op (var $ i+1) (Atom at2)
          (j, sub_ex1) = go (i+1) ex1
      (Atom at1, ex2) -> (j, eq : sub_ex2)
        where
          eq = Equiv (var i) $ op (Atom at1) (var $ i+1)
          (j, sub_ex2) = go (i+1) ex2
      (ex1, ex2) -> (k, eq : sub_ex1 ++ sub_ex2)
        where
          eq = Equiv (var i) $ op (var $ i+1) (var $ j+1)
          (j, sub_ex1) = go (i+1) ex1
          (k, sub_ex2) = go (j+1) ex2

conjunctiveNormalForm :: forall a. (Show a, Ord a, Eq a) => Expr a -> CNF a
conjunctiveNormalForm =
  clause_set . fixpoint distr . removeConstants . negationNormalForm
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
    clause_set (Atom T)    = S.empty
    clause_set (Atom F)    = S.singleton S.empty
    clause_set (And e1 e2) = S.union (clause_set e1) (clause_set e2)
    clause_set e           = S.singleton (clause e)

    clause :: Expr a -> Clause a
    clause (Or e1 e2) = S.union (clause e1) (clause e2)
    clause e          = S.singleton (literal e)

    literal :: Expr a -> Literal a
    literal (Atom (V var)) = Pos var
    literal (Not (Atom (V var))) = Neg var
    literal e = error "expression is not a literal"

-- Removes all boolean constants (0/1) unless the expression is 
-- a tautology/unsatisfiable then the output expression might 
-- reduce to just `Atom T` or `Atom F`.
removeConstants :: Eq a => Expr a -> Expr a
removeConstants = fixpoint go
  where
    go :: Expr a -> Expr a
    go expr = case expr of
      Atom e -> Atom e

      Not ex -> case ex of
        Atom T -> Atom F
        Atom F -> Atom T
        _ -> Not ex

      And ex_l ex_r -> case (ex_l, ex_r) of
        (Atom T, _) -> go ex_r
        (_, Atom T) -> go ex_l
        (Atom F, _) -> Atom F
        (_, Atom F) -> Atom F
        _ -> And (go ex_l) (go ex_r)

      Or ex_l ex_r -> case (ex_l, ex_r) of
        (Atom T, _) -> Atom T
        (_, Atom T) -> Atom T
        (Atom F, _) -> go ex_r
        (_, Atom F) -> go ex_l
        _ -> Or (go ex_l) (go ex_r)

      Impl ex_l ex_r -> case (ex_l, ex_r) of
        (Atom T, _) -> go ex_r
        (_, Atom T) -> Atom T
        (Atom F, _) -> Atom T
        (_, Atom F) -> Not (go ex_l)
        _ -> Impl (go ex_l) (go ex_r)

      Equiv ex_l ex_r -> case (ex_l, ex_r) of
        (Atom T, _) -> go ex_r
        (_, Atom T) -> go ex_l
        (Atom F, _) -> Not (go ex_r)
        (_, Atom F) -> Not (go ex_l)
        _ -> Equiv (go ex_l) (go ex_r)

variables :: Ord a => CNF a -> S.Set a
variables = foldMap (S.map variableName)

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