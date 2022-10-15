module CNF where

import Expr (Atom (..), Expr (..), rename)
import qualified Data.Set as S
import Utils (fixpoint)

data Literal = Pos String | Neg String
  deriving (Eq, Ord, Show)

type Clause = S.Set Literal

type CNF = S.Set Clause

variableName :: Literal -> String
variableName (Pos name) = name
variableName (Neg name) = name

-- substitute syntax sugar, i.e. implication and equivalence operators, with and/or/not
desugar :: Expr -> Expr
desugar (e1 `Impl` e2)  = Not e1 `Or` e2
desugar (e1 `Equiv` e2) = desugar (e1 `Impl` e2) `And` desugar (e2 `Impl` e1)
desugar e = e

negationNormalForm :: Expr -> Expr
negationNormalForm = go_id
  where
    go_id :: Expr -> Expr
    go_id expr = case expr of
      Not e         -> go_not e
      Atom e        -> Atom e
      e1 `And` e2   -> go_id e1 `And`   go_id e2
      e1 `Or` e2    -> go_id e1 `Or`    go_id e2
      impl_or_equiv -> go_id (desugar impl_or_equiv)

    go_not :: Expr -> Expr
    go_not expr = case expr of
      Not e         -> go_id e
      Atom e        -> Not (Atom e)
      -- DeMorgan rules:
      e1 `And` e2   -> go_not e1 `Or`   go_not e2
      e1 `Or` e2    -> go_not e1 `And`    go_not e2
      impl_or_equiv -> go_not (desugar impl_or_equiv)

-- The Tseytin transformation turns a formula into an equivalent
-- formula that in turn can be transformed into CNF in linear space
-- at the cost of adding new variables.
tseytin :: Expr -> Expr
tseytin = foldr And (var 1) . trd . go 0 . rename escape
  where
    trd (_,_,x) = x

    var i = Atom $ V $ 'h' : show i

    -- If expr already contains variables named h* then rename
    -- them to avoid collision with the newly added variables.
    escape ('h':rest) = "hh" <> rest
    escape var = var

    go :: Int -> Expr -> (Int, Expr, [Expr])
    go i expr = case expr of
      Atom at -> (i, Atom at, [])
      Not ex -> (j, var i, equiv : sub_ex)
        where
          (j, ex', sub_ex) = go (i+1) ex
          equiv = Equiv (var i) (Not ex')
      And ex1 ex2 -> (k, var i, equiv : sub_ex1 ++ sub_ex2)
        where
          (j, ex1', sub_ex1) = go (i+1) ex1
          (k, ex2', sub_ex2) = go j ex1
          equiv = Equiv (var i) (And ex1' ex2')
      Or ex1 ex2 -> (k, var i, equiv : sub_ex1 ++ sub_ex2)
        where 
          (j, ex1', sub_ex1) = go (i+1) ex1
          (k, ex2', sub_ex2) = go j ex2
          equiv = Equiv (var i) (Or ex1' ex2')
      Impl ex1 ex2 -> (k, var i, equiv : sub_ex1 ++ sub_ex2)
        where
          (j, ex1', sub_ex1) = go (i+1) ex1
          (k, ex2', sub_ex2) = go j ex2
          equiv = Equiv (var i) (Impl ex1' ex2')
      Equiv ex1 ex2 -> (k, var i, equiv : sub_ex1 ++ sub_ex2)
        where
          (j, ex1', sub_ex1) = go (i+1) ex1
          (k, ex2', sub_ex2) = go j ex2
          equiv = Equiv (var i) (Equiv ex1' ex2')

conjunctiveNormalForm :: Expr -> CNF
conjunctiveNormalForm = 
  clause_set . fixpoint distr . removeConstants . negationNormalForm
  where
    -- Apply distributive property to drag `And` constructors 
    -- outward and push `Or` constructors inward. 
    distr :: Expr -> Expr
    distr (Or e1 (And e2 e3)) = And (distr $ Or e1 e2) (distr $ Or e1 e3)
    distr (Or (And e1 e2) e3) = And (distr $ Or e1 e3) (distr $ Or e2 e3)
    distr (Or e1 e2)          = Or  (distr e1) (distr e2)
    distr (And e1 e2)         = And (distr e1) (distr e2)
    distr e                   = e

    clause_set (Atom T)    = S.empty
    clause_set (Atom F)    = S.singleton S.empty
    clause_set (And e1 e2) = S.union (clause_set e1) (clause_set e2)
    clause_set e           = S.singleton (clause e)

    clause (Or e1 e2) = S.union (clause e1) (clause e2)
    clause e          = S.singleton (literal e)

    literal (Atom (V var)) = Pos var
    literal (Not (Atom (V var))) = Neg var
    literal e = error $ "expression " <> show e <> " is not a literal"

-- Removes all boolean constants (0/1) unless the expression is 
-- a tautology/unsatisfiable then the output expression might 
-- reduce to just `Atom T` or `Atom F`.
removeConstants :: Expr -> Expr
removeConstants = fixpoint go
  where
    go :: Expr -> Expr
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

variables :: CNF -> S.Set String
variables = foldMap (S.map variableName)