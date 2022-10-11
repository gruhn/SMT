module CNF where
import Expr (Atom (..), Expr (..))
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
      e1 `And`   e2 -> go_id e1 `And`   go_id e2
      e1 `Or`    e2 -> go_id e1 `Or`    go_id e2
      impl_or_equiv -> go_id (desugar impl_or_equiv)

    go_not :: Expr -> Expr
    go_not expr = case expr of
      Not e         -> go_id e
      Atom e        -> Not (Atom e)
      -- DeMorgan rules:
      e1 `And`   e2 -> go_not e1 `Or`   go_not e2
      e1 `Or`    e2 -> go_not e1 `And`    go_not e2
      impl_or_equiv -> go_not (desugar impl_or_equiv)

-- The Tseytin transformation turns a formula into an equivalent
-- formula that in turn can be transformed into CNF in linear space
-- at the cost of adding new variables.
tseytin :: Expr -> Expr
tseytin = foldr And (var 1) . snd . go 1
  where
    var i = Atom $ V $ 'h' : show i

    go :: Int -> Expr -> (Int, [Expr])
    go i expr = case expr of
      Atom at -> (i, [Atom at])
      Not ex -> (n, equiv : sub_ex)
        where
          equiv = Equiv (var i) (Not $ var $ i+1)
          (n, sub_ex) = go (i+1) ex
      And ex1 ex2 -> (n, equiv : sub_ex1 ++ sub_ex2)
        where
          equiv = Equiv (var i) (var (i+1) `And` var (i+2))
          (j, sub_ex1) = go (i+2) ex1
          (n, sub_ex2) = go j ex2
      Or ex1 ex2 -> (n, equiv : sub_ex1 ++ sub_ex2)
        where 
          equiv = Equiv (var i) (var (i+1) `Or` var (i+2))
          (j, sub_ex1) = go (i+2) ex1
          (n, sub_ex2) = go j ex2
      Impl ex1 ex2 -> (n, equiv : sub_ex1 ++ sub_ex2)
        where
          equiv = Equiv (var i) (var (i+1) `Impl` var (i+2))
          (j, sub_ex1) = go (i+2) ex1
          (n, sub_ex2) = go j ex2
      Equiv ex1 ex2 -> (n, equiv : sub_ex1 ++ sub_ex2)
        where
          equiv = Equiv (var i) (var (i+1) `Equiv` var (i+2))
          (j, sub_ex1) = go (i+2) ex1
          (n, sub_ex2) = go j ex2

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

    clause_set (And e1 e2) = S.union (clause_set e1) (clause_set e2)
    clause_set e           = S.singleton (clause e)

    clause (Or e1 e2) = S.union (clause e1) (clause e2)
    clause e          = S.singleton (literal e)

    literal (Atom (V var)) = Pos var
    literal (Not (Atom (V var))) = Neg var
    literal _ = undefined

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