module SAT where

import qualified Data.Set as S
import Expr (Expr(..), Atom(..))
import CNF (CNF, tseytin, conjunctiveNormalForm, variables, Literal (..), Clause)
import Data.Foldable (toList)
import Control.Monad (guard)
import Utils (fixpoint)

dpll :: CNF -> Bool
dpll = undefined

eval :: (String -> Bool) -> Expr -> Bool
eval interpret = go
  where
    go :: Expr -> Bool
    go formula = case formula of
      Atom (V var)  -> interpret var
      Atom T        -> True
      Atom F        -> False
      Not p         -> not (go p)
      p1 `And` p2   -> go p1 && go p2
      p1 `Or` p2    -> go p1 || go p2
      p1 `Impl` p2  -> go p1 <= go p2
      p1 `Equiv` p2 -> go p1 == go p2

linearResolution :: CNF -> Bool
linearResolution cnf
  -- empty formula is a tautology
  | null cnf  = True
  -- TODO: how to pick initial resolvent in linear resolution?
  | otherwise = not $ any can_derive_empty_clause_from cnf
  where
    negate :: Literal -> Literal
    negate (Pos var) = Neg var
    negate (Neg var) = Pos var

    resolve_with :: Clause -> Clause -> Literal -> Clause
    resolve_with c1 c2 lit =
      S.delete lit c1 `S.union` S.delete (negate lit) c2

    step :: (Clause, CNF) -> (Clause, CNF)
    step (resolvent, clauses)
      -- empty clause is derivable => formula is unsatifiable
      | null resolvent       = (resolvent, clauses)
      | null next_resolvents = (resolvent, clauses)
      | otherwise            = (head next_resolvents, S.insert (head next_resolvents) clauses)
      where
        next_resolvents :: [Clause]
        next_resolvents = do
          literal <- toList resolvent
          clause  <- toList clauses
          guard (negate literal `S.member` clause)
          return $ resolve_with resolvent clause literal

    can_derive_empty_clause_from :: Clause -> Bool
    can_derive_empty_clause_from initial_resolvent =
      null . fst $ fixpoint step (initial_resolvent, cnf)

satLR :: Expr -> Bool
satLR = linearResolution . conjunctiveNormalForm

sat :: Expr -> Maybe (String -> Bool)
sat = error "TODO: implement sat"