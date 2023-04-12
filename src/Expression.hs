{-# LANGUAGE FlexibleInstances #-}
module Expression
  ( Expr(..)
  , atoms
  , conjunct
  , disjunct
  , negationNormalForm
  , eliminateConstants
  , subExpressions
  , (/\)
  , (\/)
  , (==>)
  , (<==>)
  ) where

import qualified Data.Set as S
import Utils ( fixpoint )

data Expr a =
    T
  | F
  | Atom a
  | Not (Expr a)
  | And (Expr a) (Expr a)
  | Or (Expr a) (Expr a)
  deriving Eq

instance Functor Expr where
  fmap f expr = case expr of
    T            -> T
    F            -> F
    Atom at      -> Atom (f at)
    Not  ex      -> Not (fmap f ex)
    And   ex ex' -> And (fmap f ex) (fmap f ex')
    Or    ex ex' -> Or (fmap f ex) (fmap f ex')

subExpressions :: Expr a -> [Expr a]
subExpressions expr = expr : case expr of
  T            -> []
  F            -> []
  Atom at      -> []
  Not  ex      -> subExpressions ex
  And   ex ex' -> subExpressions ex <> subExpressions ex'
  Or    ex ex' -> subExpressions ex <> subExpressions ex'

atoms :: Expr a -> [a]
atoms expr = do
  ex <- subExpressions expr
  case ex of
    Atom at -> [at]
    _       -> []

conjunct :: [Expr a] -> Expr a
conjunct []       = T
conjunct (e : es) = foldr And e es

disjunct :: [Expr a] -> Expr a
disjunct []       = F
disjunct (e : es) = foldr Or e es

negationNormalForm :: Expr a -> Expr a
negationNormalForm = go_id
 where
  go_id :: Expr a -> Expr a
  go_id expr = case expr of
    T             -> T
    F             -> F
    Not  e        -> go_not e
    Atom e        -> Atom e
    e1 `And` e2   -> go_id e1 `And` go_id e2
    e1 `Or`  e2   -> go_id e1 `Or` go_id e2

  go_not :: Expr a -> Expr a
  go_not expr = case expr of
    T             -> F
    F             -> T
    Not  e        -> go_id e
    Atom e        -> Not (Atom e)
    -- DeMorgan rules:
    e1 `And` e2   -> go_not e1 `Or` go_not e2
    e1 `Or`  e2   -> go_not e1 `And` go_not e2

-- Removes all boolean constants (0/1) unless the expression is 
-- a tautology/unsatisfiable then the output expression might 
-- reduce to just `Atom T` or `Atom F`.
eliminateConstants :: Eq a => Expr a -> Expr a
eliminateConstants = fixpoint go
 where
  go :: Expr a -> Expr a
  go expr = case expr of
    T       -> T
    F       -> F
    Atom e  -> Atom e

    Not  ex -> case ex of
      T -> F
      F -> T
      _ -> Not ex

    And ex_l ex_r -> case (ex_l, ex_r) of
      (T, _) -> go ex_r
      (_, T) -> go ex_l
      (F, _) -> F
      (_, F) -> F
      _      -> And (go ex_l) (go ex_r)

    Or ex_l ex_r -> case (ex_l, ex_r) of
      (T, _) -> T
      (_, T) -> T
      (F, _) -> go ex_r
      (_, F) -> go ex_l
      _      -> Or (go ex_l) (go ex_r)

infixl 5 /\

(/\) :: Expr a -> Expr a -> Expr a
(/\) = And

infixl 5 \/

(\/) :: Expr a -> Expr a -> Expr a
(\/) = Or

infixr 4 ==>

(==>) :: Expr a -> Expr a -> Expr a
(==>) expr expr' = Not expr `Or` expr'

infixl 3 <==>

(<==>) :: Expr a -> Expr a -> Expr a
(<==>) expr expr' = expr ==> expr' /\ expr' ==> expr
