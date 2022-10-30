{-# LANGUAGE ScopedTypeVariables #-}
module LinearResolution (sat) where

import CNF (conjunctiveNormalForm, CNF, Literal (..), Clause, complement)
import Expression (Expr)
import qualified Data.Set as S
import Data.Foldable (toList)
import Control.Monad (guard)
import Utils (fixpoint)
import Data.Tree (Forest, unfoldForest, Tree (rootLabel, Node), unfoldForestM)
import Debug.Trace (trace)
import Data.Function (on)
import Data.List (sortBy)
import qualified Control.Monad.State.Lazy as State

sat :: (Eq a, Ord a) => CNF a -> Bool
sat = linearResolution

linearResolution :: (Eq a, Ord a) => CNF a -> Bool
linearResolution = not . any (S.empty `elem`) . searchTree

searchTree :: forall a. Ord a => CNF a -> Forest (Clause a)
searchTree cnf = State.evalState (unfoldForestM expand $ toList cnf) cnf
  where
    resolve_with :: Clause a -> Clause a -> Literal a -> Clause a
    resolve_with c1 c2 lit =
      S.delete lit c1 `S.union` S.delete (complement lit) c2

    no_tautology :: Clause a -> Bool
    no_tautology clause = null $
      clause `S.intersection` S.map complement clause 

    next_resolvents :: Clause a -> CNF a -> [Clause a]
    next_resolvents resolvent derived_clauses = do
      literal <- toList resolvent
      clause  <- toList derived_clauses
      guard (complement literal `elem` clause) 
      let resolvent' = resolve_with resolvent clause literal
      guard (no_tautology resolvent')
      guard (resolvent' `notElem` derived_clauses) -- skip already derived clauses
      return resolvent'

    expand :: Clause a -> State.State (CNF a) (Clause a, [Clause a])
    expand resolvent = do
      State.modify (S.insert resolvent)
      derived_clauses <- State.get
      return (resolvent, next_resolvents resolvent derived_clauses)