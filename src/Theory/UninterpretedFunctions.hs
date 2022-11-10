{-# LANGUAGE ScopedTypeVariables  #-}
module Theory.UninterpretedFunctions where

import Expression (Expr (..), conjunct, negationNormalForm)
import qualified Expression as Expr
import qualified Data.Set as S
import qualified Data.Map as M
import Control.Monad ((>=>), guard)
import Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.List.NonEmpty as NE
import Data.Foldable (Foldable(toList))
import Data.Tuple (swap)
import Utils (distinct)
import Assignment (Assignment)
import CNF
import Data.List (sort)

ignoreAuxVars :: forall a. Ord a => CNF (WithAux a) -> CNF a
ignoreAuxVars = S.map ignore
  where
    get_var :: WithAux a -> [a]
    get_var (CNF.Var a) = [a]
    get_var (CNF.AuxVar _) = []

    ignore :: Clause (WithAux a) -> Clause a
    ignore clause = S.fromList $ do 
      literal <- toList clause
      traverse get_var literal

satWith :: (Expr (WithAux Equality) -> Maybe (Assignment (WithAux Equality)))
        -> Expr Equality
        -> Maybe (Assignment Equality)
satWith sat expr = 
  let 
    cnf = conjunctiveNormalForm 
        $ tseytin 
        $ encodeCongruence 
        $ negationNormalForm 
        $ expr

    e_graph = polarEqualityGraph (ignoreAuxVars cnf)

  in _

data Term = 
    Var String
  | Func String [Term]
  deriving (Eq, Ord, Show)

data Equality = E Term Term
  deriving Show

instance Eq Equality where
  -- Equality is symmetric so `term1 == term2` is the same equality as `term2 == term1`.
  -- This definition is helpful when making a Data.Set of Equality's so symmetic version
  -- of an equality is recognized as a duplicate and automatically discarded.
  E t1 t2 == E t3 t4 = 
    sort [t1,t2] == sort [t3,t4]
instance Ord Equality where
  E t1 t2 <= E t3 t4 = 
    sort [t1,t2] <= sort [t3,t4]

-- Collect the set of used function terms from a given expression and group them by name
-- and arity.
functionTerms :: Expr Equality -> M.Map (String, Int) (S.Set Term)
functionTerms = M.unionsWith S.union . fmap from_equality . Expr.atoms
  where
    from_equality :: Equality -> M.Map (String, Int) (S.Set Term)
    from_equality (E term1 term2) =
      M.unionWith S.union (from_term term1) (from_term term2)

    from_term :: Term -> M.Map (String, Int) (S.Set Term)
    from_term term@(Func name args) = 
      M.unionsWith S.union $ 
        M.singleton (name, length args) (S.singleton term) : fmap from_term args
    from_term _ = M.empty

-- Encode functional congruence into the formula, i.e.
--
--    if x = y then f(x) = f(y)
--
-- so the SAT solver has to respect it.
encodeCongruence :: Expr Equality -> Expr Equality
encodeCongruence expr = conjunct $ (expr :) $ do
  ((name, arity), term_set) <- M.toList (functionTerms expr)
  let terms = toList term_set

  term1 <- terms
  term2 <- terms
  guard (term1 /= term2)

  let get_args :: Term -> [Term]
      get_args (Func _ args) = args
      get_args _             = undefined

      all_args_equal = conjunct $ Atom <$> 
        zipWith E (get_args term1) (get_args term2)

  return $
    all_args_equal `Impl` Atom (E term1 term2)
  
type PolarEqualityGraph = S.Set (Literal Equality) 

polarEqualityGraph :: CNF Equality -> PolarEqualityGraph
polarEqualityGraph = S.unions . toList

neighbors :: Term -> PolarEqualityGraph -> [Term]
neighbors term graph = 

simpleChordFreeCycles :: PolarEqualityGraph -> [[Term]]
simpleChordFreeCycles = _

-- A graph is chordal iff every simple cycle over at least 4 different nodes has a chord.
-- Given a chord-free cycle with at least 4 nodes:
--    
--      t2--t1-----t6
--       \          |   
--        t3--t4---t5
-- 
-- connecting the neighbors of t2 leaves a chord-free cycle with one fewer node:
--
--          t1-----t6
--          /       |   
--         t3--t4--t5
--
-- Iterating this until the remaining cycle only has 3 nodes left...
--
--          t1-----t6
--            \     |   
--             t4--t5
--
--
--              t1-t6
--               \  |   
--                t5
-- 
-- ... eventually generates all chords to make the original cycle chordal.
makeChords :: [Term] -> [Literal Equality]
makeChords (t1:t2:t3:t4:ts) =
  Pos (E t1 t3) : makeChords (t1:t3:t4:ts)
makeChords _ = []