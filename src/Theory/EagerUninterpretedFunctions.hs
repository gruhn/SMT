{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE LambdaCase #-}
module Theory.EagerUninterpretedFunctions where

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
import qualified Data.Graph as G
import Data.Bifunctor (bimap)

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
satWith sat expr = sat
  $ encodeTransitivity
  $ conjunctiveNormalForm
  $ tseytin
  $ encodeCongruence
  $ negationNormalForm
  $ expr

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

-- See paper: "Yet Another Decision Procedure for Equality Logic"
encodeTransitivity :: CNF Equality -> CNF Equality
encodeTransitivity cnf =
  let (equalities, disequalites) = polarityPartition cnf

      generate_constraints :: Equality -> S.Set Equality -> CNF Equality
      generate_constraints = _

      -- for all es ∈ E= do
        -- 3: Find B(es) = maximal BCC in GE made of es and E= edges;
        -- 4: Add to B(es) all edges from E= that connect vertices in B(es);
        -- 5: Make the graph B(es) chordal;  (The chords can be either solid or dashed)
        -- 6: Generate-constraints (B(es), es);

  in _

biconnectedComponents :: S.Set Equality -> [S.Set Equality]
biconnectedComponents edges = edges_from <$> biconnected_components
  where
    (graph, term_from_vertex) = eGraph edges

    edges_from :: [Term] -> S.Set Equality
    edges_from terms =
      S.fromList $ zipWith E terms (tail terms ++ [head terms])

    biconnected_components = do
      tree <- G.bcc graph
      biconnected_component <- toList tree
      return $ term_from_vertex <$> biconnected_component

type EqualityGraph = (G.Graph, G.Vertex -> Term)

eGraph :: S.Set Equality -> EqualityGraph
eGraph edges =
  let go :: (Term, S.Set Term) -> (Term, Term, [Term])
      go (node, neighbors) = (node, node, toList neighbors)

      edge_map :: S.Set Equality -> M.Map Term (S.Set Term)
      edge_map edges = M.fromListWith S.union $ do
        (E t1 t2) <- toList edges
        [(t1, S.singleton t2), (t2, S.singleton t1)]

      (graph, node_form_vertex) = G.graphFromEdges' . fmap go . M.toList . edge_map $ edges

      fst' :: (a, b, c) -> a
      fst' (a,_,_) = a

  in  (graph, fst' . node_form_vertex)

simpleChordFreeCycles :: EqualityGraph -> [[Term]]
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