module Assignment (Assignment, fromLiteralList, (|=), ignoreAuxVars) where

import Expression (Expr (..))
import CNF (Literal (..), WithAux (..))
import qualified Data.Map as M
import Data.Foldable (toList)

type Assignment a = M.Map a Bool

get :: Ord a => a -> Assignment a -> Bool
get = M.findWithDefault False

(|=) :: Ord a => Assignment a -> Expr a -> Bool
(|=) assign expr = case expr of
  T             -> True
  F             -> False
  Atom atom     -> get atom assign
  Not p         -> not (assign |= p)
  p1 `And` p2   -> (assign |= p1) && (assign |= p2)
  p1 `Or` p2    -> (assign |= p1) || (assign |= p2)
  p1 `Impl` p2  -> (assign |= p1) <= (assign |= p2)
  p1 `Equiv` p2 -> (assign |= p1) == (assign |= p2)

ignoreAuxVars :: Ord a => Assignment (WithAux a) -> Assignment a
ignoreAuxVars assignment = M.fromList $ do
  (key, val) <- M.toList assignment
  case key of
    (Var a) -> [(a, val)]
    _           -> []

fromLiteralList :: Ord a => [Literal a] -> Assignment a
fromLiteralList literals = M.fromList (to_pair <$> literals)
  where
    to_pair (Pos var) = (var, True)
    to_pair (Neg var) = (var, False)