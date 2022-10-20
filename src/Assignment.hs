module Assignment (Assignment, fromLiteralList, (|=)) where

import Expr (Expr (..), Atom (..))
import CNF (Literal (..))
import qualified Data.Map as M
import Data.Foldable (toList)

type Assignment = M.Map String Bool

get :: String -> Assignment -> Bool
get = M.findWithDefault False

(|=) :: Assignment -> Expr -> Bool
(|=) assign expr = case expr of
  Atom (V var)  -> get var assign
  Atom T        -> True
  Atom F        -> False
  Not p         -> not (assign |= p)
  p1 `And` p2   -> (assign |= p1) && (assign |= p2)
  p1 `Or` p2    -> (assign |= p1) || (assign |= p2)
  p1 `Impl` p2  -> (assign |= p1) <= (assign |= p2)
  p1 `Equiv` p2 -> (assign |= p1) == (assign |= p2)

fromLiteralList :: [Literal] -> Assignment
fromLiteralList literals = M.fromList (to_pair <$> literals)
  where
    to_pair (Pos var) = (var, True)
    to_pair (Neg var) = (var, False)