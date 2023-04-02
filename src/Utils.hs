module Utils where
import Data.Maybe (isJust, catMaybes)
import Data.Foldable (toList, concatMap)
import qualified Data.Set as S
import Data.Set (Set)
import Control.Exception (assert)
import Data.List (uncons)

fixpoint :: Eq a => (a -> a) -> a -> a
fixpoint f a
  | a == f a  = a
  | otherwise = fixpoint f (f a)

rightToMaybe :: Either a b -> Maybe b
rightToMaybe = either (const Nothing) Just

takeWhileJust :: [Maybe a] -> [a]
takeWhileJust = catMaybes . takeWhile isJust

distinct :: Ord a => [a] -> [a]
distinct = toList . S.fromList
