module Utils where
import Data.Maybe (isJust, catMaybes)
import Data.Foldable (toList, concatMap)
import qualified Data.Set as S
import Data.Set (Set)
import Control.Exception (assert)
import Data.List (uncons, tails)

fixpoint :: Eq a => (a -> a) -> a -> a
fixpoint f a
  | a == f a  = a
  | otherwise = fixpoint f (f a)

rightToMaybe :: Either a b -> Maybe b
rightToMaybe = either (const Nothing) Just

takeWhileJust :: [Maybe a] -> [a]
takeWhileJust = catMaybes . takeWhile isJust

combinations :: [a] -> [(a,a)]
combinations []     = []
combinations (a:as) = map (a,) as ++ combinations as
