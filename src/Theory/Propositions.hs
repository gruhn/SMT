{-| Trivil theory just for boolean propositions -}
module Theory.Propositions where

import Theory
import CNF (Literal(..))
import qualified Data.IntMap as M

newtype Prop = Prop { getVar :: Int }
  deriving (Eq, Ord, Show)

toAssignment :: [Literal Prop] -> Assignment Bool
toAssignment = M.fromList . fmap go 
  where
    go :: Literal Prop -> (Int, Bool)
    go (Pos prop) = (getVar prop, True)
    go (Neg prop) = (getVar prop, False)

instance Theory Prop Bool where
  solve = Right . toAssignment

  satisfies assignment (Pos (Prop var)) = 
    M.findWithDefault False var assignment
  satisfies assignment (Neg (Prop var)) = 
    not $ M.findWithDefault True var assignment
