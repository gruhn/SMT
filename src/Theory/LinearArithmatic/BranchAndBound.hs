module Theory.LinearArithmatic.BranchAndBound
  ( branchAndBound
  , isIntegral
  , steps
  , isSat
  ) where

import qualified Theory.LinearArithmatic.Simplex as Simplex
import Theory.LinearArithmatic.Simplex (Tableau, BoundType(..))
import Theory.LinearArithmatic.Constraint
import Data.Ratio (denominator, numerator, (%))
import qualified Data.IntSet as S
import qualified Data.IntMap as M
import Control.Applicative ((<|>))
import Data.Maybe (fromJust)
import Utils (takeUntil, firstJust)

isIntegral :: Rational -> Bool
isIntegral rational =
  numerator rational `mod` denominator rational == 0

findFractional :: S.IntSet -> Tableau -> Maybe (Var, Rational)
findFractional vars tableau =
  M.lookupMin
    $ M.filter (not . isIntegral)
    $ M.restrictKeys (Simplex.getAssignment tableau) vars

branchOn :: Var -> Rational -> Tableau -> (Tableau, Tableau)
branchOn var frac_value tableau =
  let
    left_branch :: Tableau
    left_branch = 
      Simplex.addTableauRow
        (AffineExpr (- fromIntegral (floor frac_value)) (M.singleton var 1))
        UpperBound
        tableau

    right_branch :: Tableau
    right_branch = 
      Simplex.addTableauRow
        (AffineExpr (- fromIntegral (ceiling frac_value)) (M.singleton var 1))
        LowerBound
        tableau
  in
    (left_branch, right_branch)

solveRelaxation :: Tableau -> Maybe Tableau
solveRelaxation tableau
  | Simplex.isSatisfied tableau' = Just tableau'
  | otherwise = Nothing
  where
    tableau' = last $ Simplex.steps tableau

data BBState = Sat Assignment | Pending Tableau

steps :: [Constraint] -> S.IntSet -> [BBState] 
steps constraints int_vars = 
  let 
    original_vars = varsInAll constraints

    get_model :: Tableau -> Assignment
    get_model tableau = M.restrictKeys (Simplex.getAssignment tableau) original_vars

    go :: BBState -> [BBState]
    go (Sat _)           = []
    go (Pending tableau) = Pending tableau : 
      case solveRelaxation tableau of
        Nothing -> []
        Just tableau_next -> 
          case findFractional int_vars tableau_next of
            Nothing                -> [ Sat (get_model tableau_next) ]
            Just (var, frac_value) -> 
              let 
                (left_branch, right_branch) = branchOn var frac_value tableau_next
              in
                go (Pending left_branch) <|> go (Pending right_branch)
  in
    maybe [] (go . Pending) $ Simplex.initTableau constraints

isSat :: BBState -> Maybe Assignment
isSat (Sat model) = Just model
isSat _           = Nothing

{-|
  TODO: 
    * Currently incomplete, i.e. algorithm may not terminate on some inputs.
      - especially equality constraints
    * Constraint preprocessing: 
      - remove redundant constraints
      - tighten bounds

-}
branchAndBound :: [Constraint] -> S.IntSet -> Maybe Assignment
branchAndBound constraints int_vars = 
  firstJust isSat $ steps constraints int_vars

--------------------

example =
  [ (AffineExpr (-2)   $ M.fromList [ (0,1), (1,1) ]   , GreaterEquals )
  , (AffineExpr (-1/2) $ M.fromList [ (0, 1), (1, -1)] , LessEquals    )
  , (AffineExpr (-1)   $ M.fromList [ (0, 1) ]         , LessEquals    )
  , (AffineExpr 1      $ M.fromList [ (0, 1), (1, -1)] , GreaterEquals )
  , (AffineExpr (-3/2) $ M.fromList [ (0,1) ]          , LessEquals    )
  , (AffineExpr (-3/2) $ M.fromList [ (1,1) ]          , GreaterEquals )
  , (AffineExpr (-7/4) $ M.fromList [ (1,1) ]          , LessEquals    )
  ]

example2 =
  [ (AffineExpr 1 $ M.fromList [ (0,-2), (1,1) ], LessEquals ) ]

example3 = 
  [ ( AffineExpr (-1) (M.fromList [(0,3),(1,-3)]), GreaterEquals )
  , ( AffineExpr 0 (M.singleton 0 1), LessEquals)
  , ( AffineExpr 1 (M.singleton 1 1), LessEquals)
  ]
