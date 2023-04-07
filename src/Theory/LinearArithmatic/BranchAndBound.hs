module Theory.LinearArithmatic.BranchAndBound 
  ( branchAndBound
  , isIntegral
  ) where

import Theory.LinearArithmatic.Simplex ( simplexSteps, initTableau, Tableau(..), BoundType(..), isSatisfied )
import Theory.LinearArithmatic.Constraint
import Data.Ratio (denominator, numerator)
import qualified Data.IntSet as S
import qualified Data.IntMap as M
import Control.Applicative ((<|>))
import Data.Maybe (fromJust)

isIntegral :: Rational -> Bool
isIntegral rational = 
  numerator rational `mod` denominator rational == 0

findFractional :: S.IntSet -> BBState -> Maybe (Var, Rational)
findFractional vars state =  M.lookupMin 
  $ M.filter (not . isIntegral)
  $ M.restrictKeys (getAssignment $ getTableau state) vars

data BBState = BB 
  { getFreshVars :: [Var]
  , getTableau :: Tableau
  } deriving Show

initState :: [Constraint] -> Maybe BBState
initState constraints = do 
  tableau_0 <- initTableau constraints 
  return $ BB (freshVariables constraints) tableau_0

branch :: Var -> Rational -> BoundType -> BBState -> BBState
branch var frac_value bound_type (BB fresh_vars tableau) = 
  let Tableau basis bounds assignment = tableau

      fresh_var = head fresh_vars

      int_value = 
        case bound_type of
          UpperBound -> fromIntegral $ floor frac_value
          LowerBound -> fromIntegral $ ceiling frac_value

      tableau_row =
        case M.lookup var basis of
          Just expr -> expr
          Nothing   -> M.singleton var 1

      fresh_var_value = fromJust $ eval assignment $ AffineExpr 0 tableau_row
      
   in BB (tail fresh_vars) $ Tableau
      (M.insert fresh_var tableau_row basis)
      (M.insert fresh_var (bound_type, int_value) bounds)
      (M.insert fresh_var fresh_var_value assignment)

solveRelaxation :: BBState -> Maybe BBState
solveRelaxation (BB fresh_var tableau)
  | isSatisfied tableau' = Just $ BB fresh_var tableau'
  | otherwise = Nothing
  where
    tableau' = last $ simplexSteps tableau 

branchAndBound :: [Constraint] -> S.IntSet -> Maybe Assignment
branchAndBound constraints int_vars = do
  let original_vars = varsInAll constraints

      restrict :: Assignment -> Assignment
      restrict assignment = M.restrictKeys assignment original_vars

      go :: BBState -> Maybe BBState
      go state = do
        state' <- solveRelaxation state
        case findFractional int_vars state' of
          Nothing                -> Just state'
          Just (var, frac_value) -> go left_branch <|> go right_branch
            where
              left_branch = branch var frac_value UpperBound state'
              right_branch = branch var frac_value LowerBound state'

  state_0 <- initState constraints 
  state_n <- go state_0

  case findFractional int_vars state_n of
    Nothing -> Just $ restrict $ getAssignment $ getTableau state_n
    Just _  -> Nothing

--------------------

example = 
  [ (AffineExpr (-2)   $ M.fromList [ (0,1), (1,1) ], GreaterEquals )
  , (AffineExpr (-1/2) $ M.fromList [ (0, 1), (1, -1)], LessEquals )
  , (AffineExpr (-1) $ M.fromList [ (0, 1) ], LessEquals )
  , (AffineExpr 1      $ M.fromList [ (0, 1), (1, -1)], GreaterEquals )
  , (AffineExpr (-3/2) $ M.fromList [ (0,1) ], LessEquals )
  , (AffineExpr (-3/2) $ M.fromList [ (1,1) ], GreaterEquals )
  , (AffineExpr (-7/4) $ M.fromList [ (1,1) ], LessEquals )
  ]
