-- |
-- We are given a list of non-linear real constraints and an 
-- interval domain for each variable that appears in one of the constraints. 
-- Intervals over-approximate the variable domains. The goal is to
-- contract these intervals as much as possible to improve the approximations.
--
-- For each constraint, e.g. 
--
--    x^2 * y - 3.5 + x < 0
--
-- and a variable in that constraint, e.g. `x`, we solve the expression 
-- for `x`. In general this is not possible for non-linear expressions, 
-- but we can workaround it by introducing fresh variables for each 
-- non-linear term:
--
--    h = x^2 * y        <==>   x = +/- sqrt(h/y)
--
--    h - 3.5 + x < 0    <==>   x < 3.5 - h
--
-- Now for each constraint, substitute each variable on the right-hand-side 
-- with it's interval domain and evaluate the expression with interval 
-- arithmatic. That yields new (potentially tighter) bounds for `x`.
-- Repeat with all other variables. Since that might contract the bounds
-- for variables, that `x` depends on, we can iterate and derive even 
-- tighter bounds for `x`. This method is not guaranteed to narrow the bounds
-- down to point intervals. Stop if convergence is less some threshold.

-- TODO: Also implement Newton constraction method

module Theory.NonLinearRealArithmatic.IntervalConstraintPropagation where

import Theory.NonLinearRealArithmatic.Interval ( Interval ((:..:)) )
import qualified Theory.NonLinearRealArithmatic.Interval as Interval 
import Theory.NonLinearRealArithmatic.Polynomial ( Polynomial(Polynomial), Term(Term), Monomial, exponentOf )
import qualified Theory.NonLinearRealArithmatic.Polynomial as Polynomial
import qualified Data.IntMap as M
import qualified Data.List as List
import Control.Monad.State ( State )
import qualified Control.Monad.State as State
import Data.Containers.ListUtils ( nubOrd )
import Theory.NonLinearRealArithmatic.IntervalUnion (IntervalUnion (IntervalUnion))
import qualified Theory.NonLinearRealArithmatic.IntervalUnion as IntervalUnion
import Theory.NonLinearRealArithmatic.BoundedFloating (BoundedFloating)
import Theory.NonLinearRealArithmatic.Expr (Var)

type VarDomains a = M.IntMap (IntervalUnion a)

data ConstraintRelation = StrictLessThan | WeakLessThan | Equals
  deriving Show

-- | Assuming the expression forms the left-hand-side of the relation, 
-- while the right-hand-side is always zero, e.g. 
-- 
--    x + 3*y - 10 <= 0
-- 
type Constraint a = (ConstraintRelation, Polynomial a)

type PreprocessState a = (Var, [Constraint a], VarDomains a)

varsIn :: [Constraint a] -> [Var]
varsIn constraints = nubOrd $ do 
  (_, Polynomial terms) <- constraints
  Term _ monomial <- terms
  M.keys monomial

-- |
preprocess :: forall a. (Num a, Ord a, Bounded a) => VarDomains a -> [Constraint a] -> (VarDomains a, [Constraint a])
preprocess initial_var_domains initial_constraints = (updated_var_domains, updated_constraints <> side_conditions)
  where
    preprocess_term :: Term a -> State (PreprocessState a) (Term a)
    preprocess_term (Term coeff monomial) =
      if Polynomial.isLinear monomial then
        return (Term coeff monomial)
      else do
        -- We map non-linear terms, say `x^2`, to fresh variables, say `h`
        (fresh_var, side_conditions, var_domains) <- State.get

        let fresh_term = Term 1 (M.singleton fresh_var 1)
    
        -- and create a new constraint that demands their equality, i.e.
        -- 
        --     h = x^2   <==>   0 = h - x^2
        --
        let new_side_condition :: Constraint a
            new_side_condition = (Equals, Polynomial [ fresh_term, Term (-coeff) monomial ] )
    
        -- Then we initialize the domain of the new variable by evaluating x^2
        -- via interval arithmatic (since h = x^2).
        let fresh_var_domain :: IntervalUnion a
            fresh_var_domain = eval var_domains (Polynomial [ Term (IntervalUnion.singleton coeff) monomial ])    
             
        State.put 
          ( fresh_var + 1
          , new_side_condition : side_conditions
          , M.insert fresh_var fresh_var_domain var_domains
          )

        return fresh_term
    
    preprocess_constraint :: Constraint a -> State (PreprocessState a) (Constraint a)
    preprocess_constraint (rel, Polynomial terms) = do 
      updated_terms <- mapM preprocess_term terms
      return (rel, Polynomial updated_terms)
        
    -- Identify the largest used variable ID, so we can generate fresh variables by just incrementing.
    max_var = maximum $ varsIn initial_constraints
    
    -- During the preprocessing step we introduce fresh variables, so we need keep track of the next fresh 
    -- variable and keep updating the variables domains. We also generate side conditions in the form of 
    -- additional equality constraints that we need to keep track of.
    initial_state :: PreprocessState a
    initial_state = (max_var + 1, [], initial_var_domains)
    
    (updated_constraints, final_state) = State.runState (mapM preprocess_constraint initial_constraints) initial_state
    (_, side_conditions, updated_var_domains) = final_state

evalMonomial:: (Bounded a, Num a, Ord a) => VarDomains a -> Monomial -> IntervalUnion a
evalMonomial assignment = product . M.intersectionWith IntervalUnion.power assignment

evalTerm :: (Bounded a, Ord a, Num a) => VarDomains a -> Term (IntervalUnion a) -> IntervalUnion a
evalTerm assignment (Term coeff monomial) = coeff * evalMonomial assignment monomial
 
eval :: (Bounded a, Ord a, Num a) => VarDomains a -> Polynomial (IntervalUnion a) -> IntervalUnion a
eval assignment (Polynomial terms) = sum (evalTerm assignment <$> terms)

-- |
-- Take a constraint such as
--     
--    x^2 + 3y + 10 < 0 
--
-- Bring eveything, except one variable, to one side:
--
--    y < -(x^2 + 10) / 3
--
-- and evaluate the right-hand-side. It's assumed that the constraint 
-- has been preprocessed before. Otherwise it's not possible, in general, 
-- to solve for any variable.
solveFor :: (Ord a, Num a, Bounded a, Floating a) => Var -> Constraint a -> VarDomains a -> IntervalUnion a
solveFor var (rel, polynomial) var_domains = 
  let 
    Just (Term coeff monomial, rest_terms) = Polynomial.extractTerm var polynomial
  
    -- bring all other terms to the right-and-side
    rhs_terms = eval var_domains   
      $ Polynomial (fmap (IntervalUnion.singleton . negate) <$> rest_terms)
  
    -- extract remaining coefficients of `var`
    divisor = evalTerm var_domains
      $ Term (IntervalUnion.singleton coeff) (M.delete var monomial)

  in
    IntervalUnion.root (rhs_terms / divisor) (exponentOf var monomial)
    
-- |
contract :: (Num a, Ord a, Floating a, Bounded a) => Var -> Constraint a -> VarDomains a -> VarDomains a
contract var constraint var_domains = M.insert var new_domain var_domains
  where
    old_domain = var_domains M.! var
    solution = solveFor var constraint var_domains
    -- TODO: intersection only true for equalities
    new_domain = IntervalUnion.intersection old_domain solution
    
-- | 
contractAll :: forall a. (Ord a, Bounded a, Floating a) => [Constraint a] -> VarDomains a -> VarDomains a
contractAll constraints initial_domains = foldr accum initial_domains contraction_candidates
  where
    contraction_candidates = do
      constraint <- constraints
      var <- varsIn [constraint]
      return (var, constraint)

    accum :: (Var, Constraint a) -> VarDomains a -> VarDomains a
    accum (var, constraint) var_domains = contract var constraint var_domains 


example :: [VarDomains (BoundedFloating Float)]
example =
  let
    -- 2x - 3y = 0    
    c1 = (Equals, Polynomial [ Term 2 (M.singleton 1 1), Term (-2) (M.singleton 2 1) ]) 
     -- x^2 - 2y = 0
    c2 = (Equals, Polynomial [ Term 1 (M.singleton 1 2), Term (-2) (M.singleton 2 1) ]) 

    initial = IntervalUnion [ -1 :..: 10 ]
    domains0 = M.fromList [(1, initial), (2, initial)]
  in 
    iterate (contractAll [c1,c2]) domains0 
