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

module Theory.NonLinearRealArithmatic.IntervalConstraintPropagation () where

import Theory.NonLinearRealArithmatic.Interval ( Interval )
import qualified Theory.NonLinearRealArithmatic.Interval as Interval 
import Theory.NonLinearRealArithmatic.Expr ( Expr,  Var )
import qualified Theory.NonLinearRealArithmatic.Expr as Expr
import Theory.NonLinearRealArithmatic.Polynomial ( Polynomial(Polynomial), Term(Term), Monomial )
import qualified Theory.NonLinearRealArithmatic.Polynomial as Polynomial
import qualified Data.IntMap as M
import qualified Data.List as List
import Control.Monad.State ( State )
import qualified Control.Monad.State as State
import Data.Containers.ListUtils ( nubOrd )

type VarDomains a = M.IntMap (Interval a)

data ConstraintRelation = StrictLessThan | WeakLessThan | Equals

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
        let fresh_var_domain :: Interval a
            fresh_var_domain = eval var_domains (Polynomial [ Term (Interval.singleton coeff) monomial ])    
             
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

evalMonomial:: (Bounded a, Num a, Ord a) => VarDomains a -> Monomial -> Interval a
evalMonomial assignment = product . M.intersectionWith Interval.power assignment

evalTerm :: (Bounded a, Ord a, Num a) => VarDomains a -> Term (Interval a) -> Interval a
evalTerm assignment (Term coeff monomial) = 
  coeff * evalMonomial assignment monomial
 
eval :: (Bounded a, Ord a, Num a) => VarDomains a -> Polynomial (Interval a) -> Interval a
eval assignment (Polynomial terms) = sum (evalTerm assignment <$> terms)

-- |
-- Take a constraint, e.g.
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
solveFor :: (Ord a, Num a, Floating a, Bounded a) => Var -> Constraint a -> VarDomains a -> [Interval a]
solveFor var (rel, polynomial) var_domains = 
  let 
    Just (Term coeff monomial, rest_terms) = Polynomial.extractTerm var polynomial
  
    -- bring all other terms to the right-and-side
    rhs_terms = eval var_domains   
      $ Polynomial (fmap (Interval.singleton . negate) <$> rest_terms)
  
    -- extract remaining coefficients of `var`
    divisor = evalTerm var_domains
      $ Term (Interval.singleton coeff) (M.delete var monomial)
    
    -- get the exponent to take the root, in case the exponent not 1
    exponent = monomial M.! var

  in do
    -- computing the reciprocal may already split the interval
    recip <- Interval.reciprocal divisor
    Interval.root (rhs_terms * recip) exponent
    
type ContractionCandidate a = (Var, [Interval a], a)
    
contractionCandidates :: forall a. (Ord a, Bounded a, Floating a) => VarDomains a -> [Constraint a] -> [ContractionCandidate a]
contractionCandidates var_domains constraints = do 
  var <- M.keys var_domains

  let old_domain = var_domains M.! var
      old_diameter = Interval.diameter old_domain

  constraint <- constraints
  
  let new_domain = solveFor var constraint var_domains
      new_diameter = sum (Interval.diameter <$> new_domain)
  
  let relative_contraction = (old_diameter - new_diameter) / old_diameter
  
  return (var, new_domain, relative_contraction)


-- TODO: Newton Constraction Method
