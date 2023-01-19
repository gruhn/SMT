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

module Theory.NonLinearRealArithmatic.IntervalConstraintPropagation where

import qualified Data.IntMap as M
import Theory.NonLinearRealArithmatic.Expr
import Control.Monad ( guard )

-- | 
preprocess :: forall a. (Ord a, Num a, Bounded a, Floating a) => VarDomains a -> [Constraint a] -> [(VarDomains a, Constraint a)]
preprocess var_domains constraints = do
  -- Identify largest used variable ID, to later generate fresh variables it.
  let max_var = maximum (maximum . varsIn . snd <$> constraints)
      fresh_vars = [max_var+1 ..]

  (rel, expr) <- constraints
  
  let terms = normalize expr
      terms_with_fresh_vars = zip terms fresh_vars
      
      g :: NormalTerm a -> Int -> NormalTerm a
      g (NTerm coeff monomial) fresh_var
        | isLinear monomial = NTerm coeff monomial
        | otherwise         = NTerm coeff [(fresh_var, 1)]
        
      terms' = uncurry g <$> terms_with_fresh_vars
      constraint' = (rel, denormalize terms')
      
      non_linear_terms_with_fresh_vars = filter (not . isLinear . getMonomial . fst) terms_with_fresh_vars

      -- | 
      -- For each newly added variable h_i, create a new constraint 
      --
      --     m_i - h_i = 0
      -- 
      -- and initialize the bounds of h_i to the interval we get when we substitute the
      -- variable bounds in m_i and evaluate the result using interval arithmetic
      -- (note: the result will always be a single interval because there is no
      -- division or square root in mi).
      h :: NormalTerm a -> Int -> (VarDomains a, Constraint a)
      h term fresh_var = (var_domain, new_constr)
        where
          new_constr = (Equals, denormalize [ term, NTerm (-1) [(fresh_var, 1)] ])
          [ int ] = eval var_domains (denormalize [term])
          var_domain = M.singleton fresh_var int
      
  (M.empty, constraint') : (uncurry h <$> non_linear_terms_with_fresh_vars)


contract :: forall a. (Ord a, Bounded a, Floating a) => VarDomains a -> [Constraint a] -> VarDomains a
contract var_domains0 = foldr go var_domains0 . preprocess
  where
    preprocess :: [Constraint a] -> [(Var, Relation, Expr a)]
    preprocess constraint = do  
      (rel, expr) <- constraint 
      var <- varsIn expr
      -- TODO: introduce new variables for non-linear terms
      return (var, rel, expr `solveFor` var)

    go :: (Var, Relation, Expr a) -> VarDomains a -> VarDomains a
    go (var, rel, expr) var_domains = 
      let int = eval var_domains expr
          -- TODO
          -- derive tighter intervals for `var`
      in  undefined

