{-|
  We are given a list of non-linear real constraints and an 
  interval domain for each variable that appears in one of the constraints. 
  Intervals over-approximate the variable domains. The goal is to
  contract these intervals as much as possible to improve the approximations.

  For each constraint, such as

    x^2 * y - 3.5 + x < 0

  and a variable in that constraint, like `x`, we solve the expression 
  for `x`. In general this is not possible for non-linear expressions, 
  but we can workaround it by introducing fresh variables for each 
  non-linear term:

    h = x^2 * y        <==>   x = +/- sqrt(h/y)

    h - 3.5 + x < 0    <==>   x < 3.5 - h

  Now for each constraint, we substitute each variable on the right-hand-side 
  with it's interval domain and evaluate the expression with interval 
  arithmatic. That yields new (potentially tighter) bounds for `x`.
  We repeat with other constraint/variable pairs. Since that might contract the bounds
  for variables, that `x` depends on, we can iterate and derive even 
  tighter bounds for `x`. This method is not guaranteed to narrow the bounds
  down to point intervals, but if we obtain an empty interval, we showed unsatisfiability.
  Otherwise, we stop if convergence is less some threshold.

  TODO: Also implement Newton constraction method

-}
module Theory.NonLinearRealArithmatic.IntervalConstraintPropagation (VarDomains, Constraint, ConstraintRelation(..), intervalConstraintPropagation) where

import Theory.NonLinearRealArithmatic.Interval ( Interval ((:..:)) )
import qualified Theory.NonLinearRealArithmatic.Interval as Interval
import Theory.NonLinearRealArithmatic.Polynomial ( Polynomial(Polynomial), Term(Term), Monomial, exponentOf )
import qualified Theory.NonLinearRealArithmatic.Polynomial as Polynomial
import qualified Data.IntMap as M
import qualified Data.Map.Lazy as LazyMap
import qualified Data.List as List
import Control.Monad.State ( State )
import qualified Control.Monad.State as State
import Data.Containers.ListUtils ( nubOrd )
import Theory.NonLinearRealArithmatic.IntervalUnion (IntervalUnion (IntervalUnion))
import qualified Theory.NonLinearRealArithmatic.IntervalUnion as IntervalUnion
import Theory.NonLinearRealArithmatic.BoundedFloating (BoundedFloating (Val))
import Theory.NonLinearRealArithmatic.Expr (Var)
import Debug.Trace

type VarDomains a = M.IntMap (IntervalUnion a)

data ConstraintRelation = LessThan | LessEquals | Equals | GreaterEquals | GreaterThan
  deriving Show

{-| 

  Assuming the expression forms the left-hand-side of the relation, 
  while the right-hand-side is always zero, e.g. 
   
    x + 3*y - 10 <= 0

-}
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

{-|
  Take a constraint such as
   
    x^2 + 3y + 10 < 0 

  Bring eveything, except one variable, to one side:

    y < -(x^2 + 10) / 3

  and evaluate the right-hand-side. It's assumed that the constraint 
  has been preprocessed before. Otherwise it's not possible, in general, 
  to solve for any variable.
-}
solveFor :: (Ord a, Num a, Bounded a, Floating a) => Var -> Constraint a -> VarDomains a -> (ConstraintRelation, IntervalUnion a)
solveFor var (rel, polynomial) var_domains =
  let
    Just (Term coeff monomial, rest_terms) = Polynomial.extractTerm var polynomial

    -- bring all other terms to the right-and-side
    rhs_terms = eval var_domains
      $ Polynomial (fmap (IntervalUnion.singleton . negate) <$> rest_terms)

    -- extract remaining coefficients of `var`
    divisor = evalTerm var_domains
      $ Term (IntervalUnion.singleton coeff) (M.delete var monomial)

    flip_relation :: ConstraintRelation -> ConstraintRelation
    flip_relation = \case
      Equals -> Equals
      GreaterThan -> LessThan
      GreaterEquals -> LessEquals
      LessThan -> GreaterThan
      LessEquals -> GreaterEquals

    relation :: ConstraintRelation
    relation
      | signum coeff == -1 = flip_relation rel
      | otherwise          = rel

    solution = IntervalUnion.root (rhs_terms / divisor) (exponentOf var monomial)
  in
    (relation, solution)

type ContractionCandidate a = (Constraint a, Var)

type WeightedContractionCandidates a = LazyMap.Map a [ContractionCandidate a]

{-|
  Contraction is performed using a constraint and a variable that appears in that constraint. 
  Such a constraint/variable pair is called a constraction candidate. The number of choices
  for contraction candidates is potentially large and the contraction gain is generally not 
  predictable, so we choose contraction candidates heuristically: We assign a weight between 
  0 and 1 to each contraction candidate (initially 0.1) and always pick the candidate with 
  the highest weight. After contracting, we compute the relative contraction, that was achieved, 
  and update the weight of the contraction candidate. 

  The contraction candidates are stored in a Map from weights to lists of contraction 
  candidates (all with the same weight). Note that the Map is strict in the keys but lazy in the 
  values, so we may never compute the full list of contraction candidates.
-}
chooseContractionCandidate :: Ord a => State (WeightedContractionCandidates a) (a, ContractionCandidate a)
chooseContractionCandidate = do
  candidates <- State.get
  case LazyMap.maxViewWithKey candidates of
    Just ((_, []), candidates') -> do
      -- maximum weight has no candidates associated anymore, so clean up and choose again
      State.put candidates'
      chooseContractionCandidate
    Just ((weight, cc : ccs), candidates') -> do
      -- Maximum weight has one or more candidates associated with it, so pick the first one 
      -- and put the rest pack into the Map.
      State.put (LazyMap.insert weight ccs candidates')
      return (weight, cc)
    Nothing ->
      -- This should not happen. The set of contraction candidates should always be the same.
      -- Although we extract them above, they must be put back into the Map with updated weights.
      error "no contraction candidates"

contractWith :: (Num a, Ord a, Floating a, Bounded a) => ContractionCandidate a -> VarDomains a -> IntervalUnion a
contractWith (constraint, var) var_domains = new_domain
  where
    (relation, solution) = solveFor var constraint var_domains

    old_domain = var_domains M.! var
    new_domain = case relation of
      Equals        -> IntervalUnion.intersection old_domain solution
      LessEquals    -> error "TODO: not implemented yet"
      LessThan      -> error "TODO: not implemented yet"
      GreaterThan   -> error "TODO: not implemented yet"
      GreaterEquals -> error "TODO: not implemented yet"

relativeContraction :: (Num a, Ord a, Fractional a) => IntervalUnion a -> IntervalUnion a -> a
relativeContraction old_domain new_domain = 
  let
    old_diameter = IntervalUnion.diameter old_domain
    new_diameter = IntervalUnion.diameter new_domain
  in
    if old_diameter == 0 then
      0
    else 
      (old_diameter - new_diameter) / old_diameter

{-|
  TODO: 

  1) ICP does not behave well on linear constraints. 
     Partition constraints into linear and non-linear,
     and solve the linear constraints with simplex.

  2) splitting intervals can help with contraction, if 
     the interval contains multiple roots, so split if
     this can be detected

-}
intervalConstraintPropagation :: forall a. (Num a, Ord a, Bounded a, Floating a, Show a) => [Constraint a] -> VarDomains a -> VarDomains a
intervalConstraintPropagation constraints0 domains0 = State.evalState (go domains1) contraction_candidates 
  where
    (domains1, constraints1) = preprocess domains0 constraints0

    -- TODO: very magic number without theoretical or empirical basis
    initial_weight = 0.1

    contraction_candidates :: WeightedContractionCandidates a
    contraction_candidates = LazyMap.singleton initial_weight $ do
      constraint <- constraints1
      var <- varsIn [ constraint ]
      return (constraint, var)

    go :: VarDomains a -> State (WeightedContractionCandidates a) (VarDomains a)
    go domains = do
      (old_weight, (constraint, var)) <- chooseContractionCandidate

      let old_domain = domains M.! var
          new_domain = contractWith (constraint, var) domains
          new_weight = traceShowId $ relativeContraction old_domain new_domain

      State.modify (LazyMap.insertWith (<>) new_weight [(constraint, var)])

        -- If variable domain was contracted to an empty interval, it shows that the 
        -- constraints are unsatisfiable. 
      let unsat = IntervalUnion.isEmpty new_domain

      -- If the relative contraction is smaller than the initial weight, we assume
      -- convergence has slowed down and we terminate.
      let slow_converge = new_weight < initial_weight
          
      if unsat || slow_converge then
        return (M.insert var new_domain domains)
      else
        go (M.insert var new_domain domains)


example1 =
  let
    -- x0^2 * x1^2
    terms = [ Polynomial.Term (Val 1.0) $ M.fromList [(0, 2), (1, 2)] ]

    constraint = (Equals, Polynomial terms)

    dom = IntervalUnion [ Val (-1) :..: Val 1 ]

    domains_before = M.fromList [ (0, dom) ]
    domains_after = intervalConstraintPropagation [ constraint ] domains_before
  in 
    domains_after


example2 = 
  let
    -- 0.13883655 - x0
    terms = [ Term (-1) (M.fromList [ (0,1) ]), Term 0.13883655 M.empty ]

    constraint = (Equals, Polynomial terms)

    dom = IntervalUnion [ Val (-1) :..: Val 1 ]

    domains_before = M.fromList [ (0, dom) ]
    domains_after = intervalConstraintPropagation [ constraint ] domains_before
  in 
    domains_after
