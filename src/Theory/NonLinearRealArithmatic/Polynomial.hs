{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant $" #-}
{-# HLINT ignore "Use <$>" #-}
module Theory.NonLinearRealArithmatic.Polynomial
  ( Polynomial
  , getTerms
  , Monomial
  , mkPolynomial
  , exponentOf
  , Term(..)
  , modifyCoeff
  , modifyMonomial
  , varsIn
  , isLinear
  , extractTerm
  , fromExpr
  , toExpr
  , map
  , degree
  , termDegree
  , Assignable(..)
  , Assignment
  , UnivariatePolynomial
  , toUnivariate
  ) where

import Theory.NonLinearRealArithmatic.Expr (Expr(..), Var, BinaryOp(..), UnaryOp(..))
import qualified Data.List as L
import qualified Data.IntMap as M
import qualified Data.IntSet as S
import qualified Data.List as List
import Data.IntMap ( IntMap )
import Data.Function ( on )
import Data.Containers.ListUtils ( nubOrd )
import Control.Monad ( guard )
import Data.Maybe ( maybeToList )
import Prelude hiding (map)
import Control.Arrow ((&&&))

-- | Map of variables to integer exponents.
type Monomial = IntMap Int

exponentOf :: Var -> Monomial -> Int
exponentOf = M.findWithDefault 0

data Term a = Term { getCoeff :: a, getMonomial :: Monomial }

instance Show a => Show (Term a) where
  show (Term coeff monomial) = show coeff <> monomial_showed
    where
      show_var :: (Var,Int) -> String
      show_var (var, exp) =
        "(x" <> show var <> "^" <> show exp <> ")"

      monomial_showed :: String
      monomial_showed = concatMap show_var (M.toList monomial)

modifyCoeff :: (a -> a) -> Term a -> Term a
modifyCoeff f (Term coeff monomial) = Term (f coeff) monomial

modifyMonomial :: (Monomial -> Monomial) -> Term a -> Term a
modifyMonomial f (Term coeff monomial) = Term coeff (f monomial)

newtype Polynomial a = Polynomial { getTerms :: [Term a] }

{-|
  In a normalized polynomial:

  * All terms have non-zero coefficients. A zero coefficient is equivalent to simply
    not storing the term.

  * All exponents are non-zero. Because `x^0 = 1` we can simply not store variables 
    with zero exponent.

  * Terms have pair-wise distinct monomials. Two terms with the same monomials, 
    like `3xy` and `2yx` and always be combined to one term `5xy`.

-}
normalize :: (Num a, Ord a) => Polynomial a -> Polynomial a
normalize (Polynomial terms) =
  let
    reject_zero_coeffs = filter ((/= 0) . getCoeff)
    reject_zero_exponents = fmap (modifyMonomial (M.filter (/= 0)))
  in
    Polynomial
      $ combineTerms
      $ reject_zero_exponents
      $ reject_zero_coeffs
      $ terms

{-| 
  Constructs a normalized polynomial from a list of terms.

  For the sake of space and time complexity, it's favorable to keep polynomials normalized. 
  Some operations, like adding two normalized polynomials, can yield un-normalized polynomials. 
  For example, adding -2x and 2x, yields 0x. 

  The `Polynomial` module restricts access to the default constructor, to ensure that un-normalized
  polynomials can not be constructed and any potentially de-normalizing operation is immediately 
  followed by a re-normalization.
-}
mkPolynomial :: (Num a, Ord a) => [Term a] -> Polynomial a
mkPolynomial = normalize . Polynomial

instance Show a => Show (Polynomial a) where
  show (Polynomial terms) =
    List.intercalate " + " (show <$> terms)

instance (Ord a, Num a) => Num (Polynomial a) where
  (Polynomial p1) + (Polynomial p2) = mkPolynomial $ p1 <> p2

  (Polynomial p1) * (Polynomial p2) = mkPolynomial $ do
    Term coeff1 exps1 <- p1
    Term coeff2 exps2 <- p2
    -- Sum up exponents of same variables.
    return $ Term (coeff1*coeff2)  $ M.unionWith (+) exps1 exps2

  abs (Polynomial p) = Polynomial (modifyCoeff abs <$> p)

  negate (Polynomial p) = Polynomial (modifyCoeff negate <$> p)

  signum (Polynomial p) = Polynomial (modifyCoeff signum <$> p)

  fromInteger i = mkPolynomial [Term (fromInteger i) M.empty]

instance Functor Term where
  fmap f (Term coeff monomial) = Term (f coeff) monomial

{-|
  Mapping over a Polynomial might de-normalize it and applying normalization requires type 
  constraints, so we can't define a standard Functor instance. 
-}
map :: (Num b, Ord b) => (a -> b) -> Polynomial a -> Polynomial b
map f (Polynomial terms) = mkPolynomial (fmap (fmap f) terms)

-- Combine terms with same monomial, e.g. combine 3*x*y and 2*y*x to 5*x*y.
--
--  1.  Sort the terms BY the monomials, so equal monomials are next to each other. 
--
--  2.  `go` over the terms and sum up equal monomials.
--
--  3.  Some terms now might have coefficient `0`. Filter them out.
--
combineTerms :: forall a. (Num a, Ord a) => [Term a] -> [Term a]
combineTerms = filter ((/= 0) . getCoeff) . go . List.sortOn getMonomial
  where
    go :: [Term a] -> [Term a]
    go (Term coeff1 monomial1 : Term coeff2 monomial2 : terms)
      | monomial1 == monomial2 = go (Term (coeff1+coeff2) monomial1 : terms)
      | otherwise = Term coeff1 monomial1 : go (Term coeff2 monomial2 : terms)
    go terms = terms

-- | Computes the partial derivative of a polynomial with respect to a given Var.
partialDerivative :: forall a. (Eq a, Num a) => Var -> Polynomial a -> Polynomial a
partialDerivative var (Polynomial terms) =
  let
    go :: Term a -> Term a
    go (Term coeff monomial) = Term new_coeff new_monomial
      where
        exp = exponentOf var monomial
        new_coeff = coeff * fromIntegral exp
        new_monomial = M.insert var (exp-1) monomial
  in
    Polynomial $ filter ((/= 0) . getCoeff) $ go <$> terms

-- | Bring expression into normal form as a polynomial: 
-- 
--      (r_1 * m_1) + (r_2 * m_2) + ... + (r_k * m_k)
-- 
-- where m_i are monomials (either 1 or a product of variables) and
-- r_i are constant coeffitions. E.g.
-- 
--      3*(x+y)^2 + 2*y + 10 + 5
--   =  3*x^2 + 6*x*y + 3*y^2 + 2*y + 15*1
-- 
fromExpr :: forall a. (Ord a, Num a) => Expr a -> Polynomial a
fromExpr expr =
  -- Multiply out nested expressions and eliminate subtractions until
  -- we are left with a big sum, where each summand is composed of a 
  -- a constant coefficient and a monomial.
  case expr of
    Var var -> Polynomial [ Term 1 (M.singleton var 1) ]
    Const a -> Polynomial [ Term a M.empty ]

    UnaryOp (Root _) _ -> error "Roots in user provided expressions not supported"

    UnaryOp (Exp n) (Const a) -> Polynomial [ Term (a^n) M.empty ]
    UnaryOp (Exp n) (Var var) -> Polynomial [ Term 1 (M.singleton var n) ]
    UnaryOp (Exp n) expr ->
      if n < 1 then
        error "Non-positive exponents not supported"
      else if n == 1 then
        fromExpr expr
      else
        fromExpr $ BinaryOp Mul expr (UnaryOp (Exp (n-1)) expr)

    BinaryOp Add expr1 expr2 -> fromExpr expr1 + fromExpr expr2
    BinaryOp Sub expr1 expr2 -> fromExpr expr1 - fromExpr expr2
    BinaryOp Mul expr1 expr2 -> fromExpr expr1 * fromExpr expr2
    BinaryOp Div _ _ -> error "Division in user provided expressions not supported"

toExpr :: forall a. (Ord a, Num a) => Polynomial a -> Expr a
toExpr = sum . fmap from_term . getTerms
  where
    from_term :: Term a -> Expr a
    from_term (Term coeff monomial) =
      Const coeff * product (M.mapWithKey from_var monomial)

    from_var :: Var -> Int -> Expr a
    from_var var n
      | n == 1 = Var var
      | n > 1  = UnaryOp (Exp n) (Var var)
      | otherwise = error "Non-positive exponents not supported."

-- |
-- A monomial is linear if all exponents are 0, e.g. `x^0 * y^0 * z^0` = 1.
-- Or exactly one of the exponents is 1, e.g. x^0 * y^0 * z^1 = z.
isLinear :: Monomial -> Bool
isLinear monomial = is_zero || is_unit
  where
    non_zero_exponents = filter (/= 0) $ M.elems monomial

    is_zero = null non_zero_exponents
    is_unit = [1] == non_zero_exponents

termDegree :: Term a -> Int
termDegree = sum . getMonomial

degree :: (Num a, Ord a) => Polynomial a -> Int
degree = maximum . fmap termDegree . getTerms

-- TODO: does that make sense for multivariate polynomials?
cauchyBound :: (Fractional a, Ord a) => Polynomial a -> a
cauchyBound polynomial = 1 + maximum [ abs (coeff / top_coeff) | coeff <- coeffs ]
  where
    -- Extract highest degree term with non-zero coefficient.
    (top_coeff : coeffs) =
        filter (/= 0)
      $ fmap getCoeff
      $ List.sortOn (negate . termDegree)
      $ getTerms polynomial

varsIn :: Polynomial a -> [Var]
varsIn (Polynomial terms) =
  nubOrd (terms >>= M.keys . getMonomial)

containsVar :: Var -> Term a -> Bool
containsVar var (Term _ monomial) =
  case M.lookup var monomial of
    Nothing -> False
    Just 0  -> False -- this should never occurs for normalized polynomials
    Just _  -> True

extractTerm :: Var -> Polynomial a -> Maybe (Term a, [Term a])
extractTerm var (Polynomial terms) = go [] terms
  where
    go :: [Term a] -> [Term a] -> Maybe (Term a, [Term a])
    go init [] = Nothing
    go init (term : tail)
      | containsVar var term = Just (term, reverse init <> tail)
      | otherwise            = go (term : init) tail

type Assignment a = IntMap a

class Num a => Assignable a where
  evalMonomial :: Assignment a -> Monomial -> a
  evalMonomial assignment = product . M.intersectionWith (^) assignment

  evalTerm :: Assignment a -> Term a -> a
  evalTerm assignment (Term coeff monomial) = coeff * evalMonomial assignment monomial

  eval :: Assignment a -> Polynomial a -> a
  eval assignment polynomial = sum (evalTerm assignment <$> getTerms polynomial)

type UnivariatePolynomial a = [ (Int, a) ]

{-| 
  Extracts list of exponent/coefficient pairs, sorted by exponent. 
  Returns Nothing, if the polynomial is multivariate.
-}
toUnivariate :: Polynomial a -> Maybe (UnivariatePolynomial a)
toUnivariate polynomial =
  case varsIn polynomial of
    [ var ] -> Just 
      $ L.sortOn fst 
      $ fmap (exponentOf var . getMonomial &&& getCoeff)
      $ getTerms polynomial
    zero_or_two_or_more_vars -> Nothing
