module Theory.NonLinearRealArithmatic.UnivariatePolynomial 
  ( term
  , constant
  -- WARN: don't expose type constructor to make sure invariants are enforced
  , UnivariatePolynomial
  , viewLeadTerm
  , lookupLeadTerm
  , toList
  , fromList
  , fromPolynomial
  , toPolynomial
  , derivative
  , divide
  , eval
  ) where

import Theory.NonLinearRealArithmatic.Polynomial (Polynomial)
import qualified Theory.NonLinearRealArithmatic.Polynomial as P
import Data.IntMap (IntMap)
import qualified Data.IntMap as M
import Control.Exception (assert)
import qualified Data.List as List
import Utils (assertM, adjacentPairs, count)

-- TODO: property test: never contains zero coefficients
newtype UnivariatePolynomial a = Univariate { getTerms :: IntMap a }
  deriving Eq

instance Show a => Show (UnivariatePolynomial a) where
  show (Univariate terms) = 
    List.intercalate " + " [ show coeff ++ "x^" ++ show exp | (exp, coeff) <- M.toDescList terms ]

term :: (Eq a, Num a) => Int -> a -> UnivariatePolynomial a
term exp coeff 
  | coeff == 0 = Univariate M.empty
  | otherwise  = Univariate $ M.singleton exp coeff

constant :: (Eq a, Num a) => a -> UnivariatePolynomial a
constant = term 0

-- | Extract term with largest exponent.
viewLeadTerm :: (Eq a, Num a) => UnivariatePolynomial a -> Maybe ((Int, a), UnivariatePolynomial a)
viewLeadTerm polynomial = do
  ((exp, coeff), rest_terms) <- M.maxViewWithKey $ getTerms polynomial
  -- assume that polynomial is normalized and that all terms with zero coefficient are removed:
  assertM (coeff /= 0)
  return ((exp, coeff), Univariate rest_terms)

lookupLeadTerm :: (Eq a, Num a) => UnivariatePolynomial a -> Maybe (Int, a)
lookupLeadTerm = fmap fst . viewLeadTerm

-- | Largest exponent of term with non-zero coefficient in the polynomial.
degree :: (Eq a, Num a, Show a) => UnivariatePolynomial a -> Int
degree = maybe 0 fst . lookupLeadTerm

instance (Num a, Eq a) => Num (UnivariatePolynomial a) where
  Univariate p + Univariate q = Univariate $ M.filter (/= 0) $ M.unionWith (+) p q

  Univariate p * Univariate q = Univariate $ M.fromList $ do
    (exp_p, coeff_p) <- M.toList p
    (exp_q, coeff_q) <- M.toList q
    assertM $ coeff_p /= 0 && coeff_q /= 0
    return (exp_p + exp_q, coeff_p * coeff_q)
    
  abs = error "TODO: not implemented"

  signum = error "TODO: not implemented"

  fromInteger = constant . fromInteger

  negate (Univariate p) = Univariate $ M.map negate p

-- | From list of exponent/coefficient pairs.
fromList :: [(Int, a)] -> UnivariatePolynomial a
fromList = Univariate . M.fromList

-- | So list of exponent/coefficient pairs, ascendingly ordered by exponents.
toList :: UnivariatePolynomial a -> [(Int, a)]
toList = M.toAscList . getTerms

-- | Extracts univariate polynomial. Returns `Nothing` if the polynomial is multivariate.
fromPolynomial :: forall a. (Num a, Eq a) => Polynomial a -> Maybe (UnivariatePolynomial a)
fromPolynomial polynomial =
  case P.varsIn polynomial of
    -- polynomial is just a constant:
    [] -> Just $ constant $ P.coefficientOf M.empty polynomial

    -- polynomial has exactly one variable:
    [ var ] -> Just $ Univariate $ M.fromList $ do
      P.Term coeff monomial <- P.getTerms polynomial
      let exp = P.exponentOf var monomial      
      return (exp, coeff)

    -- polynomial has two or more variables:
    _two_or_more_variables -> Nothing

toPolynomial :: (Num a, Ord a) => UnivariatePolynomial a -> Polynomial a
toPolynomial polynomial = P.mkPolynomial $ do
  (exp, coeff) <- M.toList $ getTerms polynomial
  return $ P.Term coeff (M.singleton 0 exp)

eval :: Num a => a -> UnivariatePolynomial a -> a
eval x (Univariate terms) = sum [ coeff * x^exp | (exp, coeff) <- M.toList terms ]

derivative :: forall a. Num a => UnivariatePolynomial a -> UnivariatePolynomial a
derivative (Univariate polynomial) = Univariate $ M.fromList
  [ (exp-1, coeff * fromIntegral exp) | (exp, coeff) <- M.toList polynomial, exp > 0 ]

-- | Perform polynomial division and return both quotient and remainder.
--
-- TODO: property test division/multiplication.
divide :: forall a. (Fractional a, Eq a) => UnivariatePolynomial a -> UnivariatePolynomial a -> (UnivariatePolynomial a, UnivariatePolynomial a)
divide dividend divisor = go 0 dividend
  where
    go :: UnivariatePolynomial a -> UnivariatePolynomial a -> (UnivariatePolynomial a, UnivariatePolynomial a)
    go quotient remainder =
      case (lookupLeadTerm remainder, lookupLeadTerm divisor) of
        (_, Nothing) -> error "division by zero in polynomial division"

        (Nothing, _) -> (quotient, 0)

        (Just (rem_exp, rem_coeff), Just (div_exp, div_coeff))
          | rem_exp < div_exp -> (quotient, remainder)
          | otherwise ->
            let quot_term = term (rem_exp - div_exp) (rem_coeff / div_coeff)
            in go (quotient + quot_term) (remainder - quot_term * divisor)
