module Theory.NonLinearRealArithmatic.Polynomial where

import Theory.NonLinearRealArithmatic.Expr (Expr(..), Var, BinaryOp(..), UnaryOp(..))
import qualified Data.List as L
import Data.Function ( on )

-- | List of variables paired with their positive integer exponents.
type Monomial = [(Var, Int)]

data Term a = Term { getCoeff :: a, getMonomial :: Monomial }

type Polynomial a = [Term a]

modifyCoeff :: (a -> a) -> Term a -> Term a
modifyCoeff f (Term coeff monomial) = Term (f coeff) monomial

modifyMonomial :: (Monomial -> Monomial) -> Term a -> Term a
modifyMonomial f (Term coeff monomial) = Term coeff (f monomial)

derivative :: Polynomial a -> Polynomial a
derivative = undefined -- TODO
-- derivative = Polynomial . tail . zipWith (*) [0..] . getCoefficients

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
-- TODO: property test "expression is equivalent to polynomial"
--
fromExpr :: forall a. (Ord a, Num a) => Expr a -> Polynomial a
fromExpr = sum_coeffs . expand
  where
    -- Multiply out nested expressions and eliminate subtractions until
    -- we are left with a big sum, where each summand is composed of a 
    -- a constant coefficient and a monomial. That leaves potentially 
    -- many terms that can be summed up and combined into one term. 
    -- Do that separately with `sum_coeffs`.
    expand :: Expr a -> Polynomial a
    expand expr =
      case expr of
        Var var -> [ Term 1 [(var, 1)] ]
        Const a -> [ Term a [] ]

        UnaryOp (Root _) _ -> error "Roots in user provided expressions not supported"

        UnaryOp (Exp n) (Const a) -> [ Term (a^n) [] ]
        UnaryOp (Exp n) (Var var) -> [ Term 1 [(var, n)] ]
        UnaryOp (Exp n) expr -> 
          if n < 1 then 
            error "Non-positive exponents not supported"
          else if n == 1 then
            expand expr
          else 
            expand $ BinaryOp Mul expr (UnaryOp (Exp (n-1)) expr)

        BinaryOp Add expr1 expr2 -> 
          expand expr1 <> expand expr2

        BinaryOp Sub expr1 expr2 -> 
          expand expr1 <> (modifyCoeff negate <$> expand expr2)

        BinaryOp Div _ _ -> error "Division in user provided expressions not supported"

        BinaryOp Mul expr1 expr2 -> do
          Term coeff1 vars1 <- expand expr1
          Term coeff2 vars2 <- expand expr2
          return $ Term (coeff1*coeff2) $ sum_exponents (vars1 <> vars2)

    -- Sum up exponents of same variables.
    sum_exponents :: Monomial -> Monomial
    sum_exponents = go . L.sort
      where
        go :: Monomial -> Monomial
        go ((var1, exp1) : (var2, exp2) : factors)
          | var1 == var2 = (var1, exp1+exp2) : go factors
          | otherwise = (var1, exp1) : go ((var2, exp2) : factors)
        go (factor : factors) = factor : go factors
        go [] = []

    -- Combine terms with same monomial, e.g. combine 3*x*y and 2*y*x to 5*x*y.
    --
    --  1.  Sort each monomial, so for example x*y is recognized as being the 
    --      same monomial as y*x. 
    --
    --  2.  Sort the terms BY the monomials, so equal monomials are next to 
    --      each other. 
    --
    --  3.  `go` over the terms and sum up equal monomials.
    --
    --  4.  Some terms now might have coefficient `0`. Filter them out.
    --
    sum_coeffs :: Polynomial a -> Polynomial a
    sum_coeffs = filter ((/= 0) . getCoeff) . go . L.sortBy (compare `on` getMonomial) . fmap (modifyMonomial L.sort)
      where
        go :: [Term a] -> [Term a]
        go ((Term coeff1 monomial1) : (Term coeff2 monomial2) : terms)
          | monomial1 == monomial2 = go (Term (coeff1+coeff2) monomial1 : terms)
          | otherwise = Term coeff1 monomial1 : go (Term coeff2 monomial2 : terms)
        go terms = terms

toExpr :: Polynomial a -> Expr a
toExpr = foldr1 (BinaryOp Add) . fmap from_term
  where
    from_term :: Term a -> Expr a
    from_term (Term coeff monomial) = 
      foldr (BinaryOp Mul) (Const coeff) (from_var <$> monomial)

    from_var :: (Var, Int) -> Expr a
    from_var (var, n) 
      | n == 1 = Var var
      | n > 1  = UnaryOp (Exp n) (Var var)
      | otherwise = error "Non-positive exponents not supported."

isLinear :: Monomial -> Bool
isLinear [] = True
isLinear [(var, 1)] = True
isLinear _ = False
