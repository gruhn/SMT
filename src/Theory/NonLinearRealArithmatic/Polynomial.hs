module Theory.NonLinearRealArithmatic.Polynomial where

import Theory.NonLinearRealArithmatic.Expr (Expr(..), Var, BinaryOp(..), UnaryOp(..))
import qualified Data.Vector as V
import qualified Data.List as L
import qualified Data.IntMap as M
import qualified Data.IntSet as S
import Data.IntMap ( IntMap )
import Data.Function ( on )

-- | Map of variables to integer exponents.
type Monomial = IntMap Int

data Term a = Term { getCoeff :: a, getMonomial :: Monomial }

modifyCoeff :: (a -> a) -> Term a -> Term a
modifyCoeff f (Term coeff monomial) = Term (f coeff) monomial

modifyMonomial :: (Monomial -> Monomial) -> Term a -> Term a
modifyMonomial f (Term coeff monomial) = Term coeff (f monomial)


newtype Polynomial a = Polynomial { getTerms :: [Term a] }

instance (Ord a, Num a) => Num (Polynomial a) where
  (Polynomial p1) + (Polynomial p2) = Polynomial $ combineTerms (p1 <> p2)
  
  (Polynomial p1) * (Polynomial p2) = Polynomial $ do
    Term coeff1 exps1 <- p1
    Term coeff2 exps2 <- p2
    -- Sum up exponents of same variables.
    return $ Term (coeff1*coeff2) $ M.unionWith (+) exps1 exps2

  abs (Polynomial p) = Polynomial (modifyCoeff abs <$> p)

  negate (Polynomial p) = Polynomial (modifyCoeff negate <$> p)

  signum (Polynomial p) = Polynomial (modifyCoeff signum <$> p)

  fromInteger i = Polynomial [Term (fromInteger i) M.empty]
  
-- Combine terms with same monomial, e.g. combine 3*x*y and 2*y*x to 5*x*y.
--
--  1.  Sort the terms BY the monomials, so equal monomials are next to each other. 
--
--  2.  `go` over the terms and sum up equal monomials.
--
--  3.  Some terms now might have coefficient `0`. Filter them out.
--
combineTerms :: forall a. (Num a, Ord a) => [Term a] -> [Term a]
combineTerms = filter ((/= 0) . getCoeff) . go . L.sortBy (compare `on` getMonomial)
  where
    go :: [Term a] -> [Term a]
    go (Term coeff1 monomial1 : Term coeff2 monomial2 : terms)
      | monomial1 == monomial2 = go (Term (coeff1+coeff2) monomial1 : terms)
      | otherwise = Term coeff1 monomial1 : go (Term coeff2 monomial2 : terms)
    go terms = terms

--- TODO: make polynomial instance of Num
-- newtype Polynomial' a = Polynomial' { getTerms :: [Term a] }
-- instance Num a => Num (Polynomial' a) where
--   p1 + p2 = j


derivative :: Polynomial a -> Polynomial a
derivative = undefined -- TODO

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
--       property test "all coeffitients are always non-zero"
--       property test "key set of all monomials is the same"
--
fromExpr :: forall a. (Ord a, Num a) => Expr a -> Polynomial a
fromExpr = expand
  where
    -- Multiply out nested expressions and eliminate subtractions until
    -- we are left with a big sum, where each summand is composed of a 
    -- a constant coefficient and a monomial. That leaves potentially 
    -- many terms that can be summed up and combined into one term. 
    -- Do that separately with `sum_coeffs`.
    expand :: Expr a -> Polynomial a
    expand expr =
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
            expand expr
          else 
            expand $ BinaryOp Mul expr (UnaryOp (Exp (n-1)) expr)

        BinaryOp Add expr1 expr2 -> expand expr1 + expand expr2
        BinaryOp Sub expr1 expr2 -> expand expr1 - expand expr2
        BinaryOp Mul expr1 expr2 -> expand expr1 * expand expr2
        BinaryOp Div _ _ -> error "Division in user provided expressions not supported"

    -- -- Make sure each monomial has default entry of zero for each 
    -- -- variable that is in use in the polynomial.        
    -- fill :: Polynomial a -> Polynomial a
    -- fill polynomial = polynomial'
    --   where
    --     zero = M.fromSet (const 0) (varsIn polynomial)
    --     polynomial' =  modifyMonomial (<> zero) <$> polynomial

toExpr :: forall a. (Ord a, Num a) => Polynomial a -> Expr a
toExpr = foldr1 (BinaryOp Add) . fmap from_term . getTerms
  where
    from_term :: Term a -> Expr a
    from_term (Term coeff monomial) = 
      foldr (BinaryOp Mul) (Const coeff) (M.mapWithKey from_var monomial)

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
    
degree :: (Num a, Ord a) => Polynomial a -> Int
degree = maximum . fmap (sum . getMonomial) . getTerms

eval :: forall a. Num a => IntMap a -> Polynomial a -> a
eval assignment polynomial = sum (eval_term <$> getTerms polynomial)
  where
    eval_term :: Term a -> a
    eval_term (Term coeff monomial) = coeff * eval_monomial monomial
    
    eval_monomial :: Monomial -> a
    eval_monomial monomial = value
      where
        vars = S.toList $ M.keysSet assignment <> M.keysSet monomial
    
        get_base var = M.findWithDefault 1 var assignment
        get_exp var = M.findWithDefault 0 var monomial
    
        value = product [ get_base var ^ get_exp var | var <- vars ]

varsIn :: Polynomial a -> S.IntSet
varsIn = S.unions . fmap (M.keysSet . getMonomial) . getTerms
