module Theory.NonLinearRealArithmatic.Expr where

import qualified Data.IntMap as M
import Data.IntMap ( IntMap )
import qualified Data.List as L
import Data.Containers.ListUtils ( nubOrd )
import Data.Function ( on )

-- | Variables are simply identified by integers. 
-- That makes it easy to introduce fresh variables by incrementing the 
-- largest used variable.
type Var = Int

-- Non-linear real arithmatic expressions may included addition, subtraction,
-- multiplication, division, exponentiation, roots.
data UnaryOp = Exp Int | Root Int

data BinaryOp = Add | Sub | Mul | Div

data Expr a = 
    Var Var
  | Const a
  | UnaryOp UnaryOp (Expr a)
  | BinaryOp BinaryOp (Expr a) (Expr a)

-- | Collects all variables that appear in an expression.
varsIn :: Expr a -> [Var]
varsIn expr = case expr of 
  Var var -> [var]
  Const _ -> []
  UnaryOp _ sub_expr -> varsIn sub_expr
  BinaryOp _ sub_expr1 sub_expr2 ->
    nubOrd (varsIn sub_expr1 <> varsIn sub_expr2)

substitute :: Var -> Expr a -> Expr a -> Expr a
substitute var expr_subst_with expr_subst_in = 
  case expr_subst_in of
    Const _ -> 
      expr_subst_in
    Var var' -> 
      if var == var' then expr_subst_with else expr_subst_in
    UnaryOp op sub_expr -> 
      UnaryOp op (substitute var expr_subst_with sub_expr)
    BinaryOp op sub_expr1 sub_expr2 -> 
      BinaryOp op 
        (substitute var expr_subst_with sub_expr1)
        (substitute var expr_subst_with sub_expr2)

instance Num a => Num (Expr a) where
  expr1 + expr2 = BinaryOp Add expr1 expr2
  expr1 * expr2 = BinaryOp Mul expr1 expr2
  expr1 - expr2 = BinaryOp Sub expr1 expr2

  abs expr = error "TODO: abs not defined for expr. What would make sense here?"
  signum expr = error "TODO: signum not defined for expr. What would make sense here?"

  fromInteger n = Const (fromInteger n)

{-

domainOf :: Bounded a => Var -> VarDomains a -> Interval a
domainOf = M.findWithDefault Interval.greatest

evalUnaryOp :: (Ord a, Num a, Bounded a, Floating a) => UnaryOp -> Interval a -> [Interval a]
evalUnaryOp symbol int = 
  case symbol of 
    Exp 2 -> [ Interval.square int ] 
    Root 2 -> Interval.squareRoot int
    -- TODO: extend to arbitrary positive exponents/roots
    Exp n -> error "Exponents >2 not supported yet"
    Root n -> error "Roots >2 not supported yet"

evalBinaryOp :: (Ord a, Num a, Bounded a, Fractional a) => BinaryOp -> Interval a -> Interval a -> [Interval a]
evalBinaryOp symbol int1 int2 = 
  case symbol of 
    Add -> [ int1 + int2 ]
    Sub -> [ int1 - int2 ]
    Mul -> [ int1 * int2 ]
    Div -> do 
      int2' <- Interval.reciprocal int2
      return (int1 * int2)

evalExpr :: (Ord a, Bounded a, Floating a) => VarDomains a -> Expr a -> [Interval a]
evalExpr var_domains expr = reduce $
  case expr of
    Var var -> [ domainOf var var_domains ]

    Const a -> [ Interval.singleton a ]

    UnaryOp op_symbol expr -> do 
      value <- eval var_domains expr
      evalUnaryOp op_symbol value

    BinaryOp op_symbol expr1 expr2 -> do
      value1 <- eval var_domains expr1
      value2 <- eval var_domains expr2
      evalBinaryOp op_symbol value1 value2
-}
