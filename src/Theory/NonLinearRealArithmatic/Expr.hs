module Theory.NonLinearRealArithmatic.Expr where

import qualified Theory.NonLinearRealArithmatic.Interval as Interval
import Theory.NonLinearRealArithmatic.Interval ( Interval )
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

data Relation = LessThan | Equals | LessThanOrEquals

-- | Assuming the expression forms the left-hand-side of the relation, 
-- while the right-hand-side is always zero, e.g. 
-- 
--    x + 3*y - 10 <= 0
-- 
type Constraint a = (Relation, Expr a)

-- Expression evaluation using interval arithmatic

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

type VarDomains a = IntMap (Interval a)

domainOf :: Bounded a => Var -> VarDomains a -> Interval a
domainOf = M.findWithDefault Interval.greatest

eval :: (Ord a, Bounded a, Floating a) => VarDomains a -> Expr a -> [Interval a]
eval var_domains expr = Interval.reduce $
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

-- | Collects all variables that appear in an expression.
varsIn :: Expr a -> [Var]
varsIn expr = case expr of 
  Var var -> [var]
  Const _ -> []
  UnaryOp _ sub_expr -> varsIn sub_expr
  BinaryOp _ sub_expr1 sub_expr2 ->
    nubOrd (varsIn sub_expr1 <> varsIn sub_expr2)

-- TODO
solveFor :: Expr a -> Var -> Expr a
solveFor = undefined
