module Main where
import System.IO (hGetContents', stdin)
import qualified SMT2Parser as P
import Expression (Expr(..), (==>), (<==>), conjunct, disjunct)
import Control.Arrow (second)
import Data.Bifunctor (bimap)

substBool :: String -> Either P.BoolExpr P.AritExpr -> P.BoolExpr -> P.BoolExpr
substBool var ex_subst_with = \case
  P.BoolLit True    -> P.BoolLit True
  P.BoolLit False   -> P.BoolLit False
  P.Rel rel ex1 ex2 -> P.Rel rel ex1 ex2
  P.BoolVar name    ->
    case ex_subst_with of
      Left  bex -> if name == var then bex else P.BoolVar name
      Right _   -> P.BoolVar name
  P.Not ex          -> P.Not (substBool var ex_subst_with ex)
  P.Impl ex1 ex2    -> P.Impl (substBool var ex_subst_with ex1) (substBool var ex_subst_with ex2)
  P.Equiv ex1 ex2   -> P.Equiv (substBool var ex_subst_with ex1) (substBool var ex_subst_with ex2)
  P.And exs         -> P.And (map (substBool var ex_subst_with) exs)
  P.Or exs          -> P.Or (map (substBool var ex_subst_with) exs)
  P.LetExpr defs ex -> P.LetExpr (map (second (bimap (substBool var ex_subst_with) (substArit var ex_subst_with))) defs) (substBool var ex_subst_with ex)

substArit :: String -> Either P.BoolExpr P.AritExpr -> P.AritExpr -> P.AritExpr
substArit var ex_subst_with = \case
  P.Neg ex -> P.Neg (substArit var ex_subst_with ex)
  P.AritVar name ->
    case ex_subst_with of
      Left  _   -> P.AritVar name
      Right aex -> if name == var then aex else P.AritVar name
  P.IntLit lit -> P.IntLit lit
  P.Sub ex1 ex2 -> P.Sub (substArit var ex_subst_with ex1) (substArit var ex_subst_with ex2)
  P.Sum exs -> P.Sum (map (substArit var ex_subst_with) exs)
  P.Mul exs -> P.Mul (map (substArit var ex_subst_with) exs)
  P.Div ex1 ex2 -> P.Div (substArit var ex_subst_with ex1) (substArit var ex_subst_with ex2)
  P.Mod ex1 ex2 -> P.Mod (substArit var ex_subst_with ex1) (substArit var ex_subst_with ex2)
  P.IfThenElse cond ex_then ex_else ->
    P.IfThenElse
      (substBool var ex_subst_with cond)
      (substArit var ex_subst_with ex_then)
      (substArit var ex_subst_with ex_else)

toExpr :: P.BoolExpr -> Expr a
toExpr = \case
  P.BoolLit True    -> T
  P.BoolLit False   -> F
  P.BoolVar name    -> Atom _
  P.Rel rel ex1 ex2 -> Atom _
  P.Not ex          -> Not (toExpr ex)
  P.Impl ex1 ex2    -> toExpr ex1  ==> toExpr ex2
  P.Equiv ex1 ex2   -> toExpr ex1 <==> toExpr ex2
  P.And exs         -> conjunct (map toExpr exs)
  P.Or exs          -> disjunct (map toExpr exs)
  P.LetExpr defs ex -> toExpr $ foldr (uncurry substBool) ex defs

main :: IO ()
main = do
  content <- hGetContents' stdin
  print $ P.parseSmt2 content
