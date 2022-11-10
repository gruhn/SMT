{-# LANGUAGE FlexibleInstances #-}
module Expression
  ( Expr(..)
  , atoms
  , conjunct
  , disjunct
  , negationNormalForm
  , eliminateConstants
  , subExpressions
  ) where

import           Control.Applicative            ( many
                                                , some
                                                )
import           Control.Applicative.Combinators
                                                ( (<|>) )
import           Control.Monad                  ( (>=>) )
import           Control.Monad.Combinators.Expr ( Operator(..)
                                                , makeExprParser
                                                )
import qualified Data.Set                      as S
import           Data.String                    ( IsString(fromString) )
import           Data.Void                      ( Void )
import qualified Text.Megaparsec               as P
import qualified Text.Megaparsec.Char          as P
import qualified Text.Megaparsec.Char.Lexer    as P
import           Text.Read                      ( Lexeme(String) )
import           Utils                          ( fixpoint )

data Expr a =
    T
  | F
  | Atom a
  | Not (Expr a)
  | And (Expr a) (Expr a)
  | Or (Expr a) (Expr a)
  | Impl (Expr a) (Expr a)
  | Equiv (Expr a) (Expr a)
  deriving Eq

instance Functor Expr where
  fmap f expr = case expr of
    T            -> T
    F            -> F
    Atom at      -> Atom (f at)
    Not  ex      -> Not (fmap f ex)
    And   ex ex' -> And (fmap f ex) (fmap f ex')
    Or    ex ex' -> Or (fmap f ex) (fmap f ex')
    Impl  ex ex' -> Impl (fmap f ex) (fmap f ex')
    Equiv ex ex' -> Equiv (fmap f ex) (fmap f ex')

subExpressions :: Expr a -> [Expr a]
subExpressions expr = expr : case expr of
  T            -> []
  F            -> []
  Atom at      -> []
  Not  ex      -> subExpressions ex
  And   ex ex' -> subExpressions ex <> subExpressions ex'
  Or    ex ex' -> subExpressions ex <> subExpressions ex'
  Impl  ex ex' -> subExpressions ex <> subExpressions ex'
  Equiv ex ex' -> subExpressions ex <> subExpressions ex'

atoms :: Expr a -> [a]
atoms expr = do
  ex <- subExpressions expr
  case ex of
    Atom at -> [at]
    _       -> []

conjunct :: [Expr a] -> Expr a
conjunct []       = T
conjunct (e : es) = foldr And e es

disjunct :: [Expr a] -> Expr a
disjunct []       = F
disjunct (e : es) = foldr Or e es

-- substitute syntax sugar, i.e. implication and equivalence operators, with and/or/not
desugar :: Expr a -> Expr a
desugar (e1 `Impl`  e2) = Not e1 `Or` e2
desugar (e1 `Equiv` e2) = desugar (e1 `Impl` e2) `And` desugar (e2 `Impl` e1)
desugar e               = e

negationNormalForm :: Expr a -> Expr a
negationNormalForm = go_id
 where
  go_id :: Expr a -> Expr a
  go_id expr = case expr of
    T             -> T
    F             -> F
    Not  e        -> go_not e
    Atom e        -> Atom e
    e1 `And` e2   -> go_id e1 `And` go_id e2
    e1 `Or`  e2   -> go_id e1 `Or` go_id e2
    impl_or_equiv -> go_id (desugar impl_or_equiv)

  go_not :: Expr a -> Expr a
  go_not expr = case expr of
    T             -> F
    F             -> T
    Not  e        -> go_id e
    Atom e        -> Not (Atom e)
    -- DeMorgan rules:
    e1 `And` e2   -> go_not e1 `Or` go_not e2
    e1 `Or`  e2   -> go_not e1 `And` go_not e2
    impl_or_equiv -> go_not (desugar impl_or_equiv)

-- Removes all boolean constants (0/1) unless the expression is 
-- a tautology/unsatisfiable then the output expression might 
-- reduce to just `Atom T` or `Atom F`.
eliminateConstants :: Eq a => Expr a -> Expr a
eliminateConstants = fixpoint go
 where
  go :: Expr a -> Expr a
  go expr = case expr of
    T       -> T
    F       -> F
    Atom e  -> Atom e

    Not  ex -> case ex of
      T -> F
      F -> T
      _ -> Not ex

    And ex_l ex_r -> case (ex_l, ex_r) of
      (T, _) -> go ex_r
      (_, T) -> go ex_l
      (F, _) -> F
      (_, F) -> F
      _      -> And (go ex_l) (go ex_r)

    Or ex_l ex_r -> case (ex_l, ex_r) of
      (T, _) -> T
      (_, T) -> T
      (F, _) -> go ex_r
      (_, F) -> go ex_l
      _      -> Or (go ex_l) (go ex_r)

    Impl ex_l ex_r -> case (ex_l, ex_r) of
      (T, _) -> go ex_r
      (_, T) -> T
      (F, _) -> T
      (_, F) -> Not (go ex_l)
      _      -> Impl (go ex_l) (go ex_r)

    Equiv ex_l ex_r -> case (ex_l, ex_r) of
      (T, _) -> go ex_r
      (_, T) -> go ex_l
      (F, _) -> Not (go ex_r)
      (_, F) -> Not (go ex_l)
      _      -> Equiv (go ex_l) (go ex_r)


-- Expression Parsing and Pretty-Printing

type Parser = P.Parsec Void String

parser :: Parser (Expr String)
parser = expr
 where
  lexeme :: Parser a -> Parser a
  lexeme = P.lexeme P.hspace

  atom :: Parser (Expr String)
  atom = P.choice [true, false, var]
   where
    true  = T <$ lexeme (P.char '1')
    false = F <$ lexeme (P.char '0')

    var   = Atom <$> lexeme ((:) <$> P.letterChar <*> P.many P.alphaNumChar)

  parens :: Parser (Expr String) -> Parser (Expr String)
  parens = P.between (lexeme $ P.char '(') (lexeme $ P.char ')')

  binaryL
    :: String
    -> (Expr String -> Expr String -> Expr String)
    -> Operator Parser (Expr String)
  binaryL name f = InfixL (f <$ lexeme (P.string name))

  binaryR
    :: String
    -> (Expr String -> Expr String -> Expr String)
    -> Operator Parser (Expr String)
  binaryR name f = InfixR (f <$ lexeme (P.string name))

  prefix
    :: String -> (Expr String -> Expr String) -> Operator Parser (Expr String)
  prefix name f = Prefix (f <$ lexeme (P.string name))

  operatorTable :: [[Operator Parser (Expr String)]]
  operatorTable =
    [ [prefix "-" Not]
    , [binaryL "&" And, binaryL "|" Or]
    , [binaryR "->" Impl]
    , [binaryL "<->" Equiv]
    ]

  expr :: Parser (Expr String)
  expr = makeExprParser (atom <|> parens expr) operatorTable

instance IsString (Expr String) where
  fromString str = case P.parse (parser <* P.eof) "" str of
    Left  err  -> error (P.errorBundlePretty err)
    Right expr -> expr

instance Show (Expr String) where
  show expr = case expr of
    T           -> "1"
    F           -> "0"
    Atom var    -> var
    Not  e      -> "-" <> parens expr e
    And   e1 e2 -> parens expr e1 <> " & " <> parens expr e2
    Or    e1 e2 -> parens expr e1 <> " | " <> parens expr e2
    Impl  e1 e2 -> parens expr e1 <> " -> " <> parens expr e2
    Equiv e1 e2 -> parens expr e1 <> " <-> " <> parens expr e2
   where
    precendence op = case op of
      T         -> 3
      F         -> 3
      Atom _    -> 3
      Not  _    -> 3
      And   _ _ -> 2
      Or    _ _ -> 2
      Impl  _ _ -> 1
      Equiv _ _ -> 0

    -- TODO: avoid unnecessary parenthesis when precedences is implied by
    -- operator associativity.
    parens :: Expr String -> Expr String -> String
    parens parent_expr child_expr =
      if precendence child_expr <= precendence parent_expr
        then "(" <> show child_expr <> ")"
        else show child_expr
