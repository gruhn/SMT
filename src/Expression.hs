{-# LANGUAGE FlexibleInstances #-}
module Expression (Atom(..), Expr(..), atoms) where

import Control.Applicative (many, some)
import qualified Text.Megaparsec.Char.Lexer as P
import Data.String (IsString (fromString))
import Control.Monad.Combinators.Expr (Operator (..), makeExprParser)
import Control.Applicative.Combinators ((<|>))
import qualified Text.Megaparsec as P
import qualified Text.Megaparsec.Char as P
import Data.Void (Void)
import qualified Data.Set as S

data Atom a = T | F | V a
  deriving (Eq, Ord)

instance Functor Atom where
  fmap f (V a) = V (f a)
  fmap f T = T
  fmap f F = F

data Expr a =
    Atom (Atom a)
  | Not (Expr a)
  | And (Expr a) (Expr a)
  | Or (Expr a) (Expr a)
  | Impl (Expr a) (Expr a)
  | Equiv (Expr a) (Expr a)
  deriving Eq

instance Functor Expr where
  fmap f expr  = case expr of
    Atom (V name) -> Atom (V $ f name)
    Atom at -> Atom (fmap f at)
    Not ex  -> Not (fmap f ex)
    And ex ex' -> And (fmap f ex) (fmap f ex')
    Or ex ex' -> Or (fmap f ex) (fmap f ex')
    Impl ex ex' -> Impl (fmap f ex) (fmap f ex')
    Equiv ex ex' -> Equiv (fmap f ex) (fmap f ex')

atoms :: Expr a -> [Atom a]
atoms expr = case expr of
  Atom at -> [at]
  Not ex  -> atoms ex
  And ex ex' -> atoms ex <> atoms ex'
  Or ex ex' -> atoms ex <> atoms ex'
  Impl ex ex' -> atoms ex <> atoms ex'
  Equiv ex ex' -> atoms ex <> atoms ex'

-- Expression Parsing and Pretty-Printing

type Parser = P.Parsec Void String

parser :: Parser (Expr String)
parser = expr
  where
    lexeme :: Parser a -> Parser a
    lexeme = P.lexeme P.hspace

    atom :: Parser (Expr String)
    atom = Atom <$> P.choice [true, false, var] 
      where
        true  = T <$ lexeme (P.char '1')
        false = F <$ lexeme (P.char '0')
        var   = V <$> lexeme
          ((:) <$> P.letterChar <*> P.many P.alphaNumChar)

    parens :: Parser (Expr String) -> Parser (Expr String)
    parens = P.between (lexeme $ P.char '(') (lexeme $ P.char ')')

    binaryL :: String -> (Expr String -> Expr String -> Expr String) -> Operator Parser (Expr String)
    binaryL name f = InfixL (f <$ lexeme (P.string name))

    binaryR :: String -> (Expr String -> Expr String -> Expr String) -> Operator Parser (Expr String)
    binaryR name f = InfixR (f <$ lexeme (P.string name))

    prefix :: String -> (Expr String -> Expr String) -> Operator Parser (Expr String)
    prefix name f = Prefix (f <$ lexeme (P.string name))

    operatorTable :: [[Operator Parser (Expr String)]]
    operatorTable = 
      [ [ prefix "-" Not ]
      , [ binaryL "&" And
        , binaryL "|" Or ]
      , [ binaryR "->" Impl ]
      , [ binaryL "<->" Equiv ]
      ]

    expr :: Parser (Expr String)
    expr = makeExprParser (atom <|> parens expr) operatorTable

instance IsString (Expr String) where
  fromString str = 
    case P.parse (parser <* P.eof) "" str of
      Left  err  -> error (P.errorBundlePretty err) 
      Right expr -> expr

instance Show (Atom String) where
  show T = "1"
  show F = "0"
  show (V name) = name

-- instance Show a => Show (Atom a) where
--   show T = "1"
--   show F = "0"
--   show (V name) = show name

instance Show (Expr String) where
  show expr = case expr of
    Atom atom   -> show atom
    Not e       -> "-" <> parens expr e
    And e1 e2   -> parens expr e1 <> " & "   <> parens expr e2
    Or e1 e2    -> parens expr e1 <> " | "   <> parens expr e2
    Impl e1 e2  -> parens expr e1 <> " -> "  <> parens expr e2
    Equiv e1 e2 -> parens expr e1 <> " <-> " <> parens expr e2
    where
      precendence op = case op of 
        Atom _ -> 3; Not _ -> 3;
        And  _ _ -> 2; Or _ _ -> 2;
        Impl _ _ -> 1; Equiv _ _ -> 0

      -- TODO: avoid unnecessary parenthesis when precedences is implied by
      -- operator associativity.
      parens :: Expr String -> Expr String -> String
      parens parent_expr child_expr =
        if precendence child_expr <= precendence parent_expr then
          "(" <> show child_expr <> ")"
        else 
          show child_expr