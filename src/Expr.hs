module Expr (Atom(..), Expr(..), atoms, rename) where

import Control.Applicative (many, some)
import qualified Text.Megaparsec.Char.Lexer as P
import Data.String (IsString (fromString))
import Control.Monad.Combinators.Expr (Operator (..), makeExprParser)
import Control.Applicative.Combinators ((<|>))
import qualified Text.Megaparsec as P
import qualified Text.Megaparsec.Char as P
import Data.Void (Void)
import qualified Data.Set as S

data Atom = T | F | V String
  deriving (Eq, Ord)

data Expr =
    Atom Atom
  | Not Expr
  | And Expr Expr 
  | Or Expr Expr 
  | Impl Expr Expr 
  | Equiv Expr Expr
  deriving Eq

atoms :: Expr -> [Atom]
atoms expr = case expr of
  Atom at -> [at]
  Not ex  -> atoms ex
  And ex ex' -> atoms ex <> atoms ex'
  Or ex ex' -> atoms ex <> atoms ex'
  Impl ex ex' -> atoms ex <> atoms ex'
  Equiv ex ex' -> atoms ex <> atoms ex'

rename :: (String -> String) -> Expr -> Expr
rename f expr = case expr of
  Atom (V name) -> Atom (V $ f name)
  Atom at -> Atom at
  Not ex  -> Not (rename f ex)
  And ex ex' -> And (rename f ex) (rename f ex')
  Or ex ex' -> Or (rename f ex) (rename f ex')
  Impl ex ex' -> Impl (rename f ex) (rename f ex')
  Equiv ex ex' -> Equiv (rename f ex) (rename f ex')


-- Expression Parsing and Pretty-Printing

type Parser = P.Parsec Void String

parser :: Parser Expr
parser = expr
  where
    lexeme :: Parser a -> Parser a
    lexeme = P.lexeme P.hspace

    atom :: Parser Expr
    atom = Atom <$> P.choice [true, false, var] 
      where
        true  = T <$ lexeme (P.char '1')
        false = F <$ lexeme (P.char '0')
        var   = V <$> lexeme
          ((:) <$> P.letterChar <*> P.many P.alphaNumChar)

    parens :: Parser Expr -> Parser Expr
    parens = P.between (lexeme $ P.char '(') (lexeme $ P.char ')')

    binaryL :: String -> (Expr -> Expr -> Expr) -> Operator Parser Expr
    binaryL name f = InfixL (f <$ lexeme (P.string name))

    binaryR :: String -> (Expr -> Expr -> Expr) -> Operator Parser Expr
    binaryR name f = InfixR (f <$ lexeme (P.string name))

    prefix :: String -> (Expr -> Expr) -> Operator Parser Expr
    prefix name f = Prefix (f <$ lexeme (P.string name))

    operatorTable :: [[Operator Parser Expr]]
    operatorTable = 
      [ [ prefix "-" Not ]
      , [ binaryL "&" And
        , binaryL "|" Or ]
      , [ binaryR "->" Impl ]
      , [ binaryL "<->" Equiv ]
      ]

    expr :: Parser Expr
    expr = makeExprParser (atom <|> parens expr) operatorTable

instance IsString Expr where
  fromString str = 
    case P.parse (parser <* P.eof) "" str of
      Left  err  -> error (P.errorBundlePretty err) 
      Right expr -> expr

instance Show Atom where
  show T = "1"
  show F = "0"
  show (V name) = name

instance Show Expr where
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
      parens :: Expr -> Expr -> String
      parens parent_expr child_expr =
        if precendence child_expr <= precendence parent_expr then
          "(" <> show child_expr <> ")"
        else 
          show child_expr