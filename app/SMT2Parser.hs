{-# HLINT ignore "Use <$>" #-}
module SMT2Parser 
  ( parseSmt2
  , Logic(..)
  , ValType(..)
  , SMT2(..)
  , BoolExpr(..)
  , AritExpr(..)
  ) where

import Text.Megaparsec (Parsec, Tokens, between, anySingleBut, noneOf, choice, MonadParsec (try), parse, optional)
import Data.Void (Void)
import qualified Text.Megaparsec.Char.Lexer as Lexer
import Text.Megaparsec.Char (space1)
import Control.Applicative (empty, (<|>), Alternative (..))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Bifunctor (bimap)
import Text.Megaparsec.Error (errorBundlePretty)

parseSmt2 :: String -> SMT2
parseSmt2 input = 
  case parse smt2 "" input of
    Left  err    -> error (errorBundlePretty err)
    Right output -> output

type Parser = Parsec Void String

space :: Parser ()
space = Lexer.space space1 (Lexer.skipLineComment ";") empty

symbol :: Tokens String -> Parser (Tokens String)
symbol = Lexer.symbol space

lexeme :: Parser a -> Parser a
lexeme = Lexer.lexeme space

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

identifier :: Parser String
identifier =
  let 
    raw :: Parser String
    raw = lexeme (some $ noneOf "|\"() \n")

    escaped :: Parser String
    escaped = between (symbol "|") (symbol "|") $ some $ anySingleBut '|'

    quoted :: Parser String
    quoted = between (symbol "\"") (symbol "\"") $ some $ anySingleBut '"'
  in
    escaped <|> quoted <|> raw

data ValType = ValTypeBool | ValTypeInt | ValTypeReal
  deriving (Eq, Ord)

data Logic = QF_LRA -- TODO: add more logics
  deriving Show

type TypedVar = (String, ValType)

data SMT2 = SMT2 
  { getLogic      :: Logic
  , getVarDecls   :: Map String ValType
  , getAssertions :: [BoolExpr]
  }

data AritExpr 
  = Neg AritExpr
  | AritVar String
  | IntLit Integer
  | Sub AritExpr AritExpr
  | Sum [AritExpr]
  | Mul [AritExpr]
  | Div AritExpr AritExpr
  | Mod AritExpr AritExpr
  | IfThenElse BoolExpr AritExpr AritExpr
  deriving (Eq, Ord)

data AritRel = LessThan | LessEquals | Equals | GreaterEquals | GreaterThan
  deriving (Eq, Ord)

data BoolExpr 
  = BoolLit Bool
  | BoolVar String
  | Rel AritRel AritExpr AritExpr
  | Not BoolExpr
  | Impl BoolExpr BoolExpr
  | Equiv BoolExpr BoolExpr
  | And [BoolExpr]
  | Or [BoolExpr]
  | LetExpr [(String, Either BoolExpr AritExpr)] BoolExpr
  deriving (Eq, Ord)

logic :: Parser Logic
logic = parens $ do 
  symbol "set-logic"
  choice
    [ QF_LRA <$ symbol "QF_LRA"
    ]

info :: Parser (String, String)
info = parens $ do 
  symbol "set-info" 
  label <- identifier 
  value <- identifier
  return (label, value)

valType :: Parser ValType
valType = choice 
  [ ValTypeInt  <$ symbol "Int"
  , ValTypeBool <$ symbol "Bool"
  , ValTypeReal <$ symbol "Real"
  ]

typedVar :: Parser TypedVar
typedVar = (,) <$> identifier <*> valType

funDecl :: Parser (String, ValType)
funDecl = parens $ do
  symbol "declare-fun"
  var <- identifier
  symbol "()"
  var_type <- valType
  return (var, var_type)

assertion :: Map String ValType -> Parser BoolExpr
assertion vars = parens $ do
  symbol "assert"
  boolExpr vars

boolExpr :: Map String ValType -> Parser BoolExpr
boolExpr var_defs = bool_expr
  where
    (bool_vars, arit_vars) = 
        bimap Map.keys Map.keys 
      $ Map.partition (== ValTypeBool) var_defs

    arit_lit = lexeme (IntLit <$> Lexer.decimal)
    arit_div = parens (Div <$ symbol "/"   <*> arit_expr <*> arit_expr)
    arit_mod = parens (Mod <$ symbol "mod" <*> arit_expr <*> arit_expr)
    arit_sum = parens (Sum <$ symbol "+" <*> some arit_expr)
    arit_mul = parens (Mul <$ symbol "*" <*> some arit_expr)

    arit_neg_or_sub :: Parser AritExpr
    arit_neg_or_sub = parens $ do
      symbol "-"
      ex1 <- arit_expr
      maybe_ex2 <- optional arit_expr
      return $ case maybe_ex2 of
        Nothing  -> Neg ex1
        Just ex2 -> Sub ex1 ex2

    arit_var = do
      var <- identifier 
      if var `elem` arit_vars then
        return (AritVar var)
      else
        fail ("undefined arithmatic variable " ++ var)

    arit_expr :: Parser AritExpr
    arit_expr = choice 
      [ try arit_neg_or_sub
      , try arit_lit
      , try arit_sum
      , try arit_mul
      , try arit_div      
      , try arit_mod
      , try arit_ite
      , arit_var
      ]

    arit_rel :: Parser AritRel
    arit_rel = choice
      [ LessEquals    <$ symbol "<="
      , LessThan      <$ symbol "<"
      , Equals        <$ symbol "="
      , GreaterEquals <$ symbol ">="
      , GreaterThan   <$ symbol ">" 
      ]

    arit_ite :: Parser AritExpr
    arit_ite = 
      parens $ do
        symbol "ite"
        condition <- bool_expr
        then_case <- arit_expr
        else_case <- arit_expr
        return $ IfThenElse condition then_case else_case

    bool_lit :: Parser BoolExpr
    bool_lit = choice
      [ BoolLit True  <$ symbol "true"
      , BoolLit False <$ symbol "false"
      ]

    let_expr :: Parser BoolExpr
    let_expr = 
      parens $ do
        symbol "let"

        let_defs <- parens $
          many $ parens $ do
            var  <- identifier
            expr <- (Left <$> bool_expr) <|> (Right <$> arit_expr)
            return (var, expr)

        let new_var_defs :: Map String ValType
            new_var_defs = Map.fromList $ do 
              (var, expr) <- let_defs
              return $ case expr of
                Left _  -> (var, ValTypeBool)
                Right _ -> (var, ValTypeInt)

        let_body <- boolExpr (new_var_defs <> var_defs)

        return (LetExpr let_defs let_body)

    bool_var :: Parser BoolExpr
    bool_var = do 
      var <- identifier
      if var `elem` bool_vars then
        return (BoolVar var)
      else
        fail ("undefined boolean variable " ++ var)

    rel :: Parser BoolExpr
    rel = parens (Rel <$> arit_rel <*> arit_expr <*> arit_expr)

    not_expr   = parens (Not   <$ symbol "not" <*> bool_expr)
    impl_expr  = parens (Impl  <$ symbol "=>"  <*> bool_expr <*> bool_expr)
    equiv_expr = parens (Equiv <$ symbol "="   <*> bool_expr <*> bool_expr)
    or_expr    = parens (Or    <$ symbol "or"  <*> some bool_expr)
    and_expr   = parens (And   <$ symbol "and" <*> some bool_expr)

    bool_expr :: Parser BoolExpr
    bool_expr = choice
      [ try not_expr
      , try equiv_expr 
      , try and_expr
      , try or_expr
      , try impl_expr
      , try let_expr
      -- , try bool_ite
      , try rel
      , try bool_lit
      , bool_var
      ]

smt2 :: Parser SMT2
smt2 = do
  space
  many (try info)
  smt_logic <- logic
  many (try info)
  decls   <- Map.fromList <$> many (try funDecl)
  asserts <- many (try (assertion decls))
  symbol "(check-sat)"
  symbol "(exit)"
  return (SMT2 smt_logic decls asserts)
 
----------------------------------------------------

instance Show AritExpr where
  show = \case 
    Div ex1 ex2  -> "(/ "   ++ show ex1 ++ " " ++ show ex2 ++ ")"
    Mod ex1 ex2  -> "(mod " ++ show ex1 ++ " " ++ show ex2 ++ ")"
    Sub ex1 ex2  -> "(- "   ++ show ex1 ++ " " ++ show ex2 ++ ")"
    Mul exs      -> "(* " ++ unwords (show <$> exs) ++ ")"
    Sum exs      -> "(+ " ++ unwords (show <$> exs) ++ ")"
    Neg ex       -> "(- " ++ show ex ++ ")"
    AritVar name -> name
    IntLit int   ->
      if int < 0 then
        show $ Neg $ IntLit $ abs int
      else
        show int
    IfThenElse cond then_case else_case -> 
      "(ite " ++ show cond ++ " " ++ show then_case ++ " " ++ show else_case ++ ")"

instance Show AritRel where 
  show = \case
    LessThan -> "<"
    LessEquals -> "<="
    Equals -> "="
    GreaterEquals -> ">="
    GreaterThan -> ">"

instance Show BoolExpr where
  show = \case
    BoolLit True    -> "true"
    BoolLit False   -> "false"
    BoolVar name    -> name
    Rel rel ex1 ex2 -> "(" ++ show rel ++ " " ++ show ex1 ++ " " ++ show ex2 ++ ")"
    Not ex          -> "(not " ++ show ex ++ ")"
    Impl ex1 ex2    -> "(=> " ++ show ex1 ++ " " ++ show ex2 ++ ")"
    Equiv ex1 ex2   -> "(= " ++ show ex1 ++ " " ++ show ex2 ++ ")"
    And exs         -> "(and " ++ unwords (map show exs) ++ ")"
    Or exs          -> "(or " ++ unwords (map show exs) ++ ")"
    LetExpr defs ex -> "(let (" ++ unwords (map show_def defs) ++ ") " ++ show ex ++ ")"
      where
        show_def (vname, expr) = 
          case expr of 
            Left bexpr  -> unwords ["(", vname, show bexpr, ")"]
            Right aexpr -> unwords ["(", vname, show aexpr, ")"]

instance Show ValType where
  show = \case
    ValTypeBool -> "Bool"
    ValTypeInt  -> "Int"
    ValTypeReal -> "Real"

instance Show SMT2 where
  show (SMT2 smt_logic decls asserts) =
    let 
      show_decl :: (String, ValType) -> String
      show_decl (var, val_type) = 
        "(declare-fun " ++ var ++ " () " ++ show val_type ++ ")"

      show_assert :: BoolExpr -> String
      show_assert bool_expr = 
        "(assert " ++ show bool_expr ++ ")"

      (\\) :: String -> String -> String
      (\\) str1 str2 = str1 ++ "\n" ++ str2
    in
      "(set-logic " ++ show smt_logic ++ ")" \\
      unlines (map show_decl (Map.toList decls)) \\
      unlines (map show_assert asserts) \\
      "(check-sat)" \\
      "(exit)"
     
