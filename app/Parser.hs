{-# HLINT ignore "Use <$>" #-}
module Parser where

import Text.Megaparsec (Parsec, choice, between, some, try, errorBundlePretty, parse, oneOf, notFollowedBy, manyTill, Tokens, anySingleBut)
import Data.Void (Void)
import qualified Text.Megaparsec.Char.Lexer as L
import qualified Text.Megaparsec.Char as C
import Control.Applicative ((<|>), Alternative (many, empty))
import Data.Either (partitionEithers)
import Data.Foldable (find)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Bifunctor (bimap)
import Data.Maybe (isJust)
import Data.List (partition)

parseSmt2 :: String -> SMT2
parseSmt2 input = 
  case parse smt2 "" input of
    Left  err    -> error (errorBundlePretty err)
    Right output -> output

data AritExpr 
  = Neg AritExpr
  | AritVar String
  | IntLit Integer
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

data Predicate = Predicate
  { getPredicateName :: String 
  , getPredicateArgs :: [String]
  } deriving (Ord, Eq)

data CHC = CHC 
  { getVars :: Map String ValType
  , getLHS :: Set Predicate
  , getConstr :: BoolExpr
  , getRHS :: Maybe Predicate
  } deriving Eq

modifyLHS :: (Set Predicate -> Set Predicate) -> CHC -> CHC
modifyLHS f clause = clause { getLHS = f (getLHS clause) }

modifyConstr :: (BoolExpr -> BoolExpr) -> CHC -> CHC
modifyConstr f clause = clause { getConstr = f (getConstr clause) }

data SMT2 = SMT2
  { getPredicateDecls :: [PredicateDecl]
  , getClauses :: [CHC]
  } deriving Eq

modifyClauses :: ([CHC] -> [CHC]) -> SMT2 -> SMT2
modifyClauses f file = file { getClauses = f (getClauses file) }

------------------------------------------

type Parser = Parsec Void String

space :: Parser ()
space = L.space C.space1 (L.skipLineComment ";") empty

symbol :: Tokens String -> Parser (Tokens String)
symbol = L.symbol space

lexeme :: Parser a -> Parser a
lexeme = L.lexeme space

smt2 :: Parser SMT2
smt2 = do
  space
  symbol "(set-logic HORN)"
  pred_decls <- manyTill predicateDecl (notFollowedBy predicateDecl)
  clauses    <- manyTill (chc pred_decls) $ do
    symbol "(check-sat)"
    symbol "(exit)"
  return (SMT2 pred_decls clauses)

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

boolExpr :: Map String ValType -> Parser BoolExpr
boolExpr var_defs = bool_expr
  where
    (bool_vars, arit_vars) = 
        bimap Map.keys Map.keys 
      $ Map.partition (== ValTypeBool) var_defs

    arit_lit = L.lexeme space (IntLit <$> L.decimal)
    arit_neg = parens (Neg <$ symbol "-" <*> arit_expr)
    arit_div = parens (Div <$ symbol "div" <*> arit_expr <*> arit_expr)
    arit_mod = parens (Mod <$ symbol "mod" <*> arit_expr <*> arit_expr)
    arit_sum = parens (Sum <$ symbol "+" <*> some arit_expr)
    arit_mul = parens (Mul <$ symbol "*" <*> some arit_expr)

    arit_var = do
      var <- identifier 
      if var `elem` arit_vars then
        return (AritVar var)
      else
        fail ("undefined arithmatic variable " ++ var)

    arit_expr :: Parser AritExpr
    arit_expr = choice 
      [ try arit_neg
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

data ValType = ValTypeBool | ValTypeInt
  deriving (Eq, Ord)

valType :: Parser ValType
valType = choice 
  [ ValTypeInt  <$ symbol "Int"
  , ValTypeBool <$ symbol "Bool"
  ]

identifier :: Parser String
identifier = 
  L.lexeme space $ some $ C.alphaNumChar <|> oneOf "@.!_-^$/:"

identifierBracketed :: Parser String
identifierBracketed = 
  between (symbol "|") (symbol "|") $ some $ anySingleBut '|'

chc :: [PredicateDecl] -> Parser CHC
chc pred_decls = assert_stmt
  where
    assert_stmt = 
      parens $ do 
        symbol "assert" 
        parens $ do
          symbol "forall"
          var_defs <- Map.fromList <$> parens (many varDef)
          parens $ do
            symbol "=>"
            (lhs_preds, constraints) <- chc_lhs var_defs
            rhs <- chc_rhs
            return (CHC var_defs lhs_preds constraints rhs)

    chc_lhs :: Map String ValType -> Parser (Set Predicate, BoolExpr)
    chc_lhs var_defs = 
      parens $ do
        symbol "and"

        let expr_or_pred :: Parser (Either BoolExpr Predicate)
            expr_or_pred = 
                  (Left <$> try (boolExpr var_defs)) 
              <|> (Right <$> predicate pred_decls)

        (expr_list, pred_list) <- partitionEithers <$> many expr_or_pred 

        return (Set.fromList pred_list, And expr_list)
    
    chc_rhs :: Parser (Maybe Predicate)
    chc_rhs = (Nothing <$ symbol "false") <|> (Just <$> predicate pred_decls)

varDef :: Parser (String, ValType)
varDef = parens $ do 
  vname <- identifier
  vtype <- valType
  return (vname, vtype)

predicate :: [PredicateDecl] -> Parser Predicate
predicate pred_decls = no_parens <|> with_parens
  where
    no_parens = do
      pred_name <- identifierBracketed <|> identifier
      case find ((== pred_name) . getPredName) pred_decls of
        Nothing -> 
          fail $ "undefined 0-arity predicate " ++ pred_name
        Just (PredicateDecl _ []) -> 
          return (Predicate pred_name [])
        Just (PredicateDecl _ arg_types) -> 
          fail $ 
              "expected " 
            ++ show (length arg_types) 
            ++ " arguments for predicate " 
            ++ pred_name 
            ++ " but 0 given" 

    with_parens =
      parens $ do
        pred_name <- identifierBracketed <|> identifier
        arg_vars <- many identifier
        case find ((== pred_name) . getPredName) pred_decls of
          Nothing -> 
            fail $ "undefined " ++ show (length arg_vars) ++ "-arity predicate " ++ pred_name
          Just (PredicateDecl _ arg_types) -> do
            if length arg_types == length arg_vars then
              -- TODO check that argument types match
              return (Predicate pred_name arg_vars)
            else
              fail $ 
                  "expected " 
                ++ show (length arg_types) 
                ++ " arguments for predicate " 
                ++ pred_name 
                ++ " but " 
                ++ show (length arg_vars)
                ++ " given" 
              

data PredicateDecl = PredicateDecl 
  { getPredName :: String 
  , getPredArgTypes :: [ValType]
  } deriving (Eq, Ord)

predicateDecl :: Parser PredicateDecl
predicateDecl = 
  parens $ do 
    symbol "declare-fun"
    name <- identifierBracketed
    arg_types <- parens (many valType)
    symbol "Bool"
    return (PredicateDecl name arg_types)

----------------------------------------------------

instance Show AritExpr where
  show = \case 
    Div ex1 ex2  -> "(div " ++ show ex1 ++ " " ++ show ex2 ++ ")"
    Mod ex1 ex2  -> "(mod " ++ show ex1 ++ " " ++ show ex2 ++ ")"
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

instance Show Predicate where
  show (Predicate name []) = "|" ++ name ++ "|"
  show (Predicate name args) =
    "(" ++ unwords (("|" ++ name ++ "|"):args) ++ ")"

instance Show CHC where
  show (CHC vars lhs_preds constr rhs) = unlines
    [ "(assert"
    , "  (forall (" ++ var_def_list ++ ")"
    , "    (=>"
    , "      (and"
    , "        " ++ unwords (map show $ Set.toList lhs_preds)
    , "        " ++ show_constr constr
    , "      )"
    , "      " ++ maybe "false" show rhs
    , "    )"
    , "  )"
    , ")"
    ]
    where
      show_var_def :: (String, ValType) -> String
      show_var_def (vname, vtype) = 
        unwords [ "(", vname, show vtype, ")" ]

      -- LoAT expects at least one "and" around the constraint part
      show_constr (And exs) = show (And exs)
      show_constr ex        = show (And [ex])

      var_def_list :: String
      var_def_list = 
        case Map.toList vars of
          -- empty forall-lists are not allowed
          [] -> show_var_def ("DUMMY", ValTypeInt)
          vs -> unwords $ map show_var_def vs

instance Show PredicateDecl where
  show (PredicateDecl name arg_types) =
    "(declare-fun |" ++ name ++ "| ( " ++ unwords (map show arg_types) ++ " ) Bool)"

instance Show ValType where
  show = \case
    ValTypeBool -> "Bool"
    ValTypeInt  -> "Int"

instance Show SMT2 where
  show (SMT2 pred_decls clauses) =
    let (rules, queries) = partition (isJust . getRHS) clauses 
     in unlines
       $ [ "(set-logic HORN)" ]
      ++ map show pred_decls
      -- render rules first and queries last because LoAT expects this structure:
      ++ map show rules
      ++ map show queries
      ++ [ "(check-sat)", "(exit)" ]
