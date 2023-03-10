module TestPropositions (tests) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Data.String (fromString)

import Expression
import CNF 
import qualified Algorithm.LinearResolution as LR
import qualified Algorithm.DPLL as DPLL
import qualified Algorithm.CDCL2 as CDCL
import qualified Data.Set as S
import Data.Maybe (fromMaybe, isJust)
import Assignment ((|=), Assignment)
import Control.Applicative ((<|>))
import Control.Monad (guard)
import qualified GameUnequal
import qualified Data.Map as M
import Assignment (ignoreAuxVars)

tests :: TestTree
tests = testGroup "Propositions" 
  [ unitTests, propertyBasedTests ]


-- Unit Tests

expr1 :: Expr String
expr1 = "((-(-a)) & a)"

expr2 :: Expr String
expr2 = "(((-a)->(b->a)) & ((-a) & (b & b)))"

expr3 :: Expr String
expr3 = "(((a & b) | (a -> a)) | ((-a) & (b -> b)))"

expr4 :: Expr String
expr4 = "(((b <-> b) & (a & a)) & (-(a | b)))"

expr5 :: Expr String
expr5 = "(-((a -> a) | (a | b)))"

expr6 :: Expr String
expr6 = "(-((b -> b) | (-a)))"

-- Expression describing the (unsatisfiable) pigeon hole principle for n holes and n+1 pigeons.
-- This expression is considered performance "worst case" for SAT solvers.
pigeonHolePrinciple :: Int -> Expr String
pigeonHolePrinciple n = at_most_one_pigeon_per_hole `And` at_least_one_hole_per_pigeon
  where
    var p h = Atom $ "x" <> show p <> "x" <> show h

    at_most_one_pigeon_per_hole = foldr1 And $ do
      hole    <- [1 .. n]
      pigeon1 <- [1 .. n]
      pigeon2 <- [pigeon1+1 .. n+1]
      return $ Not (var pigeon1 hole)
          `Or` Not (var pigeon2 hole)

    pigeon_in_one_of pigeon = foldr1 Or $
      var pigeon <$> [1 .. n]

    at_least_one_hole_per_pigeon = foldr1 And $
      pigeon_in_one_of <$> [1 .. n+1]

satWith :: (CNF (WithAux String) -> Maybe (Assignment (WithAux String)))
        -> Expr String
        -> Maybe (Assignment String)
satWith sat = 
    fmap ignoreAuxVars
  . sat 
  . conjunctiveNormalForm 
  . tseytin 

unitTests :: TestTree
unitTests = testGroup "Unit Tests"
  [ testGroup "Linear Resolution"
    [ testCase "expr1 is satisfiable"   $ LR.sat (conjunctiveNormalForm expr1) @?= True
    , testCase "expr2 is unsatisfiable" $ LR.sat (conjunctiveNormalForm expr2) @?= False
    , testCase "expr3 is satisfiable"   $ LR.sat (conjunctiveNormalForm expr3) @?= True
    , testCase "expr4 is unsatisfiable" $ LR.sat (conjunctiveNormalForm expr4) @?= False
    , testCase "expr5 is unsatisfiable" $ LR.sat (conjunctiveNormalForm expr5) @?= False
    , testCase "expr6 is unsatisfiable" $ LR.sat (conjunctiveNormalForm expr6) @?= False
    ]
  , testGroup "DPLL"
    [ testCase "expr1 is satisfiable"   $ isJust (satWith DPLL.sat expr1) @?= True
    , testCase "expr2 is unsatisfiable" $ isJust (satWith DPLL.sat expr2) @?= False
    , testCase "expr3 is satisfiable"   $ isJust (satWith DPLL.sat expr3) @?= True
    , testCase "expr4 is unsatisfiable" $ isJust (satWith DPLL.sat expr4) @?= False
    , testCase "expr5 is unsatisfiable" $ isJust (satWith DPLL.sat expr5) @?= False
    , testCase "expr6 is unsatisfiable" $ isJust (satWith DPLL.sat expr6) @?= False
    , testCase "GameUnequal is satisfiable" $ isJust (DPLL.sat $ conjunctiveNormalForm GameUnequal.example) @?= True
    ]
  , testGroup "Conflict Driven Clause Learning"
    [ testCase "expr1 is satisfiable"   $ isJust (satWith CDCL.sat expr1) @?= True
    , testCase "expr2 is unsatisfiable" $ isJust (satWith CDCL.sat expr2) @?= False
    , testCase "expr3 is satisfiable"   $ isJust (satWith CDCL.sat expr3) @?= True
    , testCase "expr4 is unsatisfiable" $ isJust (satWith CDCL.sat expr4) @?= False
    , testCase "expr5 is unsatisfiable" $ isJust (satWith CDCL.sat expr5) @?= False
    , testCase "expr6 is unsatisfiable" $ isJust (satWith CDCL.sat expr6) @?= False
    , testCase "GameUnequal is satisfiable" $ isJust (CDCL.sat $ conjunctiveNormalForm GameUnequal.example) @?= True
    ]
  ]

-- Property Based Tests

propertyBasedTests :: TestTree
propertyBasedTests =
  testGroup "Property tests"
    [ testProperty "Expression parsing is inverse of showing" prop_expr_parse_is_inverse_of_show
    , testProperty "`removeConstants` drops all boolean constants from an expression" prop_removes_all_boolean_constants
    , testProperty "A formula or its negation is always satisfiable" prop_identity_or_negation_satisfiable
    , testProperty "Found assignment satisfies formula" prop_found_assigment_satisfies_formula
    , testProperty "DPLL and CDCL algorithm are equivalent" prop_dpll_cdcl_equivalent
    -- TODO
    -- negation of unsatifiable formula is tautology
    ]

instance Arbitrary (Expr String) where
  arbitrary = sized arbitrary_sized_expr
    where
      var :: Gen String
      var = do
        -- FIXME: magic number
        i <- chooseInt (0, 10)
        return $ 'x' : show i

      arbitrary_sized_expr :: Int -> Gen (Expr String)
      arbitrary_sized_expr 0 = Atom <$> var
      arbitrary_sized_expr n = do
        op <- elements [And, Or, Impl, Equiv]
        op <$> arbitrary_sized_expr (n `div` 2) <*> arbitrary_sized_expr (n `div` 2)

  shrink expr =
    case expr of
      T             -> []
      F             -> []
      Atom atom     -> []
      Not e         -> e : shrink e
      e1 `And` e2   -> [e1, e2] ++ [ e1' `And`   e2' | (e1', e2') <- shrink (e1, e2) ]
      e1 `Or` e2    -> [e1, e2] ++ [ e1' `Or`    e2' | (e1', e2') <- shrink (e1, e2) ]
      e1 `Impl` e2  -> [e1, e2] ++ [ e1' `Impl`  e2' | (e1', e2') <- shrink (e1, e2) ]
      e1 `Equiv` e2 -> [e1, e2] ++ [ e1' `Equiv` e2' | (e1', e2') <- shrink (e1, e2) ]

prop_expr_parse_is_inverse_of_show :: Expr String -> Bool
prop_expr_parse_is_inverse_of_show expr =
  (fromString . show $ expr) == expr

prop_removes_all_boolean_constants :: Expr String -> Bool
prop_removes_all_boolean_constants expr = is_constant expr' || not (contains_constant expr')
  where
    expr' = eliminateConstants expr

    is_constant :: Expr a -> Bool
    is_constant T = True
    is_constant F = True
    is_constant _ = False

    contains_constant :: Expr String -> Bool
    contains_constant = any is_constant . subExpressions

prop_found_assigment_satisfies_formula :: Expr String -> Bool
prop_found_assigment_satisfies_formula expr = fromMaybe True $ do
  model <- satWith CDCL.sat expr
  return $ model |= expr

prop_identity_or_negation_satisfiable :: Expr String -> Bool
prop_identity_or_negation_satisfiable expr = isJust $
  satWith CDCL.sat expr <|> satWith CDCL.sat (Not expr)

prop_dpll_cdcl_equivalent :: Expr String -> Bool
prop_dpll_cdcl_equivalent expr =
  isJust (satWith DPLL.sat expr) == isJust (satWith CDCL.sat expr)