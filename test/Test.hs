{-# LANGUAGE OverloadedStrings #-}

module Main where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Data.String (fromString)

import Expr 
import CNF
import qualified LinearResolution as LR
import Debug.Trace (trace)
import qualified DPLL

main = defaultMain tests

tests :: TestTree
tests = testGroup "All tests"
  [ propertyBasedTests, unitTests ]

-- Property Based Tests

propertyBasedTests :: TestTree
propertyBasedTests =
  testGroup "Property tests"
    [ testProperty "Expression parsing is inverse of showing" prop_expr_parse_is_inverse_of_show 
    , testProperty "`removeConstants` drops all boolean constants from an expression" prop_removes_all_boolean_constants
    , testProperty "A formula itself or its negation is satisfiable" prop_itself_or_negation_is_satisfiable

    -- TODO: tests too slow:
    -- , testProperty "Tseytin transformation preserves satisfiability" prop_tseytin_preserves_satisfiability
    -- , testProperty "Linear resolution and DPLL are equivalent" prop_linear_resolution_and_dpll_are_equivalent

    -- , testProperty "Found assignment satisfies formula" prop_found_assigment_satisfies_formula 
    ]

instance Arbitrary Atom where
  arbitrary = frequency [ (4, var), (1, pure T), (1, pure F) ]
    where
      var :: Gen Atom
      var = do 
        -- FIXME: magic number
        i <- chooseInt (0, 10)
        return $ V ('x' : show i)

instance Arbitrary Expr where
  arbitrary = sized arbitrary_sized_expr
    where
      arbitrary_sized_expr :: Int -> Gen Expr
      arbitrary_sized_expr 0 = Atom <$> arbitrary 
      arbitrary_sized_expr n = do
        op <- elements [And, Or, Impl, Equiv]
        op <$> arbitrary_sized_expr (n `div` 2) <*> arbitrary_sized_expr (n `div` 2)

  shrink expr = 
    case expr of
      Atom atom     -> []
      Not e         -> e : shrink e
      e1 `And` e2   -> [e1, e2] ++ [ e1' `And`   e2' | (e1', e2') <- shrink (e1, e2) ]
      e1 `Or` e2    -> [e1, e2] ++ [ e1' `Or`    e2' | (e1', e2') <- shrink (e1, e2) ]
      e1 `Impl` e2  -> [e1, e2] ++ [ e1' `Impl`  e2' | (e1', e2') <- shrink (e1, e2) ]
      e1 `Equiv` e2 -> [e1, e2] ++ [ e1' `Equiv` e2' | (e1', e2') <- shrink (e1, e2) ]

-- prop_found_assigment_satisfies_formula :: Expr -> Bool
-- prop_found_assigment_satisfies_formula expr = 
--   case sat expr of 
--     Just assignment -> assignment |= expr
--     Nothing         -> True

prop_expr_parse_is_inverse_of_show :: Expr -> Bool
prop_expr_parse_is_inverse_of_show expr = 
  (fromString . show $ expr) == expr

prop_removes_all_boolean_constants :: Expr -> Bool
prop_removes_all_boolean_constants expr = is_trivial expr' || not (contains_constant expr')
  where
    expr' = removeConstants expr

    is_constant :: Atom -> Bool
    is_constant (V _) = False
    is_constant _ = True

    is_trivial :: Expr -> Bool
    is_trivial  (Atom at) = is_constant at
    is_trivial _ = False

    contains_constant :: Expr -> Bool
    contains_constant = any is_constant . atoms

prop_tseytin_preserves_satisfiability :: Expr -> Bool
prop_tseytin_preserves_satisfiability expr =
  DPLL.sat expr == DPLL.sat (tseytin expr) 

prop_linear_resolution_and_dpll_are_equivalent :: Expr -> Bool
prop_linear_resolution_and_dpll_are_equivalent expr =
  DPLL.sat (tseytin expr) == LR.sat (tseytin expr)

prop_itself_or_negation_is_satisfiable :: Expr -> Bool
prop_itself_or_negation_is_satisfiable expr =
  DPLL.sat (tseytin expr) || DPLL.sat (tseytin $ Not expr)

-- Unit Tests

expr1 :: Expr
expr1 = "((-(-a)) & a)"

expr2 :: Expr
expr2 = "(((-a)->(b->a)) & ((-a) & (b & b)))"

expr3 :: Expr
expr3 = "(((a & b) | (a -> a)) | ((-a) & (b -> b)))"

expr4 :: Expr
expr4 = "(((b <-> b) & (a & a)) & (-(a | b)))"

expr5 :: Expr
expr5 = "(-((a -> a) | (a | b)))"

expr6 :: Expr
expr6 = "(-((b -> b) | (-a)))"

unitTests :: TestTree
unitTests = testGroup "Unit Tests"
  [ testGroup "Linear Resolution" 
    [ testCase "expr1 is satisfiable"   $ LR.sat expr1 @?= True
    , testCase "expr2 is unsatisfiable" $ LR.sat expr2 @?= False 
    , testCase "expr3 is satisfiable"   $ LR.sat expr3 @?= True
    , testCase "expr4 is unsatisfiable" $ LR.sat expr4 @?= False 
    , testCase "expr5 is unsatisfiable" $ LR.sat expr5 @?= False 
    , testCase "expr6 is unsatisfiable" $ LR.sat expr6 @?= False 
    ]
  , testGroup "DPLL"
    [ testCase "expr1 is satisfiable"   $ DPLL.sat expr1 @?= True
    , testCase "expr2 is unsatisfiable" $ DPLL.sat expr2 @?= False 
    , testCase "expr3 is satisfiable"   $ DPLL.sat expr3 @?= True
    , testCase "expr4 is unsatisfiable" $ DPLL.sat expr4 @?= False 
    , testCase "expr5 is unsatisfiable" $ DPLL.sat expr5 @?= False 
    , testCase "expr6 is unsatisfiable" $ DPLL.sat expr6 @?= False 
    ]
  ]
