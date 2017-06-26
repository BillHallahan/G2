{-# LANGUAGE FlexibleContexts #-}

module Main where

import Test.Tasty
import Test.Tasty.HUnit

import GHC

import G2.Internals.Interface
import G2.Internals.Core as G2
import G2.Internals.Translation
import G2.Internals.Preprocessing
import G2.Internals.Symbolic
import G2.Internals.SMT


import Data.List
import qualified Data.Map  as M
import Data.Maybe
import qualified Data.Monoid as Mon

import UnitTests

import PeanoTest
import HigherOrderMathTest


-- | Requirements
-- We use these to define checks on tests returning function inputs
--     RForall f -- All the returned inputs satisfy the function f
--     RExists f -- At least one of the returned inputs satisfies the function f
--     AtLeast x -- At least x inputs are returned
--     AtMost  x -- At most x inputs are returned
--     Exactly x -- Exactly x inputs are returned
data Reqs = RForAll ([Expr] -> Bool) 
          | RExists ([Expr] -> Bool)
          | AtLeast Int
          | AtMost Int
          | Exactly Int

main :: IO ()
main = do
    defaultMain =<< tests

tests = return . testGroup "Tests"
    =<< sequence [
          sampleTests
        , unitTests
        ]

sampleTests =
    return . testGroup "Samples"
        =<< sequence [
                  checkExprReach  "tests/samples/IfTest.hs" "f" 2 [RForAll (\[Const (CInt x), Const (CInt y), (Const (CInt r))] -> if x == y then r == x + y else r == y), AtLeast 2]

                , checkExprOutput "tests/samples/Peano.hs" "equalsFour" "add" 2 [RExists peano_0_4, RExists peano_1_3, RExists peano_2_2, RExists peano_3_1, RExists peano_4_0, Exactly 5]
                , checkExprOutput "tests/samples/Peano.hs" "eqEachOtherAndAddTo4" "add" 2 [RForAll peano_2_2, Exactly 1]
                , checkExprOutput "tests/samples/Peano.hs" "equalsFour" "multiply" 2 [RExists peano_1_4, RExists peano_2_2, RExists peano_4_1, Exactly 3]

                , checkExprOutput  "tests/samples/HigherOrderMath.hs" "isTrue0" "notNegativeAt0NegativeAt1" 1 [RExists negativeSquareRes, AtLeast 1]
                , checkExprOutput "tests/samples/HigherOrderMath.hs" "isTrue1" "fixed" 2 [RExists abs2NonNeg, RExists abs2Neg, RExists squareRes, RExists fourthPowerRes, AtLeast 4]
                , checkExprOutput "tests/samples/HigherOrderMath.hs" "isTrue2" "sameDoubleArgLarger" 2 [RExists addRes, RExists subRes, RExists pythagoreanRes, AtLeast 2]
                , checkExprReach  "tests/samples/HigherOrderMath.hs" "functionSatisfies" 3 [RExists functionSatisfiesRes, AtLeast 1]

                , checkExprOutput "tests/samples/McCarthy91.hs" "lessThan91" "mccarthy" 1 [RForAll (\[Const (CInt x)] -> x <= 100), AtLeast 1]
                , checkExprOutput "tests/samples/McCarthy91.hs" "greaterThan10Less" "mccarthy" 1 [RForAll (\[Const (CInt x)] -> x > 100), AtLeast 1]
                , checkExprOutput "tests/samples/McCarthy91.hs" "lessThanNot91" "mccarthy" 1 [Exactly 0]
                , checkExprOutput "tests/samples/McCarthy91.hs" "greaterThanNot10Less" "mccarthy" 1 [Exactly 0]
        ]

-- | Checks conditions on functions, with pre/post conditions
--   Also checks that the right number of inputs is found for each function
checkExprOutput :: String -> String -> String -> Int -> [Reqs] -> IO TestTree
checkExprOutput filepath prepost entry i reqList = do
    exprs <- testFilePrePost filepath prepost entry

    let ch = checkExpr exprs i reqList

    return . testCase filepath
            $ assertBool ("Assertion for file " ++ filepath ++ " with functions " ++ prepost ++ " " ++ entry ++ " failed.\n" ++ show exprs) ch

-- | Checks conditions on functions
--   Also checks that the right number of inputs is found for each function
checkExprReach :: String -> String -> Int -> [Reqs] -> IO TestTree
checkExprReach filepath entry i reqList = do
    exprs <- return . map (\(e, r) -> e ++ [r]) =<< testFile filepath entry

    let ch = checkExpr exprs (i + 1) reqList

    return . testCase filepath
        $ assertBool ("Assertion for file " ++ filepath ++ " with function " ++ entry ++ " failed.\n" ++ show exprs) ch

-- | Checks conditions on given expressions
--   Helper for checkExprOutput checkExprReach
checkExpr :: [[Expr]] -> Int -> [Reqs] -> Bool
checkExpr exprs i reqList =
    let
        argChecksAll = and . map (\f -> all (givenLengthCheck i f) exprs) $ [f | RForAll f <- reqList]
        argChecksEx = and . map (\f -> any (givenLengthCheck i f) exprs) $ [f | RExists f <- reqList]
        checkAtLeast = and . map ((>=) (length exprs)) $ [x | AtLeast x <- reqList]
        checkAtMost = and . map ((<=) (length exprs)) $ [x | AtMost x <- reqList]
        checkExactly = and . map ((==) (length exprs)) $ [x | Exactly x <- reqList]

        checkArgCount = and . map ((==) i . length) $ exprs
    in
    argChecksAll && argChecksEx && checkAtLeast && checkAtMost && checkExactly && checkArgCount

testFile :: String -> String -> IO [([Expr], Expr)]
testFile filepath entry = do
    raw_core <- mkGHCCore filepath
    let (rt_env, re_env) = mkG2Core raw_core
    let t_env' = M.union rt_env (M.fromList prelude_t_decls)
    let e_env' = re_env
    let init_state = initState t_env' e_env' "blank" entry

    hhp <- getZ3ProcessHandles

    run smt2 hhp init_state


testFilePrePost :: String -> String -> String -> IO [[Expr]]
testFilePrePost filepath prepost entry = do
    raw_core <- mkGHCCore filepath
    let (rt_env, re_env) = mkG2Core raw_core
    let t_env' = M.union rt_env (M.fromList prelude_t_decls)
    let e_env' = re_env
    let init_state = initStateCond t_env' e_env' "blank" prepost entry

    hhp <- getZ3ProcessHandles

    mapM (return . fst) =<< run smt2 hhp init_state

givenLengthCheck :: Int -> ([Expr] -> Bool) -> [Expr] -> Bool
givenLengthCheck i f e = if length e == i then f e else False