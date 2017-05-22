module Main where

import Test.Tasty
import Test.Tasty.HUnit

import GHC

import G2.Core.Defunctionalizor
import G2.Core.Language
import G2.Core.Evaluator
import G2.Core.Utils

import G2.Haskell.Prelude
import G2.Haskell.Translator

import G2.SMT.Z3

import Data.List
import qualified Data.Map  as M
import Data.Maybe

import Z3.Monad

import PeanoTest
import HigherOrderMathTest

main :: IO ()
main = do
    defaultMain =<< tests

tests = return . testGroup "Tests"
                    =<< sequence [
                              checkExprOutput "tests/samples/Peano.hs" "equalsFour" "add" 2 (\_ -> True) [peano_0_4, peano_1_3, peano_2_2, peano_3_1, peano_4_0]
                            , checkExprOutput "tests/samples/Peano.hs" "eqEachOtherAndAddTo4" "add" 2 (peano_2_2) []
                            , checkExprOutput "tests/samples/Peano.hs" "equalsFour" "multiply" 2 (\_ -> True) [peano_1_4, peano_2_2, peano_4_1]

                            , checkExprOutput "tests/samples/HigherOrderMath.hs" "isTrue" "fixed" 2 (\_ -> True) [abs2NonNeg, abs2Neg, squareRes, fourthPowerRes]
                    ]

-- Given a filename, pre/post condition function and function to evaluate in that file,
-- uses the provided function to check
checkExprOutput :: String -> String -> String -> Int -> ([Expr] -> Bool) -> [[Expr] -> Bool] -> IO TestTree
checkExprOutput filepath prepost entry i f fList = do
    exprs <- testFile filepath prepost entry

    let argChecksAll = and . map (givenLengthCheck i f) $ exprs
    let argChecksOne = and . map (\f' -> any (givenLengthCheck i f') exprs) $ fList

    return . testCase filepath $ assertBool ("Assertion for file " ++ filepath ++ " with functions " ++ prepost ++ " " ++ entry ++ " failed.") (argChecksAll && argChecksOne)

testFile :: String -> String -> String -> IO [[Expr]]
testFile filepath prepost entry = do
    raw_core <- mkRawCore filepath
    let (rt_env, re_env) = mkG2Core raw_core
    let t_env' = M.union rt_env (M.fromList prelude_t_decls)
    let e_env' = re_env
    let init_state = initStateWithPost t_env' e_env' prepost entry


    let defun_init_state = defunctionalize init_state

    let (states, n) = runN [defun_init_state] 200

    let states' = filter (\s -> not . containsNonConsFunctions (tEnv s) . cExpr $ s) states

    return . catMaybes =<< mapM (\s@State {cExpr = expr, pc = pc', slt = slt'} -> do
        (r, m) <- evalZ3 . outputSolverZ3 $ s
        if r == Sat then do
            if Nothing `notElem` m then
                return . Just . replaceFuncSLT s . map (fromJust) $ m
            else
                return Nothing
        else
            return Nothing) states'

givenLengthCheck :: Int -> ([Expr] -> Bool) -> [Expr] -> Bool
givenLengthCheck i f e = if length e == i then f e else False