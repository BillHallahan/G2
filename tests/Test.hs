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
                              checkExprReachability   "tests/samples/IfTest.hs" "f" (\[x, y] r -> if x == y then True else True)

                            , checkExprOutput "tests/samples/Peano.hs" "equalsFour" "add" 2 [RExists peano_0_4, RExists peano_1_3, RExists peano_2_2, RExists peano_3_1, RExists peano_4_0, Exactly 5]
                            , checkExprOutput "tests/samples/Peano.hs" "eqEachOtherAndAddTo4" "add" 2 [RForAll peano_2_2, Exactly 1]
                            , checkExprOutput "tests/samples/Peano.hs" "equalsFour" "multiply" 2 [RExists peano_1_4, RExists peano_2_2, RExists peano_4_1, Exactly 3]

                            , checkExprOutput "tests/samples/HigherOrderMath.hs" "isTrue" "fixed" 2 [RExists abs2NonNeg, RExists abs2Neg, RExists squareRes, RExists fourthPowerRes, AtLeast 4]

                            , checkExprOutput "tests/samples/McCarthy91.hs" "lessThan91" "mccarthy" 1 [RForAll (\[Const (CInt x)] -> x <= 100), AtLeast 1]
                            , checkExprOutput "tests/samples/McCarthy91.hs" "greaterThan10Less" "mccarthy" 1 [RForAll (\[Const (CInt x)] -> x > 100), AtLeast 1]
                            , checkExprOutput "tests/samples/McCarthy91.hs" "lessThanNot91" "mccarthy" 1 [Exactly 0]
                            , checkExprOutput "tests/samples/McCarthy91.hs" "greaterThanNot10Less" "mccarthy" 1 [Exactly 0]
                    ]

-- | Checks conditions on functions, with pre/post conditions
checkExprOutput :: String -> String -> String -> Int -> [Reqs] -> IO TestTree
checkExprOutput filepath prepost entry i reqList = do
    exprs <- testFilePrePost filepath prepost entry

    let argChecksAll = and . map (\f -> all (givenLengthCheck i f) exprs) $ [f | RForAll f <- reqList]
    let argChecksEx = and . map (\f -> any (givenLengthCheck i f) exprs) $ [f | RExists f <- reqList]
    let checkAtLeast = and . map ((>=) (length exprs)) $ [x | AtLeast x <- reqList]
    let checkAtMost = and . map ((<=) (length exprs)) $ [x | AtMost x <- reqList]
    let checkExactly = and . map ((==) (length exprs)) $ [x | Exactly x <- reqList]

    return . testCase filepath
            $ assertBool ("Assertion for file " ++ filepath ++ " with functions " ++ prepost ++ " " ++ entry ++ " failed.")
            (argChecksAll && argChecksEx && checkAtLeast && checkAtMost && checkExactly)

-- | Checks conditions on functions
checkExprReachability :: String -> String -> ([Expr] -> Expr -> Bool) -> IO TestTree
checkExprReachability filepath entry f = do
    exprs <- testFile filepath entry

    let res = and . map (\(e, r) ->  f e r) $ exprs

    return . testCase filepath $ assertBool ("Assertion for file " ++ filepath ++ " with function " ++ entry ++ " failed." ++ show exprs) res


testFile :: String -> String -> IO [([Expr], Expr)]
testFile filepath entry = do
    raw_core <- mkRawCore filepath
    let (rt_env, re_env) = mkG2Core raw_core
    let t_env' = M.union rt_env (M.fromList prelude_t_decls)
    let e_env' = re_env
    let init_state = initState t_env' e_env' entry


    let defun_init_state = defunctionalize init_state

    let (states, n) = runN [defun_init_state] 200

    let states' = filter (\s -> not . containsNonConsFunctions (tEnv s) . cExpr $ s) states

    return . catMaybes =<< mapM (\s@State {cExpr = expr, pc = pc', slt = slt'} -> do
        (r, m, out) <- evalZ3 . reachabilityAndOutputSolverZ3 $ s
        if r == Sat then do
            if Nothing `notElem` m then do
                return $ Just (replaceFuncSLT s . map (fromJust) $ m, fromJust out)
            else
                return Nothing
        else
            return Nothing) states'


testFilePrePost :: String -> String -> String -> IO [[Expr]]
testFilePrePost filepath prepost entry = do
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