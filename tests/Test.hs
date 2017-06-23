{-# LANGUAGE FlexibleContexts #-}

module Main where

import Test.Tasty
import Test.Tasty.HUnit

import GHC

import G2.Internals.Core as G2
import G2.Internals.Translation
import G2.Internals.Preprocessing
import G2.Internals.Symbolic
import G2.Internals.SMT
--import G2.Internals.SMT
-- import G2.Internals.SMT.Old.Z3
-- import G2.Internals.SMT.Old.Z3Types


import Data.List
import qualified Data.Map  as M
import Data.Maybe
import qualified Data.Monoid as Mon

-- import Z3.Monad

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
                  -- checkExprReach  "tests/samples/IfTest.hs" "f" 2 [RForAll (\[Const (CInt x), Const (CInt y), (Const (CInt r))] -> if x == y then r == x + y else r == y), AtLeast 2]

                  checkExprOutput "tests/samples/Peano.hs" "equalsFour" "add" 2 [RExists peano_0_4, RExists peano_1_3, RExists peano_2_2, RExists peano_3_1, RExists peano_4_0, Exactly 5]
                -- , checkExprOutput "tests/samples/Peano.hs" "eqEachOtherAndAddTo4" "add" 2 [RForAll peano_2_2, Exactly 1]
                -- , checkExprOutput "tests/samples/Peano.hs" "equalsFour" "multiply" 2 [RExists peano_1_4, RExists peano_2_2, RExists peano_4_1, Exactly 3]

                -- , checkExprOutput  "tests/samples/HigherOrderMath.hs" "isTrue0" "notNegativeAt0NegativeAt1" 1 [RExists negativeSquareRes, AtLeast 1]
                -- , checkExprOutput "tests/samples/HigherOrderMath.hs" "isTrue1" "fixed" 2 [RExists abs2NonNeg, RExists abs2Neg, RExists squareRes, RExists fourthPowerRes, AtLeast 4]
                --, checkExprOutput "tests/samples/HigherOrderMath.hs" "HigherOrderMath" "isTrue2" "sameDoubleArgLarger" 2 [RExists addRes, RExists subRes, RExists pythagoreanRes, AtLeast 2]
                                --------------------GET THE ABOVE REXISTS WORKING EVENTUALLY!!!!!!!!!
                -- , checkExprReach  "tests/samples/HigherOrderMath.hs" "functionSatisfies" 3 [RExists functionSatisfiesRes, AtLeast 1]

                -- , checkExprOutput "tests/samples/McCarthy91.hs" "lessThan91" "mccarthy" 1 [RForAll (\[Const (CInt x)] -> x <= 100), AtLeast 1]
                , checkExprOutput "tests/samples/McCarthy91.hs" "greaterThan10Less" "mccarthy" 1 [RForAll (\[Const (CInt x)] -> x > 100), AtLeast 1]
                -- , checkExprOutput "tests/samples/McCarthy91.hs" "lessThanNot91" "mccarthy" 1 [Exactly 0]
                -- , checkExprOutput "tests/samples/McCarthy91.hs" "greaterThanNot10Less" "mccarthy" 1 [Exactly 0]
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
-- checkExprReach :: String -> String -> Int -> [Reqs] -> IO TestTree
-- checkExprReach filepath entry i reqList = do
--     exprs <- return . map (\(e, r) -> e ++ [r]) =<< testFile filepath entry

--     let ch = checkExpr exprs (i + 1) reqList

--     return . testCase filepath
--         $ assertBool ("Assertion for file " ++ filepath ++ " with function " ++ entry ++ " failed.\n" ++ show exprs) ch

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

-- testFile :: String -> String -> IO [([Expr], Expr)]
-- testFile filepath entry = do
--     raw_core <- mkGHCCore filepath
--     let (rt_env, re_env) = mkG2Core raw_core
--     let t_env' = M.union rt_env (M.fromList prelude_t_decls)
--     let e_env' = re_env
--     let init_state = initState t_env' e_env' "blank" entry


--     let defun_init_state = defunctionalize init_state

--     let (states, n) = runN [defun_init_state] 200

--     let states' = filter (\s -> not . containsNonConsFunctions (type_env s) . curr_expr $ s) states

--     -- return . catMaybes =<< mapM (\s@State {curr_expr = expr, path_cons = path_cons', sym_links = sym_links'} -> do
--     --     (r, m, out) <- evalZ3 . reachabilityAndOutputSolverZ3 $ s
--     --     if r == Sat then do
--     --         if Nothing `notElem` m then do
--     --             return $ Just (replaceFuncSLT s . map (fromJust) $ m, fromJust out)
--     --         else
--     --             return Nothing
--     --     else
--     --         return Nothing) states'
--     hhp <- getZ3ProcessHandles

--     return . catMaybes =<<  mapM (\s -> do
--         -- putStrLn $ mkStateStr s
--         let headers = toSMTHeaders s
--         let formula = toSolver smt2 headers
--         -- putStrLn solver
--         let vars = sltToSMTNameSorts $ sym_links s-- varNamesSorts headers

--         (res, m) <- checkSatAndGetModel smt2 hhp formula headers vars
--         if res == SAT then do
--             -- putStrLn "----\nPathCons:"
--             -- putStrLn . mkPCStr $ path_cons s
--             -- putStrLn "formula:"
--             -- print formula
--             -- putStrLn "model:"
--             -- putStrLn $ show (sym_links s)
--             case m of
--                 Just m' -> do
--                     let exprM = replaceFuncSLT s . modelAsExpr $ m'

--                     return (Just exprM)
--                 Nothing -> return Nothing
--         else return Nothing
--         ) states'


testFilePrePost :: String -> String -> String -> IO [[Expr]]
testFilePrePost filepath prepost entry = do
    raw_core <- mkGHCCore filepath
    let (rt_env, re_env) = mkG2Core raw_core
    let t_env' = M.union rt_env (M.fromList prelude_t_decls)
    let e_env' = re_env
    let init_state = initStateCond t_env' e_env' "blank" prepost entry


    let defun_init_state = defunctionalize init_state

    let (states, n) = runN [defun_init_state] 200

    let states' = filter (\s -> not . containsNonConsFunctions (type_env s) . curr_expr $ s) states

    -- return . catMaybes =<< mapM (\s@State {curr_expr = expr, path_cons = path_cons', sym_links = sym_links'} -> do
    --     (r, m) <- evalZ3 . outputSolverZ3 $ s
    --     if r == Sat then do
    --         if Nothing `notElem` m then
    --             return . Just . replaceFuncSLT s . map (fromJust) $ m
    --         else
    --             return Nothing
    --     else
    --         return Nothing) states'

    hhp <- getZ3ProcessHandles

    return . catMaybes =<< mapM (\s -> do
        -- putStrLn $ mkStateStr s
        let headers = toSMTHeaders s
        let formula = toSolver smt2 headers
        -- putStrLn solver
        let vars = sltToSMTNameSorts $ sym_links s-- varNamesSorts headers

        (res, m) <- checkSatAndGetModel smt2 hhp formula headers vars
        if res == SAT then do
            -- putStrLn "----\nPathCons:"
            -- putStrLn . mkPCStr $ path_cons s
            -- putStrLn "formula:"
            -- print formula
            -- putStrLn "model:"
            -- putStrLn $ show (sym_links s)
            case m of
                Just m' -> do
                    let exprM = replaceFuncSLT s . modelAsExpr $ m'

                    let inArgN = map (\(n, _, _) -> n)
                               . sortOn (\(_, _, x) -> fromJust x)
                               . filter (\(_, _, x) -> isJust x) 
                               . M.elems $ sym_links s

                    let inArg = map (\n -> fromJust $ M.lookup n exprM) inArgN

                    return (Just inArg)
                Nothing -> return Nothing
        else return Nothing
        ) states'

givenLengthCheck :: Int -> ([Expr] -> Bool) -> [Expr] -> Bool
givenLengthCheck i f e = if length e == i then f e else False


-- Dump from DeprensFunctions :: (Manipulatable Type m) => m -> Bool
-- containsFunctions :: (Manipulatable G2.Type m) => m -> Bool
-- containsFunctions = Mon.getAny . CM.eval (Mon.Any .  containsFunctions')
--     where
--         containsFunctions' :: G2.Type -> Bool
--         containsFunctions' (G2.TyFun _ _) = True
--         containsFunctions' _ = False

--Contains functions that are not just type constructors
containsNonConsFunctions :: (ASTContainer m Expr) => TEnv -> m -> Bool
containsNonConsFunctions tenv = Mon.getAny . evalASTs (Mon.Any . containsFunctions' tenv)
    where
        containsFunctions' :: TEnv -> Expr -> Bool
        containsFunctions' tenv (App (Var n _) _) = n `notElem` (constructors tenv) && n `notElem` handledFunctions
        containsFunctions' _ _ = False

        constructors :: TEnv -> [G2.Name]
        constructors = evalASTs constructors'
            where
                constructors' :: G2.Type -> [G2.Name]
                constructors' (TyAlg _ dc) = [n | (DataCon n _ _ _) <- dc]
                constructors' _ = []

        handledFunctions = ["==", ">", "<", ">=", "<=", "+", "-", "*", "/", "&&", "||"]

--Switches every occurence of a Var in the Func SLT from datatype to function
replaceFuncSLT :: ASTContainer m Expr => State -> m -> m
replaceFuncSLT s e = modifyASTs replaceFuncSLT' e
    where
        replaceFuncSLT' :: Expr -> Expr
        replaceFuncSLT' v@(Var n t) =
            let
                n' = M.lookup n (func_interps s)
            in
            case n' of
                    Just (n'', _) -> Var n'' (case functionType s n'' of
                                                Just t -> t
                                                Nothing -> TyBottom)
                    Nothing -> v
        replaceFuncSLT' e = e

        functionType :: State -> G2.Name -> Maybe G2.Type
        functionType s n = G2.exprType <$> M.lookup n (expr_env s)

-- constructors :: TEnv -> [G2.Name]
-- constructors = evalDataConType (\(DataCon n _ _ _) -> [n])

functionType :: State -> G2.Name -> Maybe G2.Type
functionType s n = G2.exprType <$> M.lookup n (expr_env s)

