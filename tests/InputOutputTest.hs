{-# LANGUAGE OverloadedStrings #-}
module InputOutputTest where

import Test.Tasty
import Test.Tasty.HUnit

import Control.Exception
import qualified Data.Text as T

import G2.Internals.Config
import G2.Internals.Execution
import G2.Internals.Interface
import G2.Internals.Language
import G2.Internals.Liquid.Interface
import G2.Internals.Translation
import G2.Internals.Solver

import G2.Lib.Printers

import Reqs

checkInputOutput :: FilePath -> FilePath -> String -> String -> Int -> Int -> [Reqs String String] ->  IO TestTree
checkInputOutput proj src md entry stps i req = checkInputOutputWithConfig proj src md entry i req (mkConfigDef {steps = stps})

checkInputOutputWithConfig :: FilePath -> FilePath -> String -> String -> Int -> [Reqs String String] -> Config -> IO TestTree
checkInputOutputWithConfig proj src md entry i req config = do
    r <- checkInputOutput' proj src md entry i req config

    let b = case r of
            Left _ -> False
            Right b' -> b'

    return . testCase src $ assertBool ("Input/Output for file " ++ show src ++ " failed on function " ++ entry ++ ".") b 

checkInputOutput' :: FilePath -> FilePath -> String -> String -> Int -> [Reqs String String] -> Config -> IO (Either SomeException Bool)
checkInputOutput' proj src md entry i req config = try (checkInputOutput'' proj src md entry i req config)

checkInputOutput'' :: FilePath -> FilePath -> String -> String -> Int -> [Reqs String String] -> Config -> IO Bool
checkInputOutput'' proj src md entry i req config = do
    (mb_modname, binds, tycons, cls, tgtNames, exp) <- translateLoaded proj src [] False config

    let init_state = initState binds tycons cls Nothing Nothing Nothing False False (T.pack entry) mb_modname exp
    let halter_set_state = init_state {halter = steps config}
    
    (con, hhp) <- getSMT config

    let chAll = checkExprAll req

    r <- run StdRed con hhp config () halter_set_state
    mr <- validateStates proj src md entry chAll [] r
    let io = map (\(_, i, o, _) -> i ++ [o]) r

    let chEx = checkExprInOutCount io i req
    return $ mr && chEx

------------

checkInputOutputLH :: FilePath -> FilePath -> String -> String -> Int -> Int -> [Reqs String String] ->  IO TestTree
checkInputOutputLH proj src md entry stps i req = checkInputOutputLHWithConfig proj src md entry i req (mkConfigDef {steps = stps})

checkInputOutputLHWithConfig :: FilePath -> FilePath -> String -> String -> Int -> [Reqs String String] -> Config -> IO TestTree
checkInputOutputLHWithConfig proj src md entry i req config = do
    r <- checkInputOutputLH' proj src md entry i req config

    let b = case r of
            Left _ -> False
            Right b' -> b'

    return . testCase src $ assertBool ("Input/Output for file " ++ show src ++ " failed on function " ++ entry ++ ".") b 

checkInputOutputLH' :: FilePath -> FilePath -> String -> String -> Int -> [Reqs String String] -> Config -> IO (Either SomeException Bool)
checkInputOutputLH' proj src md entry i req config = try (checkInputOutputLH'' proj src md entry i req config)

checkInputOutputLH'' :: FilePath -> FilePath -> String -> String -> Int -> [Reqs String String] -> Config -> IO Bool
checkInputOutputLH'' proj src md entry i req config = do
    r <- findCounterExamples proj src (T.pack entry) [] [] config

    let chAll = checkExprAll req

    mr <- validateStates proj src md entry chAll [] r
    let io = map (\(_, i, o, _) -> i ++ [o]) r

    let chEx = checkExprInOutCount io i req
    return $ mr && chEx

------------

-- | Checks conditions on given expressions
checkExprAll :: [Reqs String String] -> [String]
checkExprAll reqList = [f | RForAll f <- reqList]

checkExprExists :: [Reqs String String] -> [String]
checkExprExists reqList = [f | RExists f <- reqList]

checkExprInOutCount :: [[Expr]] -> Int -> [Reqs c t] -> Bool
checkExprInOutCount exprs i reqList =
    let
        checkAtLeast = and . map ((>=) (length exprs)) $ [x | AtLeast x <- reqList]
        checkAtMost = and . map ((<=) (length exprs)) $ [x | AtMost x <- reqList]
        checkExactly = and . map ((==) (length exprs)) $ [x | Exactly x <- reqList]

        checkArgCount = and . map ((==) i . length) $ exprs
    in
    checkAtLeast && checkAtMost && checkExactly && checkArgCount
