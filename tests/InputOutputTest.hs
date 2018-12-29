{-# LANGUAGE OverloadedStrings #-}
module InputOutputTest ( checkInputOutput
                       , checkInputOutputLH ) where

import Test.Tasty
import Test.Tasty.HUnit

import Control.Exception
import qualified Data.Text as T

import G2.Config
import G2.Interface
import G2.Language
import G2.Liquid.Interface
import G2.Translation

import Reqs
import TestUtils

checkInputOutput :: FilePath -> FilePath -> String -> String -> Int -> Int -> [Reqs String] ->  IO TestTree
checkInputOutput proj src md entry stps i req = checkInputOutputWithConfig proj src md entry i req (mkConfigTest {steps = stps})

checkInputOutputWithConfig :: FilePath -> FilePath -> String -> String -> Int -> [Reqs String] -> Config -> IO TestTree
checkInputOutputWithConfig proj src md entry i req config = do
    r <- doTimeout (timeLimit config) $ checkInputOutput' proj src md entry i req config

    let (b, e) = case r of
            Nothing -> (False, "\nTimeout")
            Just (Left e') -> (False, "\n" ++ show e')
            Just (Right (b', _)) -> (b', "")

    return . testCase src $ assertBool ("Input/Output for file " ++ show src ++ " failed on function " ++ entry ++ "." ++ e) b 

checkInputOutput' :: FilePath 
                  -> FilePath 
                  -> String 
                  -> String 
                  -> Int 
                  -> [Reqs String] 
                  -> Config 
                  -> IO (Either SomeException (Bool, [ExecRes ()]))
checkInputOutput' proj src md entry i req config = try (checkInputOutput'' proj src md entry i req config)

checkInputOutput'' :: FilePath 
                   -> FilePath 
                   -> String 
                   -> String 
                   -> Int 
                   -> [Reqs String] 
                   -> Config 
                   -> IO (Bool, [ExecRes ()])
checkInputOutput'' proj src md entry i req config = do
    (mb_modname, binds, tycons, cls, ex) <- translateLoaded proj src [] False config

    let (init_state, _) = initState binds tycons cls Nothing Nothing Nothing False (T.pack entry) mb_modname ex config
    
    r <- runG2WithConfig init_state config

    let chAll = checkExprAll req
    mr <- validateStates proj src md entry chAll [] r
    let io = map (\(ExecRes { conc_args = i', conc_out = o}) -> i' ++ [o]) r

    let chEx = checkExprInOutCount io i req
    
    return $ (mr && chEx, r)

------------

checkInputOutputLH :: FilePath -> FilePath -> String -> String -> Int -> Int -> [Reqs String] ->  IO TestTree
checkInputOutputLH proj src md entry stps i req = checkInputOutputLHWithConfig proj src md entry i req (mkConfigTest {steps = stps})

checkInputOutputLHWithConfig :: FilePath -> FilePath -> String -> String -> Int -> [Reqs String] -> Config -> IO TestTree
checkInputOutputLHWithConfig proj src md entry i req config = do
    r <- doTimeout (timeLimit config) $ checkInputOutputLH' proj src md entry i req config

    let b = case r of
            Just (Right b') -> b'
            _ -> False

    return . testCase src $ assertBool ("Input/Output for file " ++ show src ++ " failed on function " ++ entry ++ ".") b

checkInputOutputLH' :: FilePath -> FilePath -> String -> String -> Int -> [Reqs String] -> Config -> IO (Either SomeException Bool)
checkInputOutputLH' proj src md entry i req config = try (checkInputOutputLH'' proj src md entry i req config)

checkInputOutputLH'' :: FilePath -> FilePath -> String -> String -> Int -> [Reqs String] -> Config -> IO Bool
checkInputOutputLH'' proj src md entry i req config = do
    (r, _) <- findCounterExamples proj src (T.pack entry) [] [] config

    let chAll = checkExprAll req

    mr <- validateStates proj src md entry chAll [] r
    let io = map (\(ExecRes { conc_args = i', conc_out = o}) -> i' ++ [o]) r

    let chEx = checkExprInOutCount io i req
    return $ mr && chEx

------------

-- | Checks conditions on given expressions
checkExprAll :: [Reqs String] -> [String]
checkExprAll reqList = [f | RForAll f <- reqList]

checkExprExists :: [Reqs String] -> [String]
checkExprExists reqList = [f | RExists f <- reqList]

checkExprInOutCount :: [[Expr]] -> Int -> [Reqs c] -> Bool
checkExprInOutCount exprs i reqList =
    let
        checkAtLeast = and . map ((>=) (length exprs)) $ [x | AtLeast x <- reqList]
        checkAtMost = and . map ((<=) (length exprs)) $ [x | AtMost x <- reqList]
        checkExactly = and . map ((==) (length exprs)) $ [x | Exactly x <- reqList]

        checkArgCount = and . map ((==) i . length) $ exprs
    in
    checkAtLeast && checkAtMost && checkExactly && checkArgCount
