{-# LANGUAGE OverloadedStrings #-}
module InputOutputTest ( checkInputOutput
                       , checkInputOutputLH ) where

import Test.Tasty
import Test.Tasty.HUnit

import Control.Exception
import qualified Data.Map.Lazy as M
import qualified Data.Text as T
import System.FilePath

import G2.Config
import G2.Initialization.MkCurrExpr
import G2.Interface
import G2.Language
import G2.Liquid.Config
import G2.Liquid.Interface
import G2.Translation

import Reqs
import TestUtils

checkInputOutput :: FilePath -> String -> String -> Int  -> [Reqs String] ->  TestTree
checkInputOutput src md entry stps req = checkInputOutputWithConfig [src] md entry req 
                                              (do config <- mkConfigTestIO
                                                  return $ config {steps = stps})

checkInputOutputWithConfig :: [FilePath] -> String -> String -> [Reqs String] -> IO Config -> TestTree
checkInputOutputWithConfig src md entry req config_f = do
    testCase (show src) (do
      config <- config_f
      r <- doTimeout (timeLimit config) $ checkInputOutput' src md entry req config

      let (b, e) = case r of
              Nothing -> (False, "\nTimeout")
              Just (Left e') -> (False, "\n" ++ show e')
              Just (Right (b', _)) -> (b', "")

      assertBool ("Input/Output for file " ++ show src ++ " failed on function " ++ entry ++ "." ++ e) b 
      )

checkInputOutput' :: [FilePath] 
                  -> String 
                  -> String 
                  -> [Reqs String] 
                  -> Config 
                  -> IO (Either SomeException (Bool, [ExecRes ()]))
checkInputOutput' src md entry req config = try (checkInputOutput'' src md entry req config)

checkInputOutput'' :: [FilePath] 
                   -> String 
                   -> String 
                   -> [Reqs String] 
                   -> Config 
                   -> IO (Bool, [ExecRes ()])
checkInputOutput'' src md entry req config = do
    let proj = map takeDirectory src
    (mb_modname, exg2) <- translateLoaded proj src simplTranslationConfig config

    let (init_state, bindings) = initStateWithCall exg2 False (T.pack entry) mb_modname (mkCurrExpr Nothing Nothing) mkArgTys config
    
    (r, _) <- runG2WithConfig init_state config bindings

    let chAll = checkExprAll req
    mr <- validateStates proj src md entry chAll [] r
    let io = map (\(ExecRes { conc_args = i, conc_out = o}) -> i ++ [o]) r

    let chEx = checkExprInOutCount io req
    
    return $ (mr && chEx, r)

------------

checkInputOutputLH :: [FilePath] -> [FilePath] -> String -> String -> Int -> [Reqs String] ->  IO TestTree
checkInputOutputLH proj src md entry stps req = checkInputOutputLHWithConfig proj src md entry req
                                                      (do config <- mkConfigTestIO
                                                          return $ config {steps = stps})

checkInputOutputLHWithConfig :: [FilePath] -> [FilePath] -> String -> String -> [Reqs String] -> IO Config -> IO TestTree
checkInputOutputLHWithConfig proj src md entry req config_f = do
    config <- config_f
    r <- doTimeout (timeLimit config) $ checkInputOutputLH' proj src md entry req config

    let b = case r of
            Just (Right b') -> b'
            _ -> False

    return . testCase (show src) $ assertBool ("Input/Output for file " ++ show src ++ " failed on function " ++ entry ++ ".") b

checkInputOutputLH' :: [FilePath] -> [FilePath] -> String -> String -> [Reqs String] -> Config -> IO (Either SomeException Bool)
checkInputOutputLH' proj src md entry req config = try (checkInputOutputLH'' proj src md entry req config)

checkInputOutputLH'' :: [FilePath] -> [FilePath] -> String -> String -> [Reqs String] -> Config -> IO Bool
checkInputOutputLH'' proj src md entry req config = do
    let lhconfig = mkLHConfigDirect [] M.empty
    ((r, _), _) <- findCounterExamples proj src (T.pack entry) config lhconfig

    let chAll = checkExprAll req

    mr <- validateStates proj src md entry chAll [] r
    let io = map (\(ExecRes { conc_args = i', conc_out = o}) -> i' ++ [o]) r

    let chEx = checkExprInOutCount io req
    return $ mr && chEx

------------

-- | Checks conditions on given expressions
checkExprAll :: [Reqs String] -> [String]
checkExprAll reqList = [f | RForAll f <- reqList]

checkExprExists :: [Reqs String] -> [String]
checkExprExists reqList = [f | RExists f <- reqList]

checkExprInOutCount :: [[Expr]] -> [Reqs c] -> Bool
checkExprInOutCount exprs reqList =
    let
        checkAtLeast = and . map ((>=) (length exprs)) $ [x | AtLeast x <- reqList]
        checkAtMost = and . map ((<=) (length exprs)) $ [x | AtMost x <- reqList]
        checkExactly = and . map ((==) (length exprs)) $ [x | Exactly x <- reqList]
    in
    checkAtLeast && checkAtMost && checkExactly
