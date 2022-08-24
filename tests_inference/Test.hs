{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Test.Tasty
import Test.Tasty.HUnit

import G2.Config as G2
import G2.Interface
import G2.Liquid.Config
import G2.Liquid.Inference.Interface
import G2.Liquid.Inference.Config
import G2.Liquid.Inference.G2Calls

import Data.Time.Clock
import Data.Either
import qualified Data.Map.Lazy as M
import qualified Data.Text as T

-- Run with no arguments for default test cases.
-- All default test cases should pass.
-- Run with flag '--test-options="todo yes"' to run test cases corresponding to to-be-fixed bugs.
main :: IO ()
main = do
    defaultMainWithIngredients
        defaultIngredients
        tests

tests :: TestTree
tests = testGroup "All Tests"
        [ posTests
        , negTests
        , cexTests ]

posTests :: TestTree
posTests = testGroup "Tests"
            [ posTestInference "tests_inference/test_files/Pos/HigherOrder.hs"
            , posTestInference "tests_inference/test_files/Pos/HigherOrder2.hs"
            , posTestInference "tests_inference/test_files/Pos/HigherOrder3.hs"
            -- , posTestInference "tests_inference/test_files/Pos/HigherOrder4.hs"

            , posTestInference "tests_inference/test_files/Pos/Test1.hs" 
            , posTestInference "tests_inference/test_files/Pos/Test2.hs"
            , posTestInference "tests_inference/test_files/Pos/Test3.hs"
            , posTestInference "tests_inference/test_files/Pos/Test4.hs"
            , posTestInference "tests_inference/test_files/Pos/Test5.hs"
            , posTestInference "tests_inference/test_files/Pos/Test6.hs"
            , posTestInference "tests_inference/test_files/Pos/Test7.hs"
            , posTestInference "tests_inference/test_files/Pos/Test8.hs"
            , posTestInference "tests_inference/test_files/Pos/Test9.hs"
            , posTestInference "tests_inference/test_files/Pos/Test10.hs"
            , posTestInference "tests_inference/test_files/Pos/Test11.hs"
            , posTestInference "tests_inference/test_files/Pos/Test12.hs"
            , posTestInference "tests_inference/test_files/Pos/Test13.hs"
            , posTestInference "tests_inference/test_files/Pos/Test14.hs"
            , posTestInference "tests_inference/test_files/Pos/Test15.hs"
            , posTestInference "tests_inference/test_files/Pos/Test16.hs"
            , posTestInference "tests_inference/test_files/Pos/Test17.hs"
            , posTestInference "tests_inference/test_files/Pos/Test18.hs"
            , posTestInference "tests_inference/test_files/Pos/Test19.hs"
            , posTestInference "tests_inference/test_files/Pos/Test20.hs"
            , posTestInference "tests_inference/test_files/Pos/Test21.hs"
            , posTestInference "tests_inference/test_files/Pos/Test22.hs"
            -- , posTestInference "tests_inference/test_files/Pos/Test23.hs"
            , posTestInference "tests_inference/test_files/Pos/Test24.hs"
            , posTestInference "tests_inference/test_files/Pos/Test25.hs"
            , posTestInference "tests_inference/test_files/Pos/Test26.hs"
            , posTestInference "tests_inference/test_files/Pos/Test27.hs"
            , posTestInference "tests_inference/test_files/Pos/Test28.hs"
            , posTestInference "tests_inference/test_files/Pos/Test29.hs"
            , posTestInference "tests_inference/test_files/Pos/Test30.hs"
            , posTestInference "tests_inference/test_files/Pos/Test31.hs"
            , posTestInference "tests_inference/test_files/Pos/Test32.hs"
            , posTestInference "tests_inference/test_files/Pos/Test33.hs"
            , posTestInference "tests_inference/test_files/Pos/Test34.hs"
            , posTestInference "tests_inference/test_files/Pos/Test35.hs"
            , posTestInference "tests_inference/test_files/Pos/Test36.hs"
            , posTestInference "tests_inference/test_files/Pos/Test37.hs"
            -- , posTestInferenceWithTimeOut 240 15 "tests_inference/test_files/Pos/Test38.hs"
            , posTestInference "tests_inference/test_files/Pos/Test39.hs"
            , posTestInference "tests_inference/test_files/Pos/Test40.hs"
            , posTestInference "tests_inference/test_files/Pos/Test41.hs"
            , posTestInference "tests_inference/test_files/Pos/Test42.hs"
            , posTestInference "tests_inference/test_files/Pos/Test43.hs"
            , posTestInference "tests_inference/test_files/Pos/Test44.hs"
            , posTestInference "tests_inference/test_files/Pos/Test45.hs"

            , posTestInference "tests_inference/test_files/Pos/Sets1.hs"
            , posTestInference "tests_inference/test_files/Pos/Sets2.hs"
            , posTestInference "tests_inference/test_files/Pos/Sets3.hs"
            , posTestInference "tests_inference/test_files/Pos/Sets4.hs"
            , posTestInference "tests_inference/test_files/Pos/Sets5.hs"
            , posTestInference "tests_inference/test_files/Pos/Sets6.hs"
            , posTestInference "tests_inference/test_files/Pos/Sets7.hs"
            , posTestInference "tests_inference/test_files/Pos/Sets8.hs"
            , posTestInference "tests_inference/test_files/Pos/Sets9.hs"
            -- , posTestInference "tests_inference/test_files/Pos/Sets10.hs"

            , posTestInference "tests_inference/test_files/Pos/MeasComp1.hs" 
            , posTestInference "tests_inference/test_files/Pos/MeasComp2.hs"
            , posTestInference "tests_inference/test_files/Pos/MeasComp3.hs"  ]

negTests :: TestTree
negTests = testGroup "Tests"
            [ negTestInference "tests_inference/test_files/Neg/Test1.hs"
            , negTestInference "tests_inference/test_files/Neg/Test2.hs"
            , negTestInference "tests_inference/test_files/Neg/Test3.hs"
            , negTestInference "tests_inference/test_files/Neg/Test4.hs"
            , negTestInference "tests_inference/test_files/Neg/Test5.hs"
            , negTestInference "tests_inference/test_files/Neg/Test6.hs" ]

cexTests :: TestTree
cexTests = testGroup "Tests"
            [ cexTest "tests_inference/test_files/CEx/CEx1.hs" "zipWith"
            , cexTest "tests_inference/test_files/CEx/CEx2.hs" "mapReduce" ]

posTestInferenceWithTimeOut :: Int -> NominalDiffTime -> FilePath -> TestTree
posTestInferenceWithTimeOut to to_se fp = do
    testCase fp (do
        config <- G2.getConfigDirect
        let infconfig = (mkInferenceConfigDirect []) { timeout_se = to_se }
        let lhconfig = mkLHConfigDirect [] M.empty
        res <- doTimeout to $ inferenceCheck infconfig config lhconfig [] [fp]

        assertBool ("Inference for " ++ fp ++ " failed.") $ maybe False (isRight . snd) res
        )

posTestInference :: FilePath -> TestTree
posTestInference = posTestInferenceWithTimeOut 120 5

negTestInference :: FilePath -> TestTree
negTestInference fp = do
    testCase fp (do
        config <- G2.getConfigDirect
        let infconfig = mkInferenceConfigDirect []
        let lhconfig = mkLHConfigDirect [] M.empty
        res <- doTimeout 90 $ inferenceCheck infconfig config lhconfig [] [fp]

        assertBool ("Inference for " ++ fp ++ " failed.") $ maybe False (isLeft . snd) res
        )

cexTest :: FilePath -> String -> TestTree
cexTest fp func =
    testCase fp (do
        config <- G2.getConfigDirect
        let infconfig = (mkInferenceConfigDirect []) { timeout_se = 10 }
        let lhconfig = mkLHConfigDirect [] M.empty
        res <- doTimeout 25 $ runLHInferenceAll infconfig config lhconfig (T.pack func) [] [fp]
        assertBool ("Counterexample generation for " ++ func ++ " in " ++ fp ++ " failed.") $ maybe False (not . null . fst) res
        )
