{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Test.Tasty
import Test.Tasty.HUnit

import G2.Config as G2
import G2.Interface
import G2.Liquid.Inference.Interface
import G2.Liquid.Inference.Config

import Data.Either

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
        , negTests ]

posTests :: TestTree
posTests = testGroup "Tests"
            [ posTestInference "tests_inference/test_files/Pos/Test1.hs" 
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
            -- , posTestInference "tests_inference/test_files/Pos/Test18.hs"
            -- , posTestInference "tests_inference/test_files/Pos/Test19.hs"
            , posTestInference "tests_inference/test_files/Pos/Test20.hs"
            -- , posTestInference "tests_inference/test_files/Pos/Test21.hs"
            -- , posTestInference "tests_inference/test_files/Pos/Test22.hs"
            -- , posTestInference "tests_inference/test_files/Pos/Test23.hs"
            -- , posTestInference "tests_inference/test_files/Pos/Test24.hs"
            -- , posTestInference "tests_inference/test_files/Pos/Test25.hs"
            -- , posTestInference "tests_inference/test_files/Pos/Test26.hs"
            -- , posTestInference "tests_inference/test_files/Pos/Test27.hs"
            -- , posTestInference "tests_inference/test_files/Pos/Test28.hs"
            -- , posTestInference "tests_inference/test_files/Pos/Test29.hs"
            , posTestInference "tests_inference/test_files/Pos/Test30.hs"
            , posTestInference "tests_inference/test_files/Pos/Test31.hs"
            , posTestInference "tests_inference/test_files/Pos/Test32.hs"
            , posTestInference "tests_inference/test_files/Pos/Test33.hs"
            , posTestInference "tests_inference/test_files/Pos/Test34.hs"
            , posTestInference "tests_inference/test_files/Pos/Test35.hs"
            , posTestInference "tests_inference/test_files/Pos/Test36.hs"
            , posTestInference "tests_inference/test_files/Pos/Test37.hs"
            , posTestInference "tests_inference/test_files/Pos/Test38.hs"
            , posTestInference "tests_inference/test_files/Pos/Test39.hs"
            , posTestInference "tests_inference/test_files/Pos/Test40.hs"
            , posTestInference "tests_inference/test_files/Pos/Test41.hs"
            , posTestInference "tests_inference/test_files/Pos/Test42.hs"
            , posTestInference "tests_inference/test_files/Pos/Test43.hs"

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

posTestInference :: FilePath -> TestTree
posTestInference fp = do
    testCase fp (do
        config <- G2.getConfig []
        let infconfig = mkInferenceConfig []
        res <- doTimeout 90 $ inferenceCheck infconfig config [] [fp] []

        assertBool ("Inference for " ++ fp ++ " failed.") $ maybe False isRight res
        )

negTestInference :: FilePath -> TestTree
negTestInference fp = do
    testCase fp (do
        config <- G2.getConfig []
        let infconfig = mkInferenceConfig []
        res <- doTimeout 90 $ inferenceCheck infconfig config [] [fp] []

        assertBool ("Inference for " ++ fp ++ " failed.") $ maybe False isLeft res
        )
