{-# LANGUAGE OverloadedStrings #-}

module Main where

import Test.Tasty
import Test.Tasty.HUnit

import G2.Config
import G2.SMTSynth.Synthesizer

import qualified Data.Map as M
import Data.Maybe
import qualified Data.Text as T
import System.Directory
import System.Timeout
import G2.Language.Support (State(num_steps))

main :: IO ()
main = do
    defaultMainWithIngredients
        defaultIngredients
        tests

tests :: TestTree
tests = testGroup "All Tests"
        [ smtSynthTest "tests_seq_gen/tests/Test.hs" "f1"
        , smtSynthTest "tests_seq_gen/tests/Test.hs" "f2"
        , smtSynthTest "tests_seq_gen/tests/Test.hs" "f3"
        , smtSynthTest "tests_seq_gen/tests/Test.hs" "f4"
        , smtSynthTest "tests_seq_gen/tests/Test.hs" "f5"
        , smtSynthTest "tests_seq_gen/tests/Test.hs" "f6"
        , smtSynthTest "tests_seq_gen/tests/Test.hs" "f7"
        , smtSynthTest "tests_seq_gen/tests/Test.hs" "f8"
        , smtSynthTest "tests_seq_gen/tests/Test.hs" "f9"
        , smtSynthTest "tests_seq_gen/tests/Test.hs" "f10"
        , smtSynthTest "tests_seq_gen/tests/Test.hs" "f11"
        , smtSynthTest "tests_seq_gen/tests/Test.hs" "f12"
        , smtSynthTest "tests_seq_gen/tests/Test.hs" "f13"
        , smtSynthTest "tests_seq_gen/tests/Test.hs" "f14"
        , smtSynthTest "tests_seq_gen/tests/Test.hs" "f15"
        , smtSynthTest "tests_seq_gen/tests/Test.hs" "f16"
        , smtSynthTest "tests_seq_gen/tests/Test.hs" "f17"
        , smtSynthTest "tests_seq_gen/tests/Test.hs" "f18"
        , smtSynthTest "tests_seq_gen/tests/Test.hs" "f19"
        , smtSynthTest "tests_seq_gen/tests/Test.hs" "@@"

        , smtSynthTest "tests_seq_gen/tests/TestInt.hs" "f1"
        ]

smtSynthTest :: T.Text -- ^ Function
             -> T.Text -- ^ Function
             -> TestTree
smtSynthTest = smtSynthTestWithConfig (do
                                        synth_config@(SynthConfig { g2_config = config }) <- getSeqGenConfig
                                        return $ synth_config { g2_config = adjustConfig SynthString $ config { smt = ConCVC5, steps = 2000 } })

smtSynthTestWithConfig :: IO SynthConfig
                       -> T.Text -- ^ Function
                       -> T.Text -- ^ Function
                       -> TestTree
smtSynthTestWithConfig io_config src f =
    testCase (T.unpack $ src <> " " <> f) (do
        config <- io_config
        r <- timeout (480 * 1000000) $ genSMTFunc [] [T.unpack src] f Nothing config
        assertBool "Error" (isJust r)
    )
