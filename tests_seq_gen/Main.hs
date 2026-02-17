{-# LANGUAGE OverloadedStrings #-}

module Main where

import Test.Tasty
import Test.Tasty.HUnit

import G2.Config
import G2.SMTSynth.Synthesizer

import qualified Data.Map as M
import Data.Maybe
import qualified Data.Text as T
import Options.Applicative
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

        , smtSynthTestWithEqCheck "tests_seq_gen/tests/TestFloat.hs" "f1" "seq-gen/FloatEq.hs" "eqFloatList"
        ]

getSeqGenConfigDir :: T.Text -> IO SynthConfig
getSeqGenConfigDir file = do
    homedir <- getHomeDirectory
    handleParseResult $ execParserPure (prefs mempty) (seqGenConfig homedir) [T.unpack file]

smtSynthTest :: T.Text -- ^ Filer
             -> T.Text -- ^ Function
             -> TestTree
smtSynthTest file = smtSynthTestWithConfig (do
                                        synth_config@(SynthConfig { synth_mode = sy_m, g2_config = config }) <- getSeqGenConfigDir file
                                        return $ synth_config { g2_config = adjustConfig sy_m $ config { smt = ConCVC5, steps = 2000 } }) file

smtSynthTestWithEqCheck :: T.Text -- ^ Filer
                        -> T.Text -- ^ Function
                        -> FilePath -- ^ eq-file
                        -> String -- ^ eq-check
                        -> TestTree
smtSynthTestWithEqCheck file func eq_f eq_c =
    smtSynthTestWithConfig (do
                    synth_config@(SynthConfig { synth_mode = sy_m, g2_config = config }) <- getSeqGenConfigDir file
                    let synth_config' = synth_config { eq_file = Just eq_f
                                                     , eq_check = eq_c
                                                     , g2_config = adjustConfig sy_m $ config { smt = ConZ3, steps = 2000 } }
                    return $ synth_config') file func

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
