{-# LANGUAGE OverloadedStrings #-}

module Main where

import Test.Tasty
import Test.Tasty.HUnit

import G2.Config
import G2.SMTSynth.Synthesizer

import Data.Maybe
import qualified Data.Text as T
import Options.Applicative
import System.Directory
import System.Timeout

main :: IO ()
main = do
    defaultMainWithIngredients
        defaultIngredients
        tests

tests :: TestTree
tests = testGroup "All Tests"
        [ smtSynthTestHeight "tests_seq_gen/tests/Test.hs" "f1"
        , smtSynthTestHeight "tests_seq_gen/tests/Test.hs" "f2"
        , smtSynthTestHeight "tests_seq_gen/tests/Test.hs" "f3"
        , smtSynthTestHeight "tests_seq_gen/tests/Test.hs" "f4"
        , smtSynthTestHeight "tests_seq_gen/tests/Test.hs" "f5"
        , smtSynthTestHeight "tests_seq_gen/tests/Test.hs" "f6"
        , smtSynthTestHeight "tests_seq_gen/tests/Test.hs" "f7"
        , smtSynthTestHeight "tests_seq_gen/tests/Test.hs" "f8"
        , smtSynthTestHeight "tests_seq_gen/tests/Test.hs" "f9"
        , smtSynthTestHeight "tests_seq_gen/tests/Test.hs" "f10"
        , smtSynthTestHeight "tests_seq_gen/tests/Test.hs" "f11"
        , smtSynthTestHeight "tests_seq_gen/tests/Test.hs" "f12"
        , smtSynthTestHeight "tests_seq_gen/tests/Test.hs" "f13"
        , smtSynthTestHeight "tests_seq_gen/tests/Test.hs" "f14"
        , smtSynthTestHeight "tests_seq_gen/tests/Test.hs" "f15"
        , smtSynthTestHeight "tests_seq_gen/tests/Test.hs" "f16"
        , smtSynthTestHeight "tests_seq_gen/tests/Test.hs" "f17"
        , smtSynthTestHeight "tests_seq_gen/tests/Test.hs" "f18"
        , smtSynthTestHeight "tests_seq_gen/tests/Test.hs" "f19"
        , smtSynthTestHeight "tests_seq_gen/tests/Test.hs" "@@"

        , smtSynthTestHeight "tests_seq_gen/tests/TestInt.hs" "f1"

        , smtSynthTestWithEqCheck "tests_seq_gen/tests/TestFloat.hs" "f1" "seq-gen/FloatEq.hs" "eqFloatList"

        , smtSynthTestVerify "tests_seq_gen/tests/Verify1.hs" "app"
        , smtSynthTestVerify "tests_seq_gen/tests/Verify1.hs" "eq"
        , smtSynthTestVerify "tests_seq_gen/tests/Verify1.hs" "myTake"
        ]

getSeqGenConfigDir :: T.Text -> IO SynthConfig
getSeqGenConfigDir file = do
    homedir <- getHomeDirectory
    handleParseResult $ execParserPure (prefs mempty) (seqGenConfig homedir) [T.unpack file]

smtSynthTestHeight :: T.Text -- ^ Filer
                   -> T.Text -- ^ Function
                   -> TestTree
smtSynthTestHeight file = smtSynthTestWithConfig (do
                                        synth_config@(SynthConfig { g2_config = config }) <- getSeqGenConfigDir file
                                        return $ synth_config { checking = ADTHeight
                                                              , g2_config = adjustConfig synth_config $ config { smt = ConCVC5, steps = 2000 } }) file

smtSynthTestVerify :: T.Text -- ^ Filer
                   -> T.Text -- ^ Function
                   -> TestTree
smtSynthTestVerify file = smtSynthTestWithConfig (do
                                        synth_config@(SynthConfig { g2_config = config }) <- getSeqGenConfigDir file
                                        let config' = config { smt = ConCVC5
                                                             , steps = 2000
                                                             , smt_strings = UseSMTStrings
                                                             , smt_strings_strictness = StrictSMTStrings }
                                        return $ synth_config { checking = Verify
                                                              , g2_config = adjustConfig synth_config config' }) file

smtSynthTestWithEqCheck :: T.Text -- ^ Filer
                        -> T.Text -- ^ Function
                        -> FilePath -- ^ eq-file
                        -> String -- ^ eq-check
                        -> TestTree
smtSynthTestWithEqCheck file func eq_f eq_c =
    smtSynthTestWithConfig (do
                    synth_config@(SynthConfig { g2_config = config }) <- getSeqGenConfigDir file
                    let synth_config' = synth_config { eq_file = Just eq_f
                                                     , eq_check = eq_c
                                                     , g2_config = adjustConfig synth_config $ config { smt = ConZ3, steps = 2000 } }
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
