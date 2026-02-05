{-# LANGUAGE OverloadedStrings #-}

module Main where

import Test.Tasty
import Test.Tasty.HUnit

import G2.Config
import G2.SMTSynth.Synthesizer

import qualified Data.Map as M
import qualified Data.Text as T
import System.Directory

main :: IO ()
main = do
    defaultMainWithIngredients
        defaultIngredients
        tests

tests :: TestTree
tests = testGroup "All Tests"
        [ smtSynthTest "tests_seq_gen/tests/Test.hs" "f1" ]

smtSynthTest :: T.Text -- ^ Function
             -> T.Text -- ^ Function
             -> TestTree
smtSynthTest = smtSynthTestWithConfig (do
                                        homedir <- getHomeDirectory
                                        let config = mkConfigDirect homedir [] M.empty
                                        return $ config { smt = ConCVC5 })

smtSynthTestWithConfig :: IO Config
                       -> T.Text -- ^ Function
                       -> T.Text -- ^ Function
                       -> TestTree
smtSynthTestWithConfig io_config src f =
    testCase (T.unpack $ src <> " " <> f) (do
        config <- io_config
        r <- genSMTFunc [] [T.unpack src] f Nothing config
        assertBool "Error" True
    )
