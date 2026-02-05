{-# LANGUAGE OverloadedStrings #-}

module Main where

import Test.Tasty
import Test.Tasty.HUnit

import G2.Config

import qualified Data.Text as T

main :: IO ()
main = do
    defaultMainWithIngredients
        defaultIngredients
        tests

tests :: TestTree
tests = testGroup "All Tests"
        [ ]

smtSynthTestWithConfig :: T.Text -- ^ Function
                       -> T.Text -- ^ Function
                       -> Config
                       -> TestTree
smtSynthTestWithConfig src f config =
    testCase (T.unpack $ src <> " " <> f) (do
        -- r <- genSMTFunc [] [src] Nothing config
        assertBool "Error" True
    )
