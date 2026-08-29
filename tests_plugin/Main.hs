{-# LANGUAGE CPP #-}

module Main where

import Test.Tasty
import Test.Tasty.HUnit

import Control.Exception
import Data.List
import System.IO
import System.Process

main :: IO ()
main = do
    defaultMainWithIngredients
        defaultIngredients
        tests

tests :: TestTree
tests = testGroup "All Tests"
        [ checkG2Package "tests/G2Plugin/Simple" ["f", "g", "recCall"]
        , checkG2PackageEquiv "tests/G2Plugin/Strings"
                                -- Equivalent functions
                                [
                                  -- Strings
                                  ("f", "f2")
                                , ("myApp", "app")
                                , ("appMult", "smtAppMult")

                                , ("sumList", "smtSumList")
                                , ("sumList2", "smtSumList2")

                                , ("myIntersperse", "smtMyIntersperse")
                                , ("myIntersperse2", "smtMyIntersperse2")

                                , ("myIntersperseBegin", "smtMyIntersperseBegin")
                                , ("myIntersperseBegin2", "smtMyIntersperseBegin2")

                                , ("myRev", "smtMyRev")

                                , ("makeFourthElemSix", "smtMakeFourthElemSix")

                                -- Tuples
                                , ("appTuple", "smtAppTuple")
                                , ("pairA", "smtPairA")

-- This test fails on GitHub CI for GHC 9.8.4, specifically (works locally.)
#if __GLASGOW_HASKELL__ >= 910 || __GLASGOW_HASKELL__ < 908
                                , ("myZip", "smtMyZip")
#endif
                                , ("myA", "smtMyA")
                                , ("myUnzip", "smtMyUnzip")

                                -- MoreTuples
                                , ("listTuple", "smtListTuple")
                                , ("pairInt", "smtPairInt")
                                , ("pairInt'", "smtPairInt'")
                                , ("myZipInt", "smtMyZipInt")
                                , ("myUnzipInt", "smtMyUnzipInt")
                                , ("myRevInt", "smtMyRevInt")

                                -- Regex
                                , ("isNum", "smtIsNum")
                                , ("containsFour", "smtContainsFour")
                                , ("noPat", "smtNoPat")

                                -- Zeno
                                , ("len", "lenSMT")
                                , ("rev", "revSMT")
                                , ("null", "nullSMT")
                                , ("delete", "deleteSMT")
                                , ("++", "appendSMT")
                                , ("elem", "elemSMT")
                                , ("drop", "dropSMT")
                                , ("take", "takeSMT")
                                , ("count", "countSMT")
                                , ("last", "lastSMT")
                                , ("butlast", "butlastSMT")
                                , ("map", "mapSMT")
                                , ("ins1", "ins1SMT")
                                ]

                                -- Non-equivalent functions
                                [
                                  -- Strings
                                  ("corr", "smtCorr")
                                , ("incorr", "smtIncorr")
                                , ("addTwoAll", "smtAddTwoAll")
                                , ("sumListBad", "smtSumListBad")
                                , ("myIntersperseBad", "smtMyIntersperseBad")
                                , ("myIntersperseBeginBad", "smtMyIntersperseBeginBad")
                                , ("myRevBad", "smtMyRevBad")
                                , ("myRevApp1Bad", "smtMyRevApp1Bad")

                                -- Tuples
                                , ("appTupleBad", "smtAppTupleBad")
                                , ("pairABad", "smtPairA")
                                , ("myZipBad", "smtMyZip")
                                , ("myLookupBad", "smtMyLookupBad")

                                -- MoreTuples
                                , ("myZipBadInt", "smtMyZipBadInt")

                                -- Regex
                                , ("isNumBad", "smtIsNumBad")
                                , ("containsFourBad", "smtContainsFourBad")
                                , ("noPatBad", "smtNoPatBad")
                                ]
        , checkNebulaPackage "tests/RewriteVerify/PluginTests/Simple" ["add_assoc", "fg", "fg_toint"] ["f_one"]]

-------------------------------------------------------------------------------
-- G2
-------------------------------------------------------------------------------

checkG2Package :: FilePath
               -> [String] -- ^ Functions that should be executed
               -> TestTree
checkG2Package loc funcs =
    withResource
        (buildPackage loc)
        (\_ -> return ()) $
        \io_out ->
            testGroup
            loc
            $ ranFunc io_out funcs

ranFunc :: IO String -> [String] -> [TestTree]
ranFunc io_out =
    map (\f -> testCase
                f
                (do
                    out <- io_out
                    assertBool ("Not run " ++ f) (isSubstringOf f out))
        )

checkG2PackageEquiv :: FilePath
                    -> [(String, String)] -- ^ Functions that should be equivalent
                    -> [(String, String)] -- ^ Functions that should be inequivalent
                    -> TestTree
checkG2PackageEquiv loc funcs_equiv funcs_inequiv =
    withResource
        (buildPackage loc)
        (\_ -> return ()) $
        \io_out ->
            testGroup
            loc
            $ ranFuncEquiv io_out funcs_equiv ++ ranFuncInequiv io_out funcs_inequiv

ranFuncEquiv :: IO String -> [(String, String)] -> [TestTree]
ranFuncEquiv io_out =
    map (\(f1, f2) -> testCase
                (f1 ++ " and " ++ f2)
                (do
                    out <- io_out
                    assertBool ((if checkInequiv f1 f2 out
                                     then "Found inequivalent " ++ f1 ++ " and " ++ f2
                                     else "Not run " ++ f1 ++ " and " ++ f2) ++ "\nFull output:\n" ++ out)
                               (checkEquiv f1 f2 out))
        )

ranFuncInequiv :: IO String -> [(String, String)] -> [TestTree]
ranFuncInequiv io_out =
    map (\(f1, f2) -> testCase
                (f1 ++ " and " ++ f2)
                (do
                    out <- io_out
                    assertBool ((if checkEquiv f1 f2 out
                                     then "Found equivalent " ++ f1 ++ " and " ++ f2
                                     else "Not run " ++ f1 ++ " and " ++ f2) ++ "\nFull output:\n" ++ out)
                               (checkInequiv f1 f2 out))
        )

checkEquiv :: String -> String -> String -> Bool
checkEquiv f1 f2 = isSubstringOf ("Equivalent: " ++ f1 ++ " and " ++ f2)

checkInequiv :: String -> String -> String -> Bool
checkInequiv f1 f2 = isSubstringOf ("Equivalence not proven: " ++ f1 ++ " and " ++ f2)

-------------------------------------------------------------------------------
-- Nebula
-------------------------------------------------------------------------------

checkNebulaPackage :: FilePath
                   -> [String] -- ^ Rules that should be verified
                   -> [String] -- ^ Rules that should have counterexamples
                   -> TestTree
checkNebulaPackage loc correct incorrect =
    withResource
        (buildPackage loc)
        (\_ -> return ()) $
        \io_out ->
            testGroup
            loc
            $ verifiedTests io_out correct ++ cexTests io_out incorrect

verifiedTests :: IO String -> [String] -> [TestTree]
verifiedTests io_out correct =
    map (\c -> testCase
                c
                (do
                    out <- io_out
                    assertBool ("Not verified") (isVerified c out && not (hasCEx c out)))
        ) correct

cexTests :: IO String -> [String] -> [TestTree]
cexTests io_out incorrect =
    map (\i -> testCase
                i
                (do
                    out <- io_out
                    assertBool ("No counterexample") (not (isVerified i out) && hasCEx i out))
        ) incorrect

isVerified :: String -> String -> Bool
isVerified f = isSubstringOf (f ++ " - verified")

hasCEx :: String -> String -> Bool
hasCEx f = isSubstringOf (f ++ " - counterexample found")

-------------------------------------------------------------------------------
-- Building Packages
-------------------------------------------------------------------------------

buildPackage :: FilePath -> IO String
buildPackage loc = do
    (Nothing, Nothing, Nothing, clean_ph) <- createProcess
                                    $ (proc "cabal" ["clean"]) { cwd = Just loc
                                                               , std_out = Inherit }
    _ <- waitForProcess clean_ph
    (Nothing, Nothing, Nothing, build_g2_ph) <- createProcess
                                    $ (proc "cabal" ["build", "g2"]) { cwd = Just loc }
    _ <- waitForProcess build_g2_ph
    (Nothing, Just sout, Nothing, ph) <- createProcess
                                    $ (proc "cabal" ["build"]) { cwd = Just loc
                                                               , std_out = CreatePipe }
    _ <- waitForProcess ph
    out <- hGetContents sout
    _ <- evaluate (length out)
    hClose sout
    return out

isSubstringOf :: String -> String -> Bool
isSubstringOf = isInfixOf
