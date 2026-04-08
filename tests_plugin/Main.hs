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