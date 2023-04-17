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
        [ checkPackage "tests/RewriteVerify/PluginTests/Simple" ["add_assoc", "fg", "fg_toint"] ["f_one"]]

checkPackage :: FilePath
             -> [String] -- ^ Rules that should be verified
             -> [String] -- ^ Rules that should have counterexamples
             -> TestTree
checkPackage loc correct incorrect =
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

buildPackage :: FilePath -> IO String
buildPackage loc = do
    (Nothing, Nothing, Nothing, clean_ph) <- createProcess
                                    $ (proc "cabal" ["clean"]) { cwd = Just loc
                                                               , std_out = Inherit }
    waitForProcess clean_ph
    (Nothing, Nothing, Nothing, build_g2_ph) <- createProcess
                                    $ (proc "cabal" ["build", "g2"]) { cwd = Just loc }
    waitForProcess build_g2_ph
    (Nothing, Just stdout, Nothing, ph) <- createProcess
                                    $ (proc "cabal" ["build"]) { cwd = Just loc
                                                               , std_out = CreatePipe }
    waitForProcess ph
    out <- hGetContents stdout
    _ <- evaluate (length out)
    hClose stdout
    return out

isVerified :: String -> String -> Bool
isVerified f = isSubstringOf (f ++ " - verified")

hasCEx :: String -> String -> Bool
hasCEx f = isSubstringOf (f ++ " - counterexample found")

isSubstringOf :: String -> String -> Bool
isSubstringOf = isInfixOf