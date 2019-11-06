module Main (main) where

import G2.Config
import G2.Liquid.Inference.Interface
import G2.Liquid.Inference.QualifGen

import System.Environment

main :: IO ()
main = do
    as <- getArgs

    if "--qualif" `elem` as then qualifGen "qualif.hquals" else callInference as


callInference :: [String] -> IO ()
callInference as = do
    config <- getConfig as

    case as of
        (f:_) -> do
            gs <- inference config [] [f] []
            case gs of
                Left gs' -> do
                    putStrLn "Counterexample"
                    print gs'
                Right gs' -> do
                    putStrLn "Safe"
                    print gs'
        [] -> error "No path given"