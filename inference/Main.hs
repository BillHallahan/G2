module Main (main) where

import G2.Config
import G2.Liquid.Inference.Interface

import System.Environment

main :: IO ()
main = do
    as <- getArgs
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