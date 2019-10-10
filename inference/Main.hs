module Main (main) where

import G2.Liquid.Inference.Interface

import System.Environment

main :: IO ()
main = do
    as <- getArgs

    case as of
        (f:_) -> inference [] [f] []
        [] -> error "No path given"