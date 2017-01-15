module Main where

import G2.Core.Language
import G2.Core.Evaluator
import G2.Core.Utils

import qualified G2.Sample.Prog1 as P1
import qualified G2.Sample.Prog2 as P2

main = do
    let bar = "=============================================="
    let entry = "abstract"
    let state = initState P2.t_env P2.e_env entry
    putStrLn $ mkStateStr state
    putStrLn bar

    let (states, n) = runN [state] 10
    putStrLn $ mkStatesStr states

    putStrLn "Compiles!"

