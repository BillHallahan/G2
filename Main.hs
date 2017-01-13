module Main where

import G2.Core.Language
import G2.Core.FOL
import G2.Core.Evaluator
import G2.Core.SMT
import G2.Core.Utils

import qualified G2.Sample.Prog1 as P1
import qualified G2.Sample.Prog2 as P2

main = do
    let bar = "=============================================="
    let entry = "abstract"
    let state = initState P2.t_env P2.e_env entry
    putStrLn $ mkStateStr state
    putStrLn bar

    let states_1 = eval state
    putStrLn "1"
    putStrLn $ mkStatesStr states_1
    putStrLn bar

    let states_2 = concatMap eval states_1
    putStrLn "2"
    putStrLn $ mkStatesStr states_2
    putStrLn bar

    let states_3 = concatMap eval states_2
    putStrLn "3"
    putStrLn $ mkStatesStr states_3
    putStrLn bar

    let states_4 = concatMap eval states_3
    putStrLn "4"
    putStrLn $ mkStatesStr states_4
    putStrLn bar

    let states_5 = concatMap eval states_4
    putStrLn "5"
    putStrLn $ mkStatesStr states_5
    putStrLn bar

    let states_6 = concatMap eval states_5
    putStrLn "6"
    putStrLn $ mkStatesStr states_6
    putStrLn bar


    let states_7 = concatMap eval states_6
    putStrLn "7"
    putStrLn $ mkStatesStr states_7
    putStrLn bar


    let states_8 = concatMap eval states_7
    putStrLn "8"
    putStrLn $ mkStatesStr states_8
    putStrLn bar


    let states_9 = concatMap eval states_8
    putStrLn "9"
    putStrLn $ mkStatesStr states_9
    putStrLn bar


    let states_10 = concatMap eval states_9
    putStrLn "10"
    putStrLn $ mkStatesStr states_10
    putStrLn bar


    putStrLn "Compiles!"
