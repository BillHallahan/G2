module Main where

import G2.Core.Language
import G2.Core.FOL
import G2.Core.Evaluator
import G2.Core.SMT

import qualified G2.Sample.Prog1 as P1

main = do
    let entry = "test2"
    let state = initState P1.t_env P1.e_env entry
    putStrLn $ show state

    putStrLn "======================================"

    let state_1 = head $ eval state

    putStrLn $ show state_1

    putStrLn "======================================"

    let state_2 = head $ eval state_1

    putStrLn $ show state_2

    putStrLn "====================================="

    let state_3 = head $ eval state_2

    putStrLn $ show state_3

    putStrLn "====================================="

    let state_4 = head $ eval state_3

    putStrLn $ show state_4

    putStrLn "====================================="

    let state_5 = head $ eval state_4

    putStrLn $ show state_5
    {-
    let exp = App (App (Var "a") (Var "b")) (Var "c")
    let alt = (("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []]),["ba","aa"])

    putStrLn $ show $ translateExpr exp
    putStrLn $ show $ translateAlt alt
    -}

