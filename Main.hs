module Main where

import G2.Core.Language
import G2.Core.Prelude
import G2.Core.Evaluator
import G2.Core.Utils

import qualified G2.Sample.Prog1 as P1
import qualified G2.Sample.Prog2 as P2

import qualified Data.List as L
import qualified Data.Map  as M

main = do
    let bar = "=============================================="
    let entry = "test1"
    let t_env = M.fromList (prelude_decls ++ P1.t_decls)
    let e_env = M.fromList P1.e_decls
    let state = initState t_env e_env entry
    putStrLn $ mkStateStr state
    putStrLn bar

    let (states, n) = runN [state] 10
    putStrLn $ mkStatesStr states

    putStrLn "Compiles!"

