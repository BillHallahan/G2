module Main where

import System.Environment

import HscTypes
import TyCon
import GHC

import G2.Core.Defunctionalizor
import G2.Core.Language
import G2.Core.Evaluator
import G2.Core.Utils

import G2.Haskell.Prelude
import G2.Haskell.Translator

import G2.SMT.Z3

import qualified G2.Sample.Prog1 as P1
import qualified G2.Sample.Prog2 as P2

import qualified Data.List as L
import qualified Data.Map  as M

main = do
    {-
    let bar = "=============================================="
    let entry = "test"
    let t_env = M.fromList (prelude_t_decls ++ P2.t_decls)
    let e_env = M.fromList (prelude_e_decls ++ P2.e_decls)
    let state = initState t_env e_env entry
    putStrLn $ mkStateStr state
    putStrLn bar

    let (states, n) = runN [state] 10
    putStrLn $ mkStatesStr states
    -}    
    (filepath:entry:xs) <- getArgs
    raw_core <- mkRawCore filepath
    putStrLn =<< outStr raw_core
    let (rt_env, re_env) = mkG2Core raw_core
    let t_env' = M.union rt_env (M.fromList prelude_t_decls)
    let e_env' = re_env  -- M.union re_env (M.fromList prelude_e_decls)
    let init_state = initState t_env' e_env' entry
    putStrLn $ mkStateStr init_state
    
    putStrLn $ mkStatesStr [init_state]

    putStrLn "======================="

    let (states, n) = runN [init_state] 20
    putStrLn $ mkStatesStr states

    putStrLn "Compiles!"

    putStrLn . mkStateStr . defunctionalize $ init_state
