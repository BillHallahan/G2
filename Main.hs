module Main where

import System.Environment

import HscTypes
import TyCon
import GHC

import G2.Core.Language
import G2.Core.Evaluator
import G2.Core.Utils

import G2.Haskell.Prelude
import G2.Haskell.Translator

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
    
    (filepath:xs) <- getArgs
    raw_core <- mkRawCore filepath
    let gcore = mkG2Core raw_core
    putStrLn $ show gcore
    -- putStrLn =<< outStr raw_core

    putStrLn "Compiles!"

