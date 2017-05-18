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
import Data.Maybe

import Control.Monad

import Z3.Monad

main = do
    (num:xs) <- getArgs
    let filepath:entry:xs' = xs
    raw_core <- mkRawCore filepath
    -- putStrLn "RAW CORE"
    -- putStrLn =<< outStr raw_core
    let (rt_env, re_env) = mkG2Core raw_core
    let t_env' = M.union rt_env (M.fromList prelude_t_decls)
    let e_env' = re_env  -- M.union re_env (M.fromList prelude_e_decls)
    let init_state = if num == "1" then initState t_env' e_env' entry else initStateWithPost t_env' e_env' entry (xs' !! 0)

    -- putStrLn "INIT STATE"
    -- putStrLn $ show init_state

    -- putStrLn "mkStateStr of INIT STATE"
    -- putStrLn $ mkStatesStr [init_state]

    -- putStrLn "HIGHER"

    -- putStrLn "+++++++++++++++++++++++++"


    let defun_init_state = defunctionalize init_state

    -- putStrLn $ mkStateStr init_state
    
    -- putStrLn $ mkStatesStr [defun_init_state]

    -- putStrLn "======================="

    -- testThis [(defun_init_state, 0)]

    -- foldM (\s i -> do
    --     putStrLn ( "*******" ++ show i)
    --     putStrLn . mkExprEnvStr . eEnv $ s
    --     putStrLn . mkExprStr . cExpr $ s
    --     putStrLn "-----"
    --     return ((evaluate s) !! 0)) defun_init_state [0..5000]

    let (states, n) = runN [defun_init_state] 200

    -- temporary?
    let states' = filter (\s -> not . containsNonConsFunctions (tEnv s) . cExpr $ s) states
    -- temporary?

    -- putStrLn "#############"
    -- putStrLn . mkStatesStr $ states

    -- --putStrLn $ mkStatesStr states
    -- putStrLn ("Number of execution states: " ++ (show (length states')))
    -- --putStrLn "Compiles!\n\n"
    
    if num == "1" then
        mapM_ (\s@State {cExpr = expr, pc = pc', slt = slt'} -> do
            (r, m) <- evalZ3 . reachabilitySolverZ3 $ s
            if r == Sat then do
                -- putStrLn . mkExprStr $ expr
                -- putStrLn . mkPCStr $ pc'
                -- putStrLn . mkSLTStr $ slt'
                -- putStrLn " => "
                if Nothing `notElem` m then
                    putStrLn . mkExprHaskell . foldl (\a a' -> App a a') (Var entry TyBottom) . replaceFuncSLT s . map (fromJust) $ m
                else
                    print "Error"
            else return ()) states'
    else
        mapM_ (\s@State {cExpr = expr, pc = pc', slt = slt'} -> do
            (r, m) <- evalZ3 . outputSolverZ3 $ s
            if r == Sat then do
                -- putStrLn . mkExprStr $ expr
                -- putStrLn . mkPCStr $ pc'
                -- putStrLn . mkSLTStr $ slt'
                -- putStrLn " => "
                if Nothing `notElem` m then
                    putStrLn . mkExprHaskell . foldl (\a a' -> App a a') (Var (xs' !! 0) TyBottom) . replaceFuncSLT s .map (fromJust) $ m
                else
                    print "Error"
            else return ()) states'
