module Main where

import System.Environment

import HscTypes
import TyCon
import GHC

import qualified Data.List as L
import qualified Data.Map  as M
import Data.Maybe

import Control.Monad

import Z3.Monad


import G2.Lib.Utils
import G2.Lib.Deprecated.Utils
import G2.Lib.Printers

import G2.Core.Language
import G2.Core.Utils

import G2.Haskell.Translator
import G2.Haskell.Prelude
-- import G2.Translation.Haskell
import G2.Translation.Interface

import G2.Preprocessing.Defunctionalizor
import G2.Preprocessing.Interface

import G2.Symbolic.Engine
import G2.Symbolic.Config
import G2.Symbolic.Interface

import G2.SMT.Z3Types
import G2.SMT.Z3
import G2.SMT.Interface

{-
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

    let defun_init_state = defunctionalize init_state

    let (states, n) = runN [defun_init_state] 250

    let states' = filter (\s -> not . containsNonConsFunctions (type_env s) . curr_expr $ s) states

    putStrLn $ mkStatesStr states'
    putStrLn ("Number of execution states: " ++ (show (length states')))
    -- --putStrLn "Compiles!\n\n"
    
    if num == "1" then
        mapM_ (\s@State {curr_expr = expr, path_cons = path_cons', sym_links = sym_links'} -> do
            (r, m) <- evalZ3 . reachabilitySolverZ3 $ s
            if r == Sat then do
                -- putStrLn . mkExprStr $ expr
                -- putStrLn . mkPCStr $ path_cons'
                -- putStrLn . mkSLTStr $ sym_links'
                -- putStrLn " => "
                if Nothing `notElem` m then
                    putStrLn . mkExprHaskell . foldl (\a a' -> App a a') (Var entry TyBottom) . replaceFuncSLT s . map (fromJust) $ m
                else
                    print "Error"
            else return ()) states'
    else
        mapM_ (\s@State {curr_expr = expr, path_cons = path_cons', sym_links = sym_links'} -> do
            (r, m) <- evalZ3 . outputSolverZ3 $ s
            if r == Sat then do
                -- putStrLn "HERE"
                -- putStrLn . mkExprStr $ expr
                -- putStrLn . mkPCStr $ path_cons'
                -- putStrLn . mkSLTStr $ sym_links'
                -- putStrLn " => "
                if Nothing `notElem` m then
                    putStrLn . mkExprHaskell . foldl (\a a' -> App a a') (Var (xs' !! 0) TyBottom) . replaceFuncSLT s . map (fromJust) $ m
                else
                    print "Error"
            else return ()) states'
-}

main = do
    (filepath:prepost:entry:args) <- getArgs
    putStrLn "Thank you for using G2! We appear to compile, but does it work?"
    (filepath:prepost:entry:args) <- getArgs
    raw_core <- mkRawCore filepath

    let (rt_env, re_env) = mkG2Core raw_core
    let tenv' = M.union rt_env (M.fromList prelude_t_decls)
    let eenv' = M.insert "p1" BAD re_env-- re_env
    let init_state = defunctionalize $ initState tenv' eenv' entry
    let runs = 20
    -- let (states, n) = runN [init_state] runs
    let states = histN [init_state] runs
    -- putStrLn $ show states
    mapM (\(ss, n) -> do
             putStrLn $ show (runs - n)
             -- putStrLn $ (show $ length ss) ++ "\n")
             mapM (\s -> putStrLn $ (mkRawStateStr s) ++ "\n") ss)
         (init states)

