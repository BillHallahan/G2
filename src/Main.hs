{-# LANGUAGE FlexibleContexts #-}

module Main where

import System.Environment

import HscTypes
import TyCon
import GHC hiding (Name, Type, exprType)

import qualified Data.List as L
import qualified Data.Map  as M
import Data.Maybe

import Control.Monad

import Z3.Monad


import G2.Lib.Utils
import G2.Lib.Printers

import G2.Internals.Core.Language
import G2.Internals.Core.Utils

import G2.Internals.Translation.Haskell
import G2.Internals.Translation.Prelude

import G2.Internals.Preprocessing.Defunctionalizor

import G2.Internals.Symbolic.Engine
import G2.Internals.Symbolic.Config

import G2.Internals.SMT.Z3Types
import G2.Internals.SMT.Z3

--FOR containsNonConsFunctions AND replaceFuncSLT
import qualified Data.Monoid as Mon
import qualified G2.Internals.Core.CoreManipulator as CM
--END

{-
main = do
    (num:xs) <- getArgs
    let filepath:mod:entry:xs' = xs
    raw_core <- mkRawCore filepath
    -- putStrLn "RAW CORE"
    -- putStrLn =<< outStr raw_core
    let (rt_env, re_env) = mkG2Core raw_core
    let t_env' = M.union rt_env (M.fromList prelude_t_decls)
    let e_env' = re_env  -- M.union re_env (M.fromList prelude_e_decls)
    let init_state = if num == "1" then initState t_env' e_env' mod entry else initStateWithPost t_env' e_env' mod entry (xs' !! 0)

    let defun_init_state = defunctionalize init_state

    putStrLn $ mkStateStr init_state
    putStrLn $ mkStateStr defun_init_state

    let (states, n) = runN [defun_init_state] 250

    let states' = filter (\s -> not . containsNonConsFunctions (type_env s) . curr_expr $ s) states

    putStrLn $ mkStatesStr states
    putStrLn ("Number of execution states: " ++ (show (length states)))
    putStrLn ("Number of execution states after pruning: " ++ (show (length states')))
    --putStrLn "Compiles!\n\n"
    
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
    (filepath:mod:prepost:entry:args) <- getArgs
    putStrLn "Thank you for using G2! We appear to compile, but does it work?"
    raw_core <- mkRawCore filepath

    let (rt_env, re_env) = mkG2Core raw_core
    let tenv' = M.union rt_env (M.fromList prelude_t_decls)
    let eenv' = M.insert "p1" BAD re_env-- re_env
    let init_state = defunctionalize $ initState tenv' eenv' mod entry

    putStrLn $ mkRawStateStr init_state
    
    let runs = 0 -- 20
    -- let (states, n) = runN [init_state] runs
    let states = histN [init_state] runs
    -- putStrLn $ show states
    mapM (\(ss, n) -> do
             putStrLn $ show (runs - n)
             -- putStrLn $ (show $ length ss) ++ "\n")
             mapM (\s -> putStrLn $ (mkRawStateStr s) ++ "\n") ss)
         (init states)

--Switches every occurence of a Var in the Func SLT from datatype to function
replaceFuncSLT :: CM.Manipulatable Expr m => State -> m -> m
replaceFuncSLT s e = CM.modify replaceFuncSLT' e
    where
        replaceFuncSLT' :: Expr -> Expr
        replaceFuncSLT' v@(Var n t) =
            let
                n' = M.lookup n (func_interps s)
            in
            case n' of
                    Just (n'', _) -> Var n'' (case functionType s n'' of
                                                Just t -> t
                                                Nothing -> TyBottom)
                    Nothing -> v
        replaceFuncSLT' e = e

        functionType :: State -> Name -> Maybe Type
        functionType s n = exprType <$> M.lookup n (expr_env s)

--Contains functions that are not just type constructors
containsNonConsFunctions :: (CM.Manipulatable Expr m) => TEnv -> m -> Bool
containsNonConsFunctions tenv = Mon.getAny . CM.eval (Mon.Any . containsFunctions' tenv)
    where
        containsFunctions' :: TEnv -> Expr -> Bool
        containsFunctions' tenv (App (Var n _) _) = n `notElem` (constructors tenv) && n `notElem` handledFunctions
        containsFunctions' _ _ = False

        constructors :: TEnv -> [Name]
        constructors = CM.evalDataConType (\(DataCon n _ _ _) -> [n])

        handledFunctions = ["==", ">", "<", ">=", "<=", "+", "-", "*", "/", "&&", "||"]
