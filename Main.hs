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
    let (rt_env, re_env) = mkG2Core raw_core
    let t_env' = M.union rt_env (M.fromList prelude_t_decls)
    let e_env' = re_env  -- M.union re_env (M.fromList prelude_e_decls)
    let init_state = initState t_env' e_env' entry
    putStrLn $ mkStateStr init_state
    
    putStrLn $ mkStatesStr [init_state]

    putStrLn "======================="

    let (states, n) = runN [init_state] 20
    putStrLn $ mkStatesStr states


    printModel $ states !! 0

    putStrLn "Compiles!"

    let (t, env, ex, pc) = init_state
    let check = (M.elems env) !! 0
    putStrLn ("check = " ++ (mkExprStr check))
    putStrLn "===="
    mapM_ (mapM_ putStrLn . map (mkExprStr) . findLeadingHigherOrderFuncs) . M.elems $ env

    print . countExpr $ check
    print . countTypes $ check
    print . countExpr $ init_state
    putStrLn "------"

    print . map (\tt -> case tt of TyAlg _ d -> d) . M.elems $ t
    print . map countTypes . map (\tt -> case tt of TyAlg _ d -> d) . M.elems $ t

    print . M.elems $ t
    print . map countTypes . M.elems $ t

    print . countTypes $ t
    print . countTypes $ env
    print . countTypes $ ex
    print . countTypes $ pc
    print . countTypes $ init_state

    putStrLn $ mkStateStr init_state
    --mapM_ (putStrLn . mkExprStr)  (findLeadingHigherOrderFuncs $ (M.elems env) !! 0)

    putStrLn "----"

    mapM_ (putStrLn . mkExprStr)  (findLeadingHigherOrderFuncs $ init_state)

    putStrLn "???????"

    mapM_ (putStrLn . mkExprStr)  (findLeadingHigherOrderFuncCalls $ init_state)

    putStrLn "||||||||"

    print . leadingHigherOrderFuncTypesToApplies $ init_state

    print . findPassedInFuncs $ init_state

    mapM_ (\(n, e, t) -> putStrLn ((n) ++ "\n" ++ (show t) ++ "\n" ++ (show . typeArgCount $ t)) ) (map (\(n, e) -> (n, e, typeOf e) ) (M.toList  env))

    putStrLn "]]]]]]]"
    print . findIthArg "t" init_state $ 0
    print . findIthArg "t" init_state $ 1
    print . findIthArg "t" init_state $ 2

    putStrLn "######"
    let foundCalls = findAllCalls "t" init_state
    mapM_ (putStrLn . mkExprStr) foundCalls
    print . length $ foundCalls

    --print . length . findHigherOrderFuncs $ (M.elems env) !! 0
    --print . length . L.nub . findHigherOrderFuncs $ (M.elems env) !! 0
