module Main where

import System.Environment

import HscTypes
import TyCon
import GHC hiding (Name, Type, exprType)

import qualified Data.Map as M

import G2.Lib.Utils
import G2.Lib.Printers

import G2.Internals.Interface
import G2.Internals.Core
import G2.Internals.Translation
import G2.Internals.Preprocessing
import G2.Internals.Symbolic
import G2.Internals.SMT

main = do
    (num:args) <- getArgs
    let filepath:mod:entry:args' = args

    raw_core <- mkGHCCore filepath
    let (rt_env, re_env) = mkG2Core raw_core

    -- putStrLn "RAW CORE"
    -- putStrLn =<< outStr raw_core
    let t_env' = M.union rt_env (M.fromList prelude_t_decls)
    let e_env' = re_env
    let init_state = initState t_env' e_env' Nothing Nothing entry
    -- let init_state = if num == "1" then initState t_env' e_env' mod Nothing Nothing entry else initState t_env' e_env' mod (Just entry) (Just $ args' !! 0) (args' !! 1)
        
    hhp <- getZ3ProcessHandles

    in_out <- run smt2 hhp init_state

    mapM_ (\(inArg, ex) -> do
            putStrLn . mkExprHaskell 
                . foldl (\a a' -> App a a') (Var (args' !! 0) TyBottom) $ inArg

            putStrLn .  mkExprHaskell $ ex
        ) in_out

