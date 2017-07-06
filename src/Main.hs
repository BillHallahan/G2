module Main where

import System.Environment

import HscTypes
import TyCon
import GHC hiding (Name, Type, exprType)

import Data.List
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
    (proj:src:entry:tail_args) <- getArgs

    let n_val = nVal tail_args
    let m_assume = mAssume tail_args
    let m_assert = mAssert tail_args

    (rtenv, reenv) <- hskToG2 proj src

    -- Inject extra information from custom "prelude"
    let tenv = M.union rtenv (M.fromList prelude_t_decls)
    let eenv = reenv

    -- putStrLn $ mkTypeEnvStr tenv
    -- putStrLn $ mkExprEnvStr eenv

    let init_state = initState tenv eenv m_assume m_assert entry

    hhp <- getZ3ProcessHandles

    in_out <- run smt2 hhp n_val init_state

    mapM_ (\(inArg, ex) -> do
            putStrLn . mkExprHaskell 
                . foldl (\a a' -> App a a') (Var entry TyBottom) $ inArg

            putStrLn .  mkExprHaskell $ ex
        ) in_out


mArg :: String -> [String] -> (String -> a) -> a -> a
mArg s args f d = case elemIndex s args of
               Nothing -> d
               Just id -> if id >= length args
                              then error ("Invalid use of " ++ s)
                              else f (args !! (id + 1))

nVal :: [String] -> Int
nVal args = mArg "--n" args read 200

mAssume :: [String] -> Maybe String
mAssume args = mArg "--assume" args Just Nothing

mAssert :: [String] -> Maybe String
mAssert args = mArg "--assert" args Just Nothing