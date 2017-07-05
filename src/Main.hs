module Main where

import System.Environment

import HscTypes
import TyCon
import GHC hiding (Name, Type, exprType)

import qualified Data.Map  as M
import qualified Data.List as L

import G2.Lib.Utils
import G2.Lib.Printers

import G2.Internals.Interface
import G2.Internals.Core
import G2.Internals.Translation
import G2.Internals.Preprocessing
import G2.Internals.Symbolic
import G2.Internals.SMT


nVal :: [String] -> Int
nVal args = case L.elemIndex "--n" args of
            Nothing -> 250
            Just id -> if id >= length args
                           then 250
                           else read (args !! (id + 1)) :: Int

mAssume :: [String] -> Maybe String
mAssume args = case L.elemIndex "--assume" args of
               Nothing -> Nothing
               Just id -> if id >= length args
                              then error "Invalid index for m_assume"
                              else Just (args !! (id + 1))

mAssert :: [String] -> Maybe String
mAssert args = case L.elemIndex "--assert" args of
               Nothing -> Nothing
               Just id -> if id >= length args
                              then error "Invalid index for m_assert"
                              else Just (args !! (id + 1))

main = do
    (proj:src:entry:tail_args) <- getArgs

    let n_val = nVal tail_args
    let m_assume = mAssume tail_args
    let m_assert = mAssert tail_args

    (rtenv, reenv) <- hskToG2 proj src

    -- Inject whatever extra information from custom "prelude"
    let tenv' = M.union rtenv (M.fromList prelude_t_decls)
    let eenv' = reenv
    let init_state = initState tenv' eenv' m_assume m_assert entry

    hhp <- getZ3ProcessHandles

    in_out <- run smt2 hhp init_state

    mapM_ (\(inArg, ex) -> do
            putStrLn . mkExprHaskell 
                . foldl (\a a' -> App a a') (Var entry TyBottom) $ inArg

            putStrLn .  mkExprHaskell $ ex
        ) in_out

