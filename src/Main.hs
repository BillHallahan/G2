module Main where

import System.Environment

import Data.List
import Data.Maybe

import G2.Lib.Printers

import G2.Internals.Interface
import G2.Internals.Language
import G2.Internals.Translation
import G2.Internals.SMT

main :: IO ()
main = do
    -- putStrLn "Compiles!!!"
    (proj:src:prims:entry:tail_args) <- getArgs

    --Get args
    let n_val = nVal tail_args
    let m_assume = mAssume tail_args
    let m_assert = mAssert tail_args
    let m_reaches = mReaches tail_args

    let m_wrapper = mWrapper tail_args
    let m_wrap_with = mWrapWith tail_args
    let m_wrap_i = mWrapperInt tail_args

    (binds, tycons) <- translation proj src prims

    let init_state = initState binds tycons m_assume m_assert m_reaches (isJust m_assert || isJust m_reaches) entry

    let init_state' = case (m_wrapper, m_wrap_with) of
                            (Just w, Just ww) -> case (findFunc w (expr_env init_state), findFunc ww (expr_env init_state)) of
                                (Left (Id n _, _), Left (wwi, _)) -> addHigherOrderWrappers init_state n wwi m_wrap_i
                                _ -> init_state
                            _ -> init_state

    hhp <- getZ3ProcessHandles

    in_out <- run smt2 hhp n_val init_state'

    -- putStrLn "----------------\n----------------"

    mapM_ (\(_, _, inArg, ex) -> do
            let funcCall = mkExprHaskell 
                         . foldl (\a a' -> App a a') (Var $ Id (Name entry Nothing 0) TyBottom) $ inArg

            -- mapM_ (print) rs
            -- putStrLn $ pprExecStateStr st

            -- print inArg
            -- print ex

            let funcOut = mkExprHaskell $ ex

            putStrLn $ funcCall ++ " = " ++ funcOut
        ) in_out

    -- putStrLn "End"
    
mArg :: String -> [String] -> (String -> a) -> a -> a
mArg s a f d = case elemIndex s a of
               Nothing -> d
               Just i -> if i >= length a
                              then error ("Invalid use of " ++ s)
                              else f (a !! (i + 1))

nVal :: [String] -> Int
nVal a = mArg "--n" a read 500

mAssume :: [String] -> Maybe String
mAssume a = mArg "--assume" a Just Nothing

mAssert :: [String] -> Maybe String
mAssert a = mArg "--assert" a Just Nothing

mReaches :: [String] -> Maybe String
mReaches a = mArg "--reaches" a Just Nothing

mWrapper :: [String] -> Maybe String
mWrapper a = mArg "--wrapper" a Just Nothing

mWrapWith :: [String] -> Maybe String
mWrapWith a = mArg "--wrap-with" a Just Nothing

mWrapperInt :: [String] -> Int
mWrapperInt a = mArg "--wrap-i" a read (-1)
