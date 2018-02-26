{-# LANGUAGE OverloadedStrings #-}
module InputOutputTest where

import Test.Tasty
import Test.Tasty.HUnit

import Control.Exception
import qualified Data.Text as T

import G2.Internals.Config
import G2.Internals.Execution
import G2.Internals.Interface
import G2.Internals.Language
import G2.Internals.Translation
import G2.Internals.Solver
import G2.Lib.Printers

import Reqs

checkInputOutput :: FilePath -> FilePath -> String -> String -> Int -> Int -> [Reqs] ->  IO TestTree
checkInputOutput proj src md entry stps i req = checkInputOutputWithConfig proj src md entry i req (mkConfigDef {steps = stps})

checkInputOutputWithConfig :: FilePath -> FilePath -> String -> String -> Int -> [Reqs] -> Config -> IO TestTree
checkInputOutputWithConfig proj src md entry i req config = do
    r <- checkInputOutput' proj src md entry i req config

    let b = case r of
            Left _ -> False
            Right b' -> b'

    return . testCase src $ assertBool ("Input/Output for file " ++ show src ++ " failed on function " ++ entry ++ ".") b 

checkInputOutput' :: FilePath -> FilePath -> String -> String -> Int -> [Reqs] -> Config -> IO (Either SomeException Bool)
checkInputOutput' proj src md entry i req config = try (checkInputOutput'' proj src md entry i req config)

checkInputOutput'' :: FilePath -> FilePath -> String -> String -> Int -> [Reqs] -> Config -> IO Bool
checkInputOutput'' proj src md entry i req config = do
    (mb_modname, binds, tycons, cls, _) <- translateLoaded proj src [] False config

    let init_state = initState binds tycons cls Nothing Nothing Nothing False (T.pack entry) mb_modname
    let halter_set_state = init_state {halter = steps config}
    
    (con, hhp) <- getSMT config

    r <- run stdReduce halterIsZero halterSub1 executeNext con hhp config halter_set_state
    mr <- validate proj src md entry r
    let io = map (\(_, i, o, _) -> i ++ [o]) r

    let chEx = checkExprGen io i req
    return $ mr && chEx