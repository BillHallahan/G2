{-# LANGUAGE BangPatterns, LambdaCase #-}

module Solver (solverTests) where

import G2.Solver

import Data.Map.Lazy as M
import Test.Tasty
import Test.Tasty.HUnit

type GetSMT smt = PrintSMT -> Int -> IO smt

solverTests :: TestTree
solverTests =
    testGroup "Solver" [
          uninterpreted1 getZ3
        , uninterpreted1 getCVC5
        ]

uninterpreted1 :: SMTConverter smt => GetSMT smt -> TestTree
uninterpreted1 = smtExpectModel
                        "Uninterpreted 1"
                        [ SetLogic ALL
                        , DeclareFun "f" [SortInt, SortInt] SortInt
                        , DeclareFun "g" [SortInt, SortInt] SortInt
                        , Assert (Func "f" [VInt 1, VInt 7] :> Func "g" [VInt 1, VInt 7])
                        , Assert (Func "g" [VInt 1, VInt 7] :> Func "f" [VInt 2, VInt 9])
                        , Assert (Func "f" [VInt 2, VInt 9] :> Func "g" [VInt 17, VInt 5]) 
                        
                        , Assert (Func "f" [VInt 6, VInt 2] := VInt 9) 
                        , Assert (Func "f" [VInt 1, VInt 2] := VInt 19)
                        , Assert (Func "f" [VInt 1, VInt 8] := VInt 22)
                        , Assert (Func "f" [VInt 22, VInt 29] := VInt 100) ]
                        [ ("f", SortFunc [SortInt, SortInt] SortInt)
                        , ("g", SortFunc [SortInt, SortInt] SortInt) ]

smtExpectModel :: SMTConverter smt => String -> [SMTHeader] -> [(SMTName, Sort)] -> GetSMT smt -> TestTree
smtExpectModel = smtSolveTest (\case SAT m -> forceModel m `seq` True; _ -> False)

smtSolveTest :: SMTConverter smt =>
                (Result SMTModel () () -> Bool)
             -> String
             -> [SMTHeader]
             -> [(SMTName, Sort)]
             -> GetSMT smt
             -> TestTree
smtSolveTest p test_name headers values get_smt =
    withResource
        (get_smt False 60)
        close
        $ \io_con -> do
            testCase test_name (do
                con <- io_con
                res <- checkSatGetModel con headers values
                assertBool "Unexpected result" $ p res)

forceModel :: SMTModel -> ()
forceModel m = go $ M.toList m
    where
        go [] = ()
        go ((!_, !_):xs) = go xs