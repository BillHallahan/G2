{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Test.Tasty
import Test.Tasty.HUnit

import GetNthTest
import PeanoTest
import LHReqs
import TestUtils
import UnionPoly

import G2.Config as G2
import G2.Interface
import G2.Language
import G2.Liquid.Config
import G2.Liquid.Helpers
import G2.Liquid.Interface
import G2.Liquid.Inference.Interface
import G2.Liquid.Inference.Config
import G2.Liquid.Inference.G2Calls
import G2.Translation

import Control.Exception
import Data.Time.Clock
import Data.Either
import qualified Data.Map.Lazy as M
import qualified Data.Text as T
import System.FilePath

import G2.Liquid.Types
import qualified System.IO as T


import Language.Haskell.Liquid.UX.CmdLine hiding (config)

-- Run with no arguments for default test cases.
-- All default test cases should pass.
-- Run with flag '--test-options="todo yes"' to run test cases corresponding to to-be-fixed bugs.
main :: IO ()
main = do
    defaultMainWithIngredients
        defaultIngredients
        tests

tests :: TestTree
tests = testGroup "All Tests"
        [ liquidTests
        , posInfTests
        , negInfTests
        , cexInfTests
        
        , unionPolyTests ]

liquidTests :: TestTree
liquidTests = testGroup "Liquid" 
    [
      checkLiquids "tests_lh/Liquid/SimpleMath.hs"
        [ ("abs2", 2000, [RForAll (\[x, y] -> isDouble x ((==) 0) && isDouble y ((==) 0)), Exactly 1])
        , ("add", 800, [RForAll (\[x, y, z] -> isInt x $ \x' -> isInt y $ \y' -> isInt z $ \z' -> x' > z' || y' > z'), AtLeast 1])
        , ("subToPos", 1000, [ RForAll (\[x, y, z] -> isInt x $ \x' -> isInt y $ \y' -> isInt z $ \z' -> x' > 0 && x' >= y' && z' <= 0), AtLeast 1])]
    , checkLiquidWithNoCutOff "tests_lh/Liquid/SimpleMath.hs" 
        [ ("fib", 4000, [RForAll (\[x, y] -> isInt x $ \x' -> isInt y $ \y' -> x' > y'), AtLeast 3])
        , ("fib'", 6000, [RForAll (\[x, y] -> isInt x $ \x' -> isInt y $ \y' -> x' > y'), AtLeast 3])
        , ("xSqPlusYSq", 1000 , [RForAll (\[x, y, z] -> isInt x $ \x' -> isInt y $ \y' -> isInt z $ \z' -> x' + y' >= z'), AtLeast 1])
        ]

    , checkLiquids "tests_lh/Liquid/SimplePoly.hs"
        [ ("snd2Int", 800, [ RForAll (\[x, y, z] -> isInt x $ \x' -> isInt y $ \y' -> isInt z $ \z' -> x' /= y' && y' == z'), Exactly 1])
        , ("sumPair", 800, [ AtLeast 1, RForAll (\[App (App _ x) y, z] -> isInt x $ \x' -> isInt y $ \y' -> isInt z $ \z' ->  x' > z' || y' > z')])
        , ("switchInt", 600, [ Exactly 1, RForAll (\[App (App _ x) _, App (App _ _) y] -> getIntB x $ \ x' -> getIntB y $ \ y' -> x' == y')]) ]

    , checkLiquids "tests_lh/Liquid/Peano.hs"
        [ ("add", 1400, [RForAll (\[x, y, _] -> x `eqIgT` zeroPeano || y `eqIgT` zeroPeano), AtLeast 5])
        , ("fromInt", 600, [RForAll (\[x, y] -> isInt x (\x' -> x' == 0)  && y `eqIgT` zeroPeano), AtLeast 1])
        ]

    , checkLiquidWithNoCutOff "tests_lh/Liquid/GetNth.hs"
        [ ("getNthInt", 2700, [AtLeast 3, RForAll getNthErrors])
        , ("getNth", 2700, [AtLeast 3]) ]
    , checkLiquidWithCutOff "tests_lh/Liquid/GetNth.hs" "sumC" 2000000 1000
        [AtLeast 3, RForAll (\[_, y] -> isInt y $ (==) 0)]
    , checkLiquidWithCutOff "tests_lh/Liquid/GetNth.hs" "sumCList" 2000000 1000 [AtLeast 3]

    , checkLiquids "tests_lh/Liquid/DataRefTest.hs"
        [ ("addMaybe", 1000, [AtLeast 1, RForAll (\[_, y, z] -> isInt y $ \y' -> appNthArgIs z (\z' -> isInt z' $ \z'' -> z'' <= y') 2)])
        , ("addMaybe2", 2000, [ AtLeast 1, RForAll (\[x, _, _] -> appNthArgIs x (\x' -> isInt x' $ \x'' -> x'' >= 0) 2)
                              , RForAll (\[_, y, z] -> isInt y $ \y' -> appNthArgIs z (\z' -> isInt z' $ \z'' -> z'' <= y') 2)])
        , ("getLeftInts", 2000, [AtLeast 1, RForAll (\[x, _] -> dcInAppHasName "Right" x 3)])
        , ("sumSameInts", 2000, [AtLeast 1, RForAll (\[x, y, _] -> dcInAppHasName "Right" x 3 && dcInAppHasName "Left" y 3)])
        , ("sub1", 1200, [AtLeast 1]) ]

    , checkLiquid "tests_lh/Liquid/NumOrd.hs" "subTuple" 1200 [AtLeast 1]

    , checkLiquids "tests_lh/Liquid/CommentMeasures.hs"
        [ ("d", 1000, [AtLeast 1])
        , ("unpackCP'", 100000, [Exactly 0])
        , ("unpackBool", 1000, [AtLeast 1, RForAll (\[_, r] -> getBoolB r (== False))])
        , ("sumSameOneOfs", 100000, [Exactly 0])
        , ("gets2As", 2000, [AtLeast 1, RExists (\[x, y, _] -> buriedDCName "B" x && buriedDCName "B" y)])
        , ("gets2As'", 1000, [AtLeast 1, RExists (\[x, y, _] -> buriedDCName "A" x && buriedDCName "B" y)
                             , RExists (\[x, y, _] -> buriedDCName "B" x && buriedDCName "A" y)])
        , ("ge4gt5", 1000, [AtLeast 1, RForAll (\[x, y] -> appNth x 1 $ \x' -> isInt x' $ \x'' -> isInt y $ \y' ->  x'' == 4 && y' == 5)])
        ]

    , checkLiquids "tests_lh/Liquid/ConcatList.hs"
        [ ("concat2", 800, [AtLeast 2])
        , ("concat3", 800, [AtLeast 2])
        , ("concat5", 1600, [AtLeast 1])]

    , checkLiquid "tests_lh/Liquid/Tests/Group3.lhs" "f" 2200 [AtLeast 1]

    , checkLiquid "tests_lh/Liquid/Nonused.hs" "g" 2000 [AtLeast 1]

    -- , checkLiquid "tests_lh/Liquid/HigherOrderRef.hs" "f1" 2000 [Exactly 0]
    -- , checkLiquid "tests_lh/Liquid/HigherOrderRef.hs" "f2" 2000 [AtLeast 4, RForAll (\[_, x, y] -> x == y)]
    -- , checkLiquid "tests_lh/Liquid/HigherOrderRef.hs" "f3" 2000 [Exactly 0]
    -- , checkLiquid "tests_lh/Liquid/HigherOrderRef.hs" "f4" 2000
    --     [AtLeast 4, RForAll (\[_, x, _] -> isInt x $ \x' -> x' == 0)]
    -- , checkLiquid "tests_lh/Liquid/HigherOrderRef.hs" "f5" 2000 [Exactly 0]
    -- , checkLiquid "tests_lh/Liquid/HigherOrderRef.hs" "f6" 2000 [AtLeast 10]
    -- , checkLiquid "tests_lh/Liquid/HigherOrderRef.hs" "f7" 2000 
    --    [AtLeast 10, RForAll (\[x, _, y] -> isInt x $ \x' -> isInt y $ \y' -> x' == y')]
    -- , checkLiquid "tests_lh/Liquid/HigherOrderRef.hs" "f8" 2000 [AtLeast 10]
    -- , checkLiquid "tests_lh/Liquid/HigherOrderRef.hs" "callf" 2000 [AtLeast 1]

    -- , checkLiquid "tests_lh/Liquid/Error/Error1.hs" "f" 600 [AtLeast 1]
    , checkLiquid "tests_lh/Liquid/Error/Error2.hs" "f1" 2000 [AtLeast 1]
    , checkLiquid "tests_lh/Liquid/ZipWith.lhs" "distance" 1000 [AtLeast 3]

    , checkLiquids "tests_lh/Liquid/HigherOrder2.hs"
        [ ("f", 2000, [Exactly 0])
        , ("h", 2000, [AtLeast 1])]
    , checkLiquid "tests_lh/Liquid/HigherOrder3.hs" "m" 600 [AtLeast 1]

    , checkLiquid "tests_lh/Liquid/Ordering.hs" "oneOrOther" 1000 [Exactly 0]

    , checkLiquid "tests_lh/Liquid/AddKV.lhs" "empty" 1000 [Exactly 0]

    , checkLiquid "tests_lh/Liquid/PropSize.hs" "prop_size" 2000 [AtLeast 1]
    , checkLiquid "tests_lh/Liquid/PropSize2.hs" "prop_size" 2000 [AtLeast 1]

    , checkLiquids "tests_lh/Liquid/WhereFuncs.lhs" [ ("f", 1000, [Exactly 0])
                                                    , ("g", 1000, [Exactly 0])]

    , checkLiquid "tests_lh/Liquid/PropConcat.lhs" "prop_concat" 1000 [AtLeast 1]

    , checkLiquid "tests_lh/Liquid/Distance.lhs" "distance" 1000 [AtLeast 1]

    -- The below test generates a LiquidHaskell error with newer LiquidHaskell versions
    -- , checkLiquid "tests_lh/Liquid/MultModules/CallZ.lhs" "callZ" 1000 [AtLeast 1]

    , checkAbsLiquid "tests_lh/Liquid/AddToEven.hs" "f" 2500
        [ AtLeast 1
        , RForAll $ \[i] r [(FuncCall { funcName = Name n _ _ _, returns = fcr }) ]
            -> n == "g"
                && isInt i (\i' -> i' `mod` 2 == 0  &&
                                    isInt r (\r' -> isInt fcr (\fcr' -> r' == i' + fcr')))]
    , checkAbsLiquid "tests_lh/Liquid/AddToEven4.hs" "f" 2000 [ AtLeast 1]

    , checkAbsLiquid "tests_lh/Liquid/Concat.hs" "prop_concat" 1000 [ AtLeast 1]

    , checkLiquids "tests_lh/Liquid/ListTests.lhs"
        [ ("r", 1000, [Exactly 0])
        , ("prop_map", 1500, [AtLeast 3])
        , ("prop_concat_1", 1500, [AtLeast 1])
        ]
    , checkAbsLiquid "tests_lh/Liquid/ListTests2.lhs" "prop_map" 2000
        [ AtLeast 2
        , RForAll (\_ _ [(FuncCall { funcName = Name n _ _ _ }) ] -> n == "map") ]
    , checkAbsLiquid "tests_lh/Liquid/ListTests2.lhs" "prop_size" 2000
        [ AtLeast 1
        , RForAll (\[] _ [(FuncCall { funcName = Name n _ _ _, returns = r }) ]
            -> n == "length2" && getIntB r (/= 3)) ]

    , checkLiquid "tests_lh/Liquid/MapReduceTest2.lhs" "mapReduce" 1500 [AtLeast 1]

    -- The below test generates a LiquidHaskell error with LiquidHaskell 8.2.2 version
    -- , checkLiquid "tests_lh/Liquid/MeasErr.hs" "f" 1500 [Exactly 0]

    , checkAbsLiquid "tests_lh/Liquid/PropRep.hs" "prop_rep" 2000
        [ AtLeast 1 ]

    , checkAbsLiquid "tests_lh/Liquid/Replicate.hs" "replicate" 2000
        [ AtLeast 1
        , RExists (\_ _ [(FuncCall { funcName = Name n _ _ _ }) ] -> n == "foldl") ]
    , checkAbsLiquid "tests_lh/Liquid/Replicate.hs" "r" 2000
        [ AtLeast 1
        , RExists (\_ _ [(FuncCall { funcName = Name n _ _ _ }) ] -> n == "foldl") ]

    , checkAbsLiquid "tests_lh/Liquid/AbsTypeClass.hs" "callF" 1000
        [ AtLeast 1
        , RExists (\_ _ [(FuncCall { funcName = Name n _ _ _ }) ] -> n == "f") ]
    , checkAbsLiquid "tests_lh/Liquid/AbsTypeClassVerified.hs" "callF" 10000 [ Exactly 0 ]

    , checkLiquid "tests_lh/Liquid/Tree.hs" "sumPosTree" 1000 [AtLeast 1]
    , checkLiquid "tests_lh/Liquid/Error4.hs" "extractRights" 1000 [AtLeast 1]
    , checkLiquid "tests_lh/Liquid/PostFalse.hs" "f" 2000 [AtLeast 1]

    , checkLiquid "tests_lh/Liquid/TypeSym.hs" "f" 500 []

    , checkLiquid "tests_lh/Liquid/CorrectDict.hs" "f" 2000 [AtLeast 1]

    , checkAbsLiquid "tests_lh/Liquid/ZipWith3.hs" "prop_zipWith" 400 [ AtLeast 3]

    , checkAbsLiquid "tests_lh/Liquid/Length.hs" "prop_size" 1000
        [ AtLeast 1
        , RForAll (\_ _ [ _ ]  -> True)]

    , checkLiquidWithConfig "tests_lh/Liquid/NestedLength.hs" [("nested", 1000, [AtLeast 1])]
                            mkConfigTestIO
                            (return $ (mkLHConfigDirect [] M.empty) { add_tyvars = True })
    , checkLiquidWithConfig "tests_lh/Liquid/AddTyVars.hs"
                            [ ("f", 400, [AtLeast 1])
                            , ("g", 400, [AtLeast 1])
                            , ("h", 400, [AtLeast 1])]
                            mkConfigTestIO
                            (return $ (mkLHConfigDirect [] M.empty) { add_tyvars = True })

    , checkLiquid "tests_lh/Liquid/Polymorphism/Poly1.hs" "f" 1000 [Exactly 0]
    , checkLiquid "tests_lh/Liquid/Polymorphism/Poly2.hs" "f" 600 [Exactly 0]

    , checkLiquid "tests_lh/Liquid/Sets/Sets1.hs" "prop_union_assoc" 2000 [AtLeast 2]
    , checkLiquid "tests_lh/Liquid/Sets/Sets1.hs" "prop_intersection_comm" 1000 [AtLeast 5]
    , checkLiquid "tests_lh/Liquid/Sets/Sets2.hs" "badIdList" 1000 [AtLeast 1]
    , checkLiquid "tests_lh/Liquid/Sets/Sets2.hs" "append" 1000 [AtLeast 1]
    , checkLiquid "tests_lh/Liquid/Sets/Sets3.hs" "filter" 1800 [AtLeast 1]
    , checkLiquid "tests_lh/Liquid/Sets/Sets4.hs" "isin" 1000 [AtLeast 1]
    , checkLiquid "tests_lh/Liquid/Sets/Sets5.hs" "f" 1000 [AtLeast 1]
    , checkLiquid "tests_lh/Liquid/Sets/Sets6.hs" "f" 2000 [AtLeast 1]
    , checkLiquid "tests_lh/Liquid/Sets/Sets7.hs" "insertSort" 3000 [AtLeast 1]

    -- Higher Order Functions
    , checkLiquid "tests_lh/Liquid/HigherOrder/IntFuncArg.hs" "caller" 1000 [AtLeast 1]
    , checkLiquid "tests_lh/Liquid/HigherOrder/HigherOrderPre.hs" "test" 1000 [AtLeast 1]
    , checkLiquid "tests_lh/Liquid/HigherOrder/HigherOrder2.hs" "f" 2000 [Exactly 0]

    -- IO
    , checkLiquid "tests_lh/Liquid/IO/IO1.hs" "f" 1000 [Exactly 0]
    , checkLiquid "tests_lh/Liquid/IO/IO2.hs" "f" 1000 [AtLeast 1]
    , checkLiquid "tests_lh/Liquid/IO/IO3.hs" "f" 1400 [AtLeast 1]

    -- Abstract counterexamples
    , checkAbsLiquid "tests_lh/Liquid/Polymorphism/Poly3.hs" "f" 800
        [ AtLeast 4
        , RForAll (\_ _ [ FuncCall { funcName = Name n _ _ _} ]  -> n == "fil")]
    , checkLiquid "tests_lh/Liquid/Polymorphism/Poly4.hs" "f" 600 [Exactly 0]
    , checkAbsLiquid "tests_lh/Liquid/Polymorphism/Poly5.hs" "call" 600 [AtLeast 1]
    , checkAbsLiquid "tests_lh/Liquid/Polymorphism/Poly6.hs" "f" 1000
        [ AtLeast 1
        , RForAll (\_ _ [ FuncCall { returns = r } ] ->
                    case r of { Prim Undefined _-> False; _ -> True})
        ]
    , checkAbsLiquid "tests_lh/Liquid/Polymorphism/Poly7.hs" "prop_f" 2000 [AtLeast 1]
    , checkAbsLiquid "tests_lh/Liquid/Polymorphism/Poly8.hs" "prop" 2000
        [ AtLeast 1
        , RForAll (\_ _ [ FuncCall { funcName = Name n _ _ _ } ] -> n == "func")]
    , checkAbsLiquid "tests_lh/Liquid/Polymorphism/Poly9.hs" "prop" 2000
        [ AtLeast 1
        , RForAll (\_ _ [ FuncCall { funcName = Name n _ _ _ } ] -> n == "func")]
    , checkAbsLiquid "tests_lh/Liquid/Polymorphism/Poly10.hs" "prop" 2000
        [ AtLeast 1 ]
    , checkAbsLiquid "tests_lh/Liquid/Polymorphism/Poly11.hs" "call" 700
        [ AtLeast 1
        , RForAll (\_ _ [ FuncCall { funcName = Name n _ _ _ } ] -> n == "higher")]
    , checkAbsLiquid "tests_lh/Liquid/Polymorphism/Poly12.hs" "prop" 3000
        [ AtLeast 1
        , RForAll (\_ _ [ FuncCall { funcName = Name n _ _ _ } ] -> n == "map")]
    , checkAbsLiquid "tests_lh/Liquid/Polymorphism/Poly13.hs" "call" 1000
        [ AtLeast 1
        , RForAll (\_ _ [ FuncCall { funcName = Name n _ _ _ } ] -> n == "f")]
    , checkAbsLiquid "tests_lh/Liquid/Polymorphism/Poly14.hs" "initCall" 1000 [ AtLeast 1]
    , checkAbsLiquid "tests_lh/Liquid/Polymorphism/Poly15.hs" "call" 1000 [ AtLeast 1]
    , checkAbsLiquid "tests_lh/Liquid/Polymorphism/Poly16.hs" "call" 1000 
        [ AtLeast 1
        , RForAll (\ _ _ [ FuncCall { arguments = [_, _, ar] } ] -> case ar of Prim _ _ -> False; _ -> True )]
    , checkAbsLiquid "tests_lh/Liquid/Polymorphism/Poly17.hs" "empty2" 1000 [ AtLeast 1]
    , checkAbsLiquid "tests_lh/Liquid/Polymorphism/Poly18.hs" "f" 500 [ AtLeast 1]
    ]

posInfTests :: TestTree
posInfTests = testGroup "Tests"
            [ posTestInference "tests_lh/test_files/Pos/HigherOrder.hs"
            , posTestInference "tests_lh/test_files/Pos/HigherOrder2.hs"
            -- , posTestInferenceWithTimeOut 240 5 "tests_lh/test_files/Pos/HigherOrder3.hs"
            -- , posTestInference "tests_lh/test_files/Pos/HigherOrder4.hs"

            , posTestInference "tests_lh/test_files/Pos/Test1.hs" 
            , posTestInference "tests_lh/test_files/Pos/Test2.hs"
            , posTestInference "tests_lh/test_files/Pos/Test3.hs"
            , posTestInference "tests_lh/test_files/Pos/Test4.hs"
            , posTestInference "tests_lh/test_files/Pos/Test5.hs"
            , posTestInference "tests_lh/test_files/Pos/Test6.hs"
            , posTestInference "tests_lh/test_files/Pos/Test7.hs"
            , posTestInference "tests_lh/test_files/Pos/Test8.hs"
            , posTestInference "tests_lh/test_files/Pos/Test9.hs"
            , posTestInference "tests_lh/test_files/Pos/Test10.hs"
            , posTestInference "tests_lh/test_files/Pos/Test11.hs"
            , posTestInference "tests_lh/test_files/Pos/Test12.hs"
            , posTestInference "tests_lh/test_files/Pos/Test13.hs"
            , posTestInference "tests_lh/test_files/Pos/Test14.hs"
            , posTestInference "tests_lh/test_files/Pos/Test15.hs"
            , posTestInference "tests_lh/test_files/Pos/Test16.hs"
            , posTestInference "tests_lh/test_files/Pos/Test17.hs"
            , posTestInference "tests_lh/test_files/Pos/Test18.hs"
            , posTestInference "tests_lh/test_files/Pos/Test19.hs"
            , posTestInference "tests_lh/test_files/Pos/Test20.hs"
            , posTestInference "tests_lh/test_files/Pos/Test21.hs"
            , posTestInference "tests_lh/test_files/Pos/Test22.hs"
            -- , posTestInference "tests_lh/test_files/Pos/Test23.hs"
            , posTestInference "tests_lh/test_files/Pos/Test24.hs"
            , posTestInference "tests_lh/test_files/Pos/Test25.hs"
            , posTestInference "tests_lh/test_files/Pos/Test26.hs"
            , posTestInference "tests_lh/test_files/Pos/Test27.hs"
            , posTestInference "tests_lh/test_files/Pos/Test28.hs"
            , posTestInference "tests_lh/test_files/Pos/Test29.hs"
            , posTestInference "tests_lh/test_files/Pos/Test30.hs"
            , posTestInference "tests_lh/test_files/Pos/Test31.hs"
            , posTestInference "tests_lh/test_files/Pos/Test32.hs"
            , posTestInference "tests_lh/test_files/Pos/Test33.hs"
            , posTestInference "tests_lh/test_files/Pos/Test34.hs"
            , posTestInference "tests_lh/test_files/Pos/Test35.hs"
            , posTestInference "tests_lh/test_files/Pos/Test36.hs"
            , posTestInference "tests_lh/test_files/Pos/Test37.hs"
            -- , posTestInferenceWithTimeOut 240 15 "tests_lh/test_files/Pos/Test38.hs"
            , posTestInference "tests_lh/test_files/Pos/Test39.hs"
            , posTestInference "tests_lh/test_files/Pos/Test40.hs"
            , posTestInference "tests_lh/test_files/Pos/Test41.hs"
            , posTestInference "tests_lh/test_files/Pos/Test42.hs"
            , posTestInference "tests_lh/test_files/Pos/Test43.hs"
            , posTestInference "tests_lh/test_files/Pos/Test44.hs"
            , posTestInference "tests_lh/test_files/Pos/Test45.hs"
            , posTestInference "tests_lh/test_files/Pos/Test46.hs"
            , posTestInference "tests_lh/test_files/Pos/Test47.hs"
            , posTestInference "tests_lh/test_files/Pos/Test48.hs"
            , posTestInference "tests_lh/test_files/Pos/Test49.hs"
            , posTestInference "tests_lh/test_files/Pos/Test50.hs"

            , posTestInference "tests_lh/test_files/Pos/Sets1.hs"
            , posTestInference "tests_lh/test_files/Pos/Sets2.hs"
            , posTestInference "tests_lh/test_files/Pos/Sets3.hs"
            , posTestInference "tests_lh/test_files/Pos/Sets4.hs"
            , posTestInference "tests_lh/test_files/Pos/Sets5.hs"
            , posTestInference "tests_lh/test_files/Pos/Sets6.hs"
            , posTestInference "tests_lh/test_files/Pos/Sets7.hs"
            , posTestInference "tests_lh/test_files/Pos/Sets8.hs"
            , posTestInference "tests_lh/test_files/Pos/Sets9.hs"
            -- , posTestInference "tests_lh/test_files/Pos/Sets10.hs"

            , posTestInference "tests_lh/test_files/Pos/MeasComp1.hs" 
            , posTestInference "tests_lh/test_files/Pos/MeasComp2.hs"
            , posTestInference "tests_lh/test_files/Pos/MeasComp3.hs"  ]

negInfTests :: TestTree
negInfTests = testGroup "Tests"
            [ negTestInference "tests_lh/test_files/Neg/Test1.hs"
            , negTestInference "tests_lh/test_files/Neg/Test2.hs"
            , negTestInference "tests_lh/test_files/Neg/Test3.hs"
            , negTestInference "tests_lh/test_files/Neg/Test4.hs"
            , negTestInference "tests_lh/test_files/Neg/Test5.hs"
            , negTestInference "tests_lh/test_files/Neg/Test6.hs" ]

cexInfTests :: TestTree
cexInfTests = testGroup "Tests"
            [ cexTest "tests_lh/test_files/CEx/CEx1.hs" "zipWith"
            , cexTest "tests_lh/test_files/CEx/CEx2.hs" "mapReduce" ]

todoTests :: TestTree
todoTests = testGroup "To Do"
    [
      checkLiquid "tests_lh/Liquid/TyApps.hs" "goodGet" 1000 [Exactly 0]
    , checkLiquid "tests_lh/Liquid/TyApps.hs" "getPosInt" 1000
        [ AtLeast 1
        , RForAll (\[_, _, (App _ x), y] -> getIntB x $ \x' -> getIntB y $ \y' -> x' == y' && y' == 10)]
    , checkLiquid "tests_lh/Liquid/TyApps.hs" "getPos" 1000
        [ AtLeast 1
        , RExists (\[_, _, (App _ x), y] -> getIntB x $ \x' -> getIntB y $ \y' -> x' == y' && y' == 10)]
    , checkLiquid "tests_lh/Liquid/FoldrTests.hs" "max2" 1000 [Exactly 0]
    , checkLiquid "tests_lh/Liquid/FoldrTests.hs" "max3" 1000 [Exactly 0]
    , checkLiquid "tests_lh/Liquid/SimpleAnnot.hs" "simpleF" 1000 [Exactly 0]
    , checkLiquid "tests_lh/Liquid/Ordering.hs" "lt" 1000 [AtLeast 1]
    , checkLiquid "tests_lh/Liquid/Ordering.hs" "gt" 1000 [AtLeast 1]
    , checkLiquid "tests_lh/Liquid/WhereFuncs2.hs" "hCalls" 1000 [AtLeast 1]
    , checkLiquid "tests_lh/Liquid/WhereFuncs2.hs" "i" 1000 [AtLeast 1]
    , checkAbsLiquid "tests_lh/Liquid/AddToEvenWhere.hs" "f" 2000
        [ AtLeast 1
        , RForAll (\[i] r [(FuncCall { funcName = Name n _ _ _, returns = r' }) ]
                        -> n == "g" && isInt i (\i' -> i' `mod` 2 == 0) && r == r' )]
    , checkLiquid "tests_lh/Liquid/ListTests.lhs" "concat" 1000 [AtLeast 3]
    , checkLiquid "tests_lh/Liquid/MapReduceTest.lhs" "mapReduce" 1500
        [Exactly 0]
    , checkLiquid "tests_lh/Liquid/NearestTest.lhs" "nearest" 1500 [Exactly 1]

    , checkAbsLiquid "tests_lh/Liquid/ListTests2.lhs" "replicate" 2000
        [ AtLeast 3
        , RForAll (\[_, nA, aA] _ [(FuncCall { funcName = Name n _ _ _, arguments = [_, _, nA', aA'] }) ]
            -> n == "replicate" && nA == nA' && aA == aA') ]
    ]
-------------------------------------------------
-- CEx Gen tests
-------------------------------------------------

checkLiquidWithNoCutOff :: FilePath -> [(String, Int, [Reqs ([Expr] -> Bool)])] -> TestTree
checkLiquidWithNoCutOff fp tests = do
    let lhconfig = mkLHConfigDirect [] M.empty
    checkLiquidWithConfig fp tests
        mkConfigTestIO
        (return lhconfig { cut_off = maximum $ map (\(_, stps, _) -> stps) tests })

checkLiquid :: FilePath -> String -> Int -> [Reqs ([Expr] -> Bool)] -> TestTree
checkLiquid fp entry stps req = do
    let lhconfig = mkLHConfigDirect [] M.empty
    checkLiquidWithConfig  fp [(entry, stps, req)]
        mkConfigTestIO
        (return lhconfig)

checkLiquids :: FilePath -> [(String, Int, [Reqs ([Expr] -> Bool)])] -> TestTree
checkLiquids fp tests = do
    let lhconfig = mkLHConfigDirect [] M.empty
    checkLiquidWithConfig  fp tests
        mkConfigTestIO
        (return lhconfig)


checkLiquidWithSet :: FilePath -> [(String, Int, [Reqs ([Expr] -> Bool)])] -> TestTree
checkLiquidWithSet fp tests = do
    let lhconfig = mkLHConfigDirect [] M.empty
    checkLiquidWithConfig fp tests
        mkConfigTestWithSetIO
        (return lhconfig)

checkLiquidWithCutOff :: FilePath -> String -> Int -> Int -> [Reqs ([Expr] -> Bool)] -> TestTree
checkLiquidWithCutOff fp entry stps co reqList = do
    let lhconfig = mkLHConfigDirect [] M.empty
    checkLiquidWithConfig fp [(entry, stps, reqList)]
        mkConfigTestIO
        (return lhconfig { cut_off = co })

checkLiquidWithMap :: FilePath -> [(String, Int, [Reqs ([Expr] -> Bool)])] -> TestTree
checkLiquidWithMap fp tests = do
    let lhconfig = mkLHConfigDirect [] M.empty
    checkLiquidWithConfig fp tests
        mkConfigTestWithMapIO
        (return lhconfig)

checkLiquidWithConfig :: FilePath -> [(String, Int, [Reqs ([Expr] -> Bool)])] -> IO Config -> IO LHConfig -> TestTree
checkLiquidWithConfig fp tests config_f lhconfig_f =
    withResource
        (do
            config <- config_f
            g2_lh_config <- lhconfig_f

            lh_config <- getOpts []

            let config' = config { mode = Liquid }
            let proj = takeDirectory fp

            ghci <- try $ getGHCInfos lh_config [proj] [fp] :: IO (Either SomeException [GhcInfo])
            
            let ghci' = case ghci of
                        Right g_c -> g_c
                        Left e -> error $ "ERROR OCCURRED IN LIQUIDHASKELL\n" ++ show e

            tgt_trans <- translateLoaded [proj] [fp] (simplTranslationConfig { simpl = False }) config'

            return (tgt_trans, ghci', config', g2_lh_config)
        )
        (\_ -> return ())
        $ \loaded ->
                testGroup
                fp
                $ map (\(entry, stps, reqList) ->
                        testCase (fp ++ " " ++ entry) (do
                            (tgt_trans, ghci, config, lh_config) <- loaded
                            let config' = config { steps = stps }
                            res <- doTimeout (timeLimit config)
                                        $ (try (return . fst. fst =<< runLHCore (T.pack entry) tgt_trans ghci config' lh_config)
                                                                                :: IO (Either SomeException [ExecRes AbstractedInfo]))
 
                            let (ch, r) = case res of
                                        Nothing -> (False, Right [Time])
                                        Just (Left e) -> (False, Left e)
                                        Just (Right exprs) ->
                                            let
                                                r_ = checkExprGen
                                                        (map (\(ExecRes { conc_args = inp, conc_out = out}) -> inp ++ [out]) exprs)
                                                        reqList
                                            in
                                            (null r_, Right r_)

                            assertBool ("Liquid test for file " ++ fp ++ 
                                        " with function " ++ entry ++ " failed.\n" ++ show r) ch
                        )
                    ) tests

checkAbsLiquid :: FilePath -> String -> Int -> [Reqs ([Expr] -> Expr -> [FuncCall] -> Bool)] -> TestTree
checkAbsLiquid fp entry stps reqList = do
    let lhconfig = mkLHConfigDirect [] M.empty
    checkAbsLiquidWithConfig fp entry reqList
        (do config <- mkConfigTestIO
            return $ config {steps = stps} )
        (return lhconfig)

checkAbsLiquidWithConfig :: FilePath
                         -> String
                         -> [Reqs ([Expr]
                         -> Expr
                         -> [FuncCall]
                         -> Bool)]
                         -> IO Config
                         -> IO LHConfig
                         -> TestTree
checkAbsLiquidWithConfig fp entry reqList config_f lhconfig_f = do
    testCase fp (do
        config <- config_f
        lhconfig <- lhconfig_f
        res <- findCounterExamples' fp (T.pack entry) config lhconfig

        let (ch, r) = case res of
                    Nothing -> (False, Right [])
                    Just (Left e) -> (False, Left e)
                    Just (Right exprs) ->
                        let
                            te = checkAbsLHExprGen
                                    (map (\(ExecRes { final_state = s, conc_args = inp, conc_out = out})
                                            -> (s, inp, out)
                                         ) exprs
                                    ) reqList
                        in
                        (null te, Right te)

        assertBool ("Liquid test for file " ++ fp ++ 
                    " with function " ++ entry ++ " failed.\n" ++ show r) ch
        )

findCounterExamples' :: FilePath
                     -> T.Text
                     -> Config
                     -> LHConfig
                     -> IO (Maybe (Either SomeException [ExecRes AbstractedInfo]))
findCounterExamples' fp entry config lhconfig =
    let
        proj = takeDirectory fp
    in
    doTimeout (timeLimit config)
        $ try (return . fst. fst =<< findCounterExamples [proj] [fp] entry config lhconfig)

-------------------------------------------------
-- Inference tests
-------------------------------------------------

posTestInferenceWithTimeOut :: Int -> NominalDiffTime -> FilePath -> TestTree
posTestInferenceWithTimeOut to to_se fp = do
    testCase ("Inference " ++ fp) (do
        config <- G2.getConfigDirect
        let infconfig = (mkInferenceConfigDirect []) { timeout_se = to_se }
        let lhconfig = mkLHConfigDirect [] M.empty
        res <- doTimeout to $ inferenceCheck infconfig config lhconfig [] [fp]

        assertBool ("Inference for " ++ fp ++ " failed.") $ maybe False (isRight . snd) res
        )

posTestInference :: FilePath -> TestTree
posTestInference = posTestInferenceWithTimeOut 120 5

negTestInference :: FilePath -> TestTree
negTestInference fp = do
    testCase ("Inference " ++ fp) (do
        config <- G2.getConfigDirect
        let infconfig = mkInferenceConfigDirect []
        let lhconfig = mkLHConfigDirect [] M.empty
        res <- doTimeout 90 $ inferenceCheck infconfig config lhconfig [] [fp]

        assertBool ("Inference for " ++ fp ++ " failed.") $ maybe False (isLeft . snd) res
        )

cexTest :: FilePath -> String -> TestTree
cexTest fp func =
    testCase ("Inference " ++ fp) (do
        config <- G2.getConfigDirect
        let infconfig = (mkInferenceConfigDirect []) { timeout_se = 10 }
        let lhconfig = mkLHConfigDirect [] M.empty
        res <- doTimeout 25 $ runLHInferenceAll infconfig config lhconfig (T.pack func) [] [fp]
        assertBool ("Counterexample generation for " ++ func ++ " in " ++ fp ++ " failed.") $ maybe False (not . null . fst) res
        )
