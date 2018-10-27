{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Test.Tasty
import Test.Tasty.HUnit

import G2.Internals.Config.Config

import G2.Internals.Execution
import G2.Internals.Interface
import G2.Internals.Language as G2
import G2.Internals.Translation
import G2.Internals.Solver
import G2.Internals.Liquid.Interface

import Control.Exception
import Data.Maybe
import qualified Data.Text as T

import PeanoTest
import HigherOrderMathTest
import GetNthTest
import DefuncTest
import CaseTest
import Expr
import Typing

import InputOutputTest
import Reqs
import TestUtils

main :: IO ()
main = defaultMain
       =<< tests

tests :: IO TestTree
tests = return . testGroup "Tests"
    =<< sequence [
          sampleTests
        , liquidTests
        , testFileTests
        , baseTests
        , primTests
        , exprTests
        , typingTests
        ]

timeout :: Timeout
timeout = mkTimeout 1

-- Test based on examples that are also good for demos
sampleTests :: IO TestTree
sampleTests =
    return . testGroup "Samples"
        =<< sequence [
                  checkExpr "tests/Samples/" "tests/Samples/Peano.hs" 900 Nothing (Just "equalsFour") "add" 3 [RForAll $ not . peano_4_out, AtLeast 10]
                , checkExpr "tests/Samples/" "tests/Samples/Peano.hs" 900 (Just "fstIsEvenAddToFour") (Just "fstIsTwo") "add" 3 [RExists peano_0_4, RExists peano_4_0, Exactly 2]
                , checkExpr "tests/Samples/" "tests/Samples/Peano.hs" 1200 (Just "multiplyToFour") (Just "equalsFour") "add" 3 [RExists peano_1_4_5, RExists peano_4_1_5, Exactly 2]
                , checkExpr "tests/Samples/" "tests/Samples/Peano.hs" 750 (Just "eqEachOtherAndAddTo4") Nothing "add" 3 [RForAll peano_2_2, Exactly 1]
                , checkExpr "tests/Samples/" "tests/Samples/Peano.hs" 600 (Just "equalsFour") Nothing "add" 3 [RExists peano_0_4, RExists peano_1_3, RExists peano_2_2, RExists peano_3_1, RExists peano_4_0, Exactly 5]
                , checkExpr "tests/Samples/" "tests/Samples/Peano.hs" 750 (Just "equalsFour") Nothing "multiply" 3 [RExists peano_1_4, RExists peano_2_2, RExists peano_4_1, Exactly 3]

                , checkExpr "tests/Samples/" "tests/Samples/HigherOrderMath.hs" 800 (Just "isTrue0") Nothing "notNegativeAt0NegativeAt1" 2 [RExists negativeSquareRes, AtLeast 1]
                , checkExpr "tests/Samples/" "tests/Samples/HigherOrderMath.hs" 600 (Just "isTrue1") Nothing "fixed" 3 [RExists abs2NonNeg, RExists squareRes, RExists fourthPowerRes, RForAll allabs2NonNeg, AtLeast 4]
                , checkExpr "tests/Samples/" "tests/Samples/HigherOrderMath.hs" 600 Nothing Nothing "fixed" 3 [RExists abs2NonNeg, RExists squareRes, RExists fourthPowerRes, AtLeast 4]
                , checkExpr "tests/Samples/" "tests/Samples/HigherOrderMath.hs" 600 (Just "isTrue2") Nothing "sameFloatArgLarger" 3 [RExists addRes, RExists subRes, AtLeast 2]
                , checkExpr "tests/Samples/" "tests/Samples/HigherOrderMath.hs" 600 Nothing Nothing "functionSatisfies" 4 [RExists functionSatisfiesRes, AtLeast 1]
                , checkExpr "tests/Samples/" "tests/Samples/HigherOrderMath.hs" 1000 Nothing Nothing "approxSqrt" 3 [AtLeast 2]
                -- The below test fails because Z3 returns unknown.
                -- , checkExpr "tests/Samples/" "tests/Samples/HigherOrderMath.hs" 1200 (Just "isTrue2") Nothing "sameFloatArgLarger" 2 [RExists approxSqrtRes, RExists pythagoreanRes, AtLeast 2]
                
                , checkExpr "tests/Samples/" "tests/Samples/McCarthy91.hs" 1000 (Just "lessThan91") Nothing "mccarthy" 2 [RForAll (\[App _ (Lit (LitInt x)), _] -> x <= 100), AtLeast 1]
                , checkExpr "tests/Samples/" "tests/Samples/McCarthy91.hs" 400 (Just "greaterThan10Less") Nothing "mccarthy" 2 [RForAll (\[App _ (Lit (LitInt x)), _] -> x > 100), AtLeast 1]
                , checkExpr "tests/Samples/" "tests/Samples/McCarthy91.hs" 1000 (Just "lessThanNot91") Nothing "mccarthy" 2 [Exactly 0]
                , checkExpr "tests/Samples/" "tests/Samples/McCarthy91.hs" 1000 (Just "greaterThanNot10Less") Nothing "mccarthy" 2 [Exactly 0]

                , checkExpr "tests/Samples/" "tests/Samples/GetNth.hs" 600 Nothing Nothing "getNth" 3 [AtLeast 10, RForAll getNthTest]
                , checkExpr "tests/Samples/" "tests/Samples/GetNthPoly.hs" 600 Nothing Nothing "getNthInt" 3 [AtLeast 10, RForAll getNthErrTest]
                , checkExpr "tests/Samples/" "tests/Samples/GetNthPoly.hs" 600 Nothing Nothing "getNthX" 3 [AtLeast 10, RForAll getNthErrGenTest]
                , checkExpr "tests/Samples/" "tests/Samples/GetNthPoly.hs" 600 Nothing Nothing "getNthPeano" 3 [AtLeast 10, RForAll getNthErrGenTest] -- 533
                , checkExpr "tests/Samples/" "tests/Samples/GetNthPoly.hs" 600 Nothing Nothing "getNthCListInt" 3 [AtLeast 10, RForAll getNthErrGenTest2']
                , checkExpr "tests/Samples/" "tests/Samples/GetNthPoly.hs" 600 Nothing Nothing "getNthCListX" 3 [AtLeast 10, RForAll getNthErrGenTest2]
                , checkExpr "tests/Samples/" "tests/Samples/GetNthPoly.hs" 1000 Nothing Nothing "getNth" 4 [AtLeast 10]

                , checkExpr "tests/Samples/" "tests/Samples/GetNthPoly.hs" 1000 Nothing Nothing "cfmapInt" 3 [AtLeast 10, RForAll cfmapTest]
                , checkExpr "tests/Samples/" "tests/Samples/GetNthPoly.hs" 1600 Nothing Nothing "cfmapIntX" 3 [AtLeast 10, RForAll cfmapTest]
                , checkExpr "tests/Samples/" "tests/Samples/GetNthPoly.hs" 800 Nothing Nothing "cfmapIntCListInt" 3 [AtLeast 3, RForAll cfmapTest]

                , checkExprReaches "tests/Samples/" "tests/Samples/GetNthErr.hs" 800 Nothing Nothing (Just "error") "getNth" 3 [AtLeast 8, RForAll errors]

                , checkExpr "tests/Samples/" "tests/Samples/FoldlUses.hs" 1600 Nothing Nothing "sum" 2 [AtLeast 3]
                , checkExpr "tests/Samples/" "tests/Samples/FoldlUses.hs" 1000 Nothing Nothing "dotProd" 3 [AtLeast 3]

                , checkExpr "tests/Samples/" "tests/Samples/FoldlUsesPoly.hs" 600 Nothing Nothing "sumMinAndMax" 5 [AtLeast 10]
                , checkExpr "tests/Samples/" "tests/Samples/FoldlUsesPoly.hs" 400 Nothing Nothing "maxes" 7 [AtLeast 10]
                , checkExpr "tests/Samples/" "tests/Samples/FoldlUsesPoly.hs" 400 Nothing Nothing "switchInt" 2 [AtLeast 1]
                , checkExpr "tests/Samples/" "tests/Samples/FoldlUsesPoly.hs" 400 Nothing Nothing "getInInt" 2 [AtLeast 1]
                , checkExpr "tests/Samples/" "tests/Samples/FoldlUsesPoly.hs" 400 Nothing Nothing "switchP" 6 [AtLeast 1]
        ]

liquidTests :: IO TestTree
liquidTests = 
    return . testGroup "Liquid"
        =<< sequence [
                  checkLiquid "tests/Liquid" "tests/Liquid/SimpleMath.hs" "abs2" 2000 2 [RForAll (\[x, y] -> isDouble x ((==) 0) && isDouble y ((==) 0)), Exactly 1]
                , checkLiquid "tests/Liquid" "tests/Liquid/SimpleMath.hs" "add" 800 3 
                    [RForAll (\[x, y, z] -> isInt x $ \x' -> isInt y $ \y' -> isInt z $ \z' -> x' > z' || y' > z'), AtLeast 1]
                , checkLiquid "tests/Liquid" "tests/Liquid/SimpleMath.hs" "subToPos" 1000 3 
                    [RForAll (\[x, y, z] -> isInt x $ \x' -> isInt y $ \y' -> isInt z $ \z' -> x' > 0 && x' >= y' && z' <= 0), AtLeast 1]
                , checkLiquid "tests/Liquid" "tests/Liquid/SimpleMath.hs" "fib" 4000 2 [RForAll (\[x, y] -> isInt x $ \x' -> isInt y $ \y' -> x' > y'), AtLeast 3]
                , checkLiquid "tests/Liquid" "tests/Liquid/SimpleMath.hs" "fib'" 6000 2 [RForAll (\[x, y] -> isInt x $ \x' -> isInt y $ \y' -> x' > y'), AtLeast 3]
                , checkLiquid "tests/Liquid" "tests/Liquid/SimpleMath.hs" "xSqPlusYSq" 1000 3 
                    [RForAll (\[x, y, z] -> isInt x $ \x' -> isInt y $ \y' -> isInt z $ \z' -> x' + y' >= z'), AtLeast 1]

                , checkLiquid "tests/Liquid" "tests/Liquid/SimplePoly.hs" "snd2Int" 800 3 [RForAll (\[x, y, z] -> isInt x $ \x' -> isInt y $ \y' -> isInt z $ \z' -> x' /= y' && y' == z'), Exactly 1]
                , checkLiquid "tests/Liquid" "tests/Liquid/SimplePoly.hs" "sumPair" 800 2 [AtLeast 1, RForAll (\[App (App _ x) y, z] -> isInt x $ \x' -> isInt y $ \y' -> isInt z $ \z' ->  x' > z' || y' > z')]
                , checkLiquid "tests/Liquid" "tests/Liquid/SimplePoly.hs" "switchInt" 600 2 [Exactly 1, RForAll (\[App (App _ x) _, App (App _ _) y] -> getIntB x $ \ x' -> getIntB y $ \ y' -> x' == y')]

                , checkLiquid "tests/Liquid" "tests/Liquid/Peano.hs" "add" 1400 3 [RForAll (\[x, y, _] -> x `eqIgT` zeroPeano || y `eqIgT` zeroPeano), AtLeast 5]
                , checkLiquid "tests/Liquid" "tests/Liquid/Peano.hs" "fromInt" 600 2 [RForAll (\[x, y] -> isInt x (\x' -> x' == 0)  && y `eqIgT` zeroPeano), AtLeast 1]

                , checkLiquid "tests/Liquid" "tests/Liquid/GetNth.hs" "getNthInt" 4000 3 [AtLeast 3, RForAll getNthErrors]
                , checkLiquid "tests/Liquid" "tests/Liquid/GetNth.hs" "sumC" 2000 2 [AtLeast 3, RForAll (\[_, y] -> isInt y $ (==) 0)]
                , checkLiquid "tests/Liquid" "tests/Liquid/GetNth.hs" "getNth" 4000 4 [AtLeast 3]
                , checkLiquid "tests/Liquid" "tests/Liquid/GetNth.hs" "sumCList" 2000 2 [AtLeast 3]

                , checkLiquid "tests/Liquid" "tests/Liquid/DataRefTest.hs" "addMaybe" 1000 3 
                    [AtLeast 1, RForAll (\[_, y, z] -> isInt y $ \y' -> appNthArgIs z (\z' -> isInt z' $ \z'' -> z'' <= y') 2)]
                , checkLiquid "tests/Liquid" "tests/Liquid/DataRefTest.hs" "addMaybe2" 2000 3
                    [AtLeast 1, RForAll (\[x, _, _] -> appNthArgIs x (\x' -> isInt x' $ \x'' -> x'' >= 0) 2)
                              , RForAll (\[_, y, z] -> isInt y $ \y' -> appNthArgIs z (\z' -> isInt z' $ \z'' -> z'' <= y') 2)]
                , checkLiquid "tests/Liquid" "tests/Liquid/DataRefTest.hs" "getLeftInts" 2000 2 
                    [AtLeast 1, RForAll (\[x, _] -> dcInAppHasName "Right" x 3)]
                , checkLiquid "tests/Liquid" "tests/Liquid/DataRefTest.hs" "sumSameInts" 2000 3 
                    [AtLeast 1, RForAll (\[x, y, _] -> dcInAppHasName "Right" x 3 && dcInAppHasName "Left" y 3)]
                , checkLiquid "tests/Liquid" "tests/Liquid/DataRefTest.hs" "sub1" 1200 4 [AtLeast 1]

                , checkLiquid "tests/Liquid" "tests/Liquid/NumOrd.hs" "subTuple" 1200 3 [AtLeast 1]

                , checkLiquid "tests/Liquid" "tests/Liquid/CommentMeasures.hs" "d" 1000 2 [AtLeast 1]
                , checkLiquid "tests/Liquid" "tests/Liquid/CommentMeasures.hs" "unpackCP'" 100000 2 [Exactly 0]
                , checkLiquid "tests/Liquid" "tests/Liquid/CommentMeasures.hs" "unpackBool" 1000 2 [AtLeast 1, RForAll (\[_, r] -> getBoolB r (== False))]
                , checkLiquid "tests/Liquid" "tests/Liquid/CommentMeasures.hs" "sumSameOneOfs" 100000 3 [Exactly 0]
                , checkLiquid "tests/Liquid" "tests/Liquid/CommentMeasures.hs" "gets2As" 2000 3 
                    [AtLeast 1, RExists (\[x, y, _] -> buriedDCName "B" x && buriedDCName "B" y)]
                , checkLiquid "tests/Liquid" "tests/Liquid/CommentMeasures.hs" "gets2As'" 1000 3 
                    [AtLeast 1, RExists (\[x, y, _] -> buriedDCName "A" x && buriedDCName "B" y)
                              , RExists (\[x, y, _] -> buriedDCName "B" x && buriedDCName "A" y)]
                , checkLiquid "tests/Liquid" "tests/Liquid/CommentMeasures.hs" "ge4gt5" 1000 2 
                    [AtLeast 1, RForAll (\[x, y] -> appNth x 1 $ \x' -> isInt x' $ \x'' -> isInt y $ \y' ->  x'' == 4 && y' == 5)]

                , checkLiquid "tests/Liquid" "tests/Liquid/ConcatList.hs" "concat2" 800 3 [AtLeast 2]
                , checkLiquid "tests/Liquid" "tests/Liquid/ConcatList.hs" "concat3" 800 3 [AtLeast 2]
                , checkLiquid "tests/Liquid" "tests/Liquid/ConcatList.hs" "concat5" 1600 3 [AtLeast 1]

                , checkLiquidWithConfig "tests/Liquid/Tests" "tests/Liquid/Tests/Group3.lhs" "f" 1 (mkConfigTestWithMap {steps = 2200}) [AtLeast 1]

                , checkLiquid "tests/Liquid/Tests" "tests/Liquid/Nonused.hs" "g" 2000 1 [AtLeast 1]

                -- , checkLiquid "tests/Liquid/Tests" "tests/Liquid/HigherOrderRef.hs" "f1" 2000 3 [Exactly 0]
                -- , checkLiquid "tests/Liquid/Tests" "tests/Liquid/HigherOrderRef.hs" "f2" 2000 3 [AtLeast 4, RForAll (\[_, x, y] -> x == y)]
                -- , checkLiquid "tests/Liquid/Tests" "tests/Liquid/HigherOrderRef.hs" "f3" 2000 3 [Exactly 0]
                -- , checkLiquid "tests/Liquid/Tests" "tests/Liquid/HigherOrderRef.hs" "f4" 2000 3 [AtLeast 4, RForAll (\[_, x, _] -> isInt x $ \x' -> x' == 0)]
                -- , checkLiquid "tests/Liquid/Tests" "tests/Liquid/HigherOrderRef.hs" "f5" 2000 3 [Exactly 0]
                -- , checkLiquid "tests/Liquid/Tests" "tests/Liquid/HigherOrderRef.hs" "f6" 2000 3 [AtLeast 10]
                -- , checkLiquid "tests/Liquid/Tests" "tests/Liquid/HigherOrderRef.hs" "f7" 2000 3 [AtLeast 10, RForAll (\[x, _, y] -> isInt x $ \x' -> isInt y $ \y' -> x' == y')]
                -- , checkLiquid "tests/Liquid/Tests" "tests/Liquid/HigherOrderRef.hs" "f8" 2000 3 [AtLeast 10]
                -- , checkLiquid "tests/Liquid/Tests" "tests/Liquid/HigherOrderRef.hs" "callf" 2000 3 [AtLeast 1]

                -- , checkLiquid "tests/Liquid/Error/Tests" "tests/Liquid/Error/Error1.hs" "f" 600 2 [AtLeast 1]
                , checkLiquid "tests/Liquid/Error/Tests" "tests/Liquid/Error/Error2.hs" "f1" 2000 4 [AtLeast 1]
                , checkLiquid "tests/Liquid" "tests/Liquid/ZipWith.lhs" "distance" 1000 4 [AtLeast 3]

                , checkLiquid "tests/Liquid/Tests" "tests/Liquid/FoldrTests.hs" "max2" 1000 2 [Exactly 0]
                , checkLiquid "tests/Liquid/Tests" "tests/Liquid/FoldrTests.hs" "max3" 1000 2 [Exactly 0]
                , checkLiquid "tests/Liquid/Tests" "tests/Liquid/SimpleAnnot.hs" "simpleF" 1000 1 [Exactly 0]

                , checkLiquid "tests/Liquid/Tests" "tests/Liquid/Ordering.hs" "lt" 1000 2 [AtLeast 1]
                , checkLiquid "tests/Liquid/Tests" "tests/Liquid/Ordering.hs" "gt" 1000 2 [AtLeast 1]
                , checkLiquid "tests/Liquid/Tests" "tests/Liquid/Ordering.hs" "oneOrOther" 1000 2 [Exactly 0]

                , checkLiquid "tests/Liquid/Tests" "tests/Liquid/AddKV.lhs" "empty" 1000 3 [Exactly 0]

                , checkLiquid "tests/Liquid/Tests" "tests/Liquid/PropSize.hs" "prop_size" 2000 1 [AtLeast 1]
                , checkLiquid "tests/Liquid/Tests" "tests/Liquid/PropSize2.hs" "prop_size" 2000 1 [AtLeast 1]

                , checkLiquidWithConfig "tests/Liquid/Tests" "tests/Liquid/WhereFuncs.lhs" "f" 3 (mkConfigTestWithMap {steps = 1000}) [Exactly 0]
                , checkLiquidWithConfig "tests/Liquid/Tests" "tests/Liquid/WhereFuncs.lhs" "g" 3 (mkConfigTestWithMap {steps = 1000}) [Exactly 0]

                , checkLiquid "tests/Liquid/Tests" "tests/Liquid/WhereFuncs2.hs" "hCalls" 1000 3 [AtLeast 1]
                , checkLiquid "tests/Liquid/Tests" "tests/Liquid/WhereFuncs2.hs" "i" 1000 2 [AtLeast 1]

                , checkLiquid "tests/Liquid/Tests" "tests/Liquid/PropConcat.lhs" "prop_concat" 1000 1 [AtLeast 1]

                , checkLiquid "tests/Liquid/Tests" "tests/Liquid/Distance.lhs" "distance" 1000 4 [AtLeast 1]
                , checkLiquid "tests/Liquid/MultModules" "tests/Liquid/MultModules/CallZ.lhs" "callZ" 1000 3 [AtLeast 1]

                , checkAbsLiquid "tests/Liquid/" "tests/Liquid/AddToEven.hs" "f" 2000 1
                    [ AtLeast 1
                    , RForAll (\[i] r [(FuncCall { funcName = Name n _ _ _, returns = r' }) ]
                                    -> n == "g" && isInt i (\i' -> i' `mod` 2 == 0) && r == r' )]

                , checkLiquid "tests/Liquid/" "tests/Liquid/ListTests.lhs" "r" 1000 1 [Exactly 0]
                , checkLiquid "tests/Liquid/" "tests/Liquid/ListTests.lhs" "prop_map" 1500 3 [AtLeast 3]
                , checkLiquid "tests/Liquid/" "tests/Liquid/ListTests.lhs" "concat" 1000 2 [AtLeast 3]
                , checkLiquid "tests/Liquid/" "tests/Liquid/ListTests.lhs" "prop_concat_1" 1500 1 [AtLeast 1]

                , checkLiquid "tests/Liquid/" "tests/Liquid/MapReduceTest.lhs" "mapReduce" 1500 1 [Exactly 0]
                , checkLiquid "tests/Liquid/" "tests/Liquid/NearestTest.lhs" "nearest" 1500 1 [Exactly 1]
        ]

-- Tests that are intended to ensure a specific feature works, but that are not neccessarily interesting beyond that
testFileTests :: IO TestTree
testFileTests = 
    return . testGroup "TestFiles"
        =<< sequence [
                  checkExpr "tests/TestFiles/" "tests/TestFiles/IfTest.hs" 400 Nothing Nothing "f" 3 [RForAll (\[App _ (Lit (LitInt x)), App _ (Lit (LitInt y)), App _ (Lit (LitInt r))] -> if x == y then r == x + y else r == y), AtLeast 2]

                , checkExpr "tests/TestFiles/" "tests/TestFiles/AssumeAssert.hs" 400 Nothing (Just "assertGt5") "outShouldBeGt5" 2 [Exactly 0]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/AssumeAssert.hs" 400 Nothing (Just "assertGt5") "outShouldBeGe5" 2 [AtLeast 1]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/AssumeAssert.hs" 400 (Just "assumeGt5") (Just "assertGt5") "outShouldBeGt5" 2 [Exactly 0]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/AssumeAssert.hs" 400 (Just "assumeGt5") (Just "assertGt5") "outShouldBeGe5" 2 [Exactly 0]

                , checkExpr "tests/TestFiles/" "tests/TestFiles/CheckSq.hs" 400 Nothing Nothing "checkSq" 2 [AtLeast 2, RExists (\[x, _] -> isInt x (\x' -> x' == 3))]

                , checkExpr "tests/TestFiles/" "tests/TestFiles/Defunc1.hs" 400 Nothing Nothing "f" 2 [RExists defunc1Add1, RExists defunc1Multiply2, RExists defuncB, AtLeast 3]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/Defunc1.hs" 400 Nothing Nothing "x" 2 [AtLeast 1]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/Defunc1.hs" 600 Nothing Nothing "mapYInt" 3 [AtLeast 1]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/Defunc1.hs" 600 Nothing Nothing "makeMoney" 3 [AtLeast 3]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/Defunc1.hs" 1600 Nothing Nothing "compZZ" 4 [AtLeast 2, RForAll (\[_, _, _, x] -> getBoolB x not)]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/Defunc1.hs" 1600 Nothing Nothing "compZZ2" 4 [AtLeast 2, RForAll (\[_, _, _, x] -> getBoolB x not)]

                , checkExpr "tests/TestFiles/" "tests/TestFiles/Defunc2.hs" 400 Nothing Nothing "funcMap" 3 [RForAll defunc2Check, AtLeast 30]

                , checkExpr "tests/TestFiles/" "tests/TestFiles/MultCase.hs" 400 Nothing Nothing "f" 2
                    [ RExists (\[App _ (Lit (LitInt x)), y] -> x == 2 && getBoolB y id)
                    , RExists (\[App _ (Lit (LitInt x)), y] -> x == 1 && getBoolB y id)
                    , RExists (\[App _ (Lit (LitInt x)), y] -> x /= 2 && x /= 1 && getBoolB y not)]

                , checkExpr "tests/TestFiles/" "tests/TestFiles/LetFloating/LetFloating.hs" 400 (Just "output6") Nothing "f" 2 [AtLeast 1, RExists (\[App _ (Lit (LitInt x)), _] -> x == 6)]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/LetFloating/LetFloating2.hs" 400 (Just "output16") Nothing "f" 2 [AtLeast 1, RExists (\[App _ (Lit (LitInt x)), _] -> x == 15)]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/LetFloating/LetFloating3.hs" 600 (Just "output32") Nothing "f" 2 [AtLeast 1, RExists (\[App _ (Lit (LitInt x)), _] -> x == 4)]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/LetFloating/LetFloating4.hs" 400 (Just "output12") Nothing "f" 2 [AtLeast 1, RExists (\[App _ (Lit (LitInt x)), _] -> x == 11)]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/LetFloating/LetFloating5.hs" 400 (Just "output19") Nothing "f" 3 [AtLeast 1, RForAll (\[App _ (Lit (LitInt x)), App _ (Lit (LitInt y)), _] -> x + y + 1 == 19)]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/LetFloating/LetFloating6.hs" 400 (Just "output32") Nothing "f" 2 [AtLeast 1, RExists (\[App _ (Lit (LitInt x)), _] -> x == 25)]

                , checkExpr "tests/TestFiles/" "tests/TestFiles/TypeClass/TypeClass1.hs" 400 Nothing Nothing "f" 2 [RExists (\[x, y] -> x == y), Exactly 1]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/TypeClass/TypeClass2.hs" 400 Nothing Nothing "f" 2 [RExists (\[x, y] -> x == y), Exactly 1]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/TypeClass/TypeClass3.hs" 400 Nothing Nothing "f" 2 [RExists (\[x, y] -> getIntB x $ \x' -> getIntB y $ \y' -> x' + 8 == y'), Exactly 1]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/TypeClass/HKTypeClass1.hs" 400 (Just "largeJ") Nothing "extractJ" 2 [RForAll (\[x, ly@(App _ (Lit (LitInt y)))] -> appNthArgIs x (ly ==) 2 && y > 100), Exactly 1]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/TypeClass/HKTypeClass1.hs" 400 (Just "largeE") Nothing "extractE" 2 [RForAll (\[x, ly@(App _ (Lit (LitInt y)))] -> appNthArgIs x (ly ==) 4 && y > 100), Exactly 1]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/TypeClass/HKTypeClass1.hs" 400 Nothing Nothing "changeJ" 3 [RForAll (\[_, x, y] -> dcInAppHasName "J" x 2 && (dcInAppHasName "J" y 2 || isError y)), AtLeast 2]

                , checkExpr "tests/TestFiles/" "tests/TestFiles/Case1.hs" 400 Nothing Nothing "f" 2 [ RExists (\[App _ (Lit (LitInt x)), y] -> x < 0 && dcHasName "A" y)
                                                                                                              , RExists (\[App _ (Lit (LitInt x)), y] -> x >= 0 && dcHasName "C" y), Exactly 2]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/Case2.hs" 400 Nothing Nothing "f" 2 
                        [ RExists exists1
                        , RExists exists2
                        , RExists exists3
                        , RExists exists4
                        , AtLeast 4]

                , checkExpr "tests/TestFiles/" "tests/TestFiles/Guards.hs" 400 (Just "g") Nothing "f" 2 [AtLeast 1, RExists (\[dc, _] -> getBoolB dc id)]

                , checkExpr "tests/TestFiles/" "tests/TestFiles/Infinite.hs" 400 (Just "g") Nothing "f" 2 [AtLeast 1, RExists (\[App _ (Lit (LitInt x)), _] -> x <= 100 && x /= 80)]

                , checkExpr "tests/TestFiles/" "tests/TestFiles/Strictness1.hs" 400 Nothing Nothing "f" 1 [AtLeast 1, RExists (\[(App x (App _ (Lit (LitInt y))))] -> dcHasName "A" x && y == 9)]

                , checkExpr "tests/TestFiles/" "tests/TestFiles/Where1.hs" 400 Nothing Nothing "f" 2 [ RExists (\[App _ (Lit (LitInt x)), App _ (Lit (LitInt y))] -> x == 4 && y == 1)
                                                                                                           , RExists (\[App _ (Lit (LitInt x)), App _ (Lit (LitInt y))] -> x /= 4 && y == 1) ]
                
                , checkExpr "tests/TestFiles/" "tests/TestFiles/Error/Error1.hs" 400 Nothing Nothing "f" 2 [AtLeast 1, RForAll(errors)]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/Error/Error1.hs" 400 Nothing Nothing "g" 2 [AtLeast 1, RForAll(errors)]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/Error/Error2.hs" 400 Nothing Nothing "f" 1 [AtLeast 1, RForAll(errors)]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/Error/Error3.hs" 400 Nothing Nothing "f" 2 [AtLeast 1, RForAll(errors)]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/Error/Error3.hs" 400 Nothing Nothing "g" 2 [AtLeast 1, RForAll(not . errors)]

                , checkExpr "tests/TestFiles/" "tests/TestFiles/BadNames1.hs" 400 Nothing Nothing "abs'" 2 [Exactly 2]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/BadNames1.hs" 400 Nothing Nothing "xswitch" 2 [AtLeast 10]

                , checkExpr "tests/TestFiles/" "tests/TestFiles/PolyDataTy1.hs" 400 Nothing Nothing "f" 3 [Exactly 2, RExists (\[x, _, y] -> x == y), RExists (\[_, App _ x, y] -> x == y)]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/PolyDataTy1.hs" 400 Nothing Nothing "getFstXIntInt" 2 [AtLeast 2, RExists (\[x, y] -> isApp x && isError y)]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/PolyDataTy1.hs" 400 Nothing Nothing "sum" 2 [AtLeast 3, RExists (\[x, y] -> isApp x && isError y)]

                , checkExpr "tests/TestFiles/" "tests/TestFiles/MultiSplit.hs" 1000 (Just "equals1") Nothing "f" 3 [Exactly 0]

                , checkExpr "tests/TestFiles/" "tests/TestFiles/MatchesFunc1.hs" 400 Nothing Nothing "f" 2 [RExists (\[x, y] -> getIntB x $ \x' -> getIntB y $ \y' ->  y' == 6 + x'), AtLeast 1]

                , checkExpr "tests/TestFiles/" "tests/TestFiles/RecordFields1.hs" 400 Nothing Nothing "f" 2 [RExists (\[x, y] -> appNthArgIs x notCast 0 && appNthArgIs x (\x' -> getIntB x' $ \x'' -> getIntB y $ \y' -> x'' + 1 == y') 1), Exactly 1]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/RecordFields1.hs" 400 Nothing Nothing "fCall" 1 [RExists (\[x] -> isInt x ((==) 35)), Exactly 1]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/RecordFields1.hs" 400 Nothing Nothing "g" 2 [RExists (\[x, y] -> appNthArgIs x (dcHasName "A") 2 && appNthArgIs y (dcHasName "B") 2)
                                                                                                                      , RExists (\[x, y] -> appNthArgIs x (dcHasName "B") 2 && appNthArgIs y (dcHasName "C") 2)
                                                                                                                      , RExists (\[x, y] -> appNthArgIs x (dcHasName "C") 2 && appNthArgIs y (dcHasName "A") 2)
                                                                                                                      , Exactly 3]

                , checkExpr "tests/TestFiles/Deriving" "tests/TestFiles/Deriving/DerivingSimple.hs" 400 Nothing Nothing "eq" 3 [AtLeast  2, RForAll (\[_, _, x] -> isBool x)]
                , checkExpr "tests/TestFiles/Deriving" "tests/TestFiles/Deriving/DerivingSimple.hs" 400 Nothing Nothing "lt" 3 [AtLeast 2, RForAll (\[_, _, x] -> isBool x)]
                , checkExpr "tests/TestFiles/Deriving" "tests/TestFiles/Deriving/DerivingComp.hs" 800 Nothing Nothing "eq" 3 [AtLeast 2, RForAll (\[_, _, x] -> isBool x)]
                , checkExpr "tests/TestFiles/Deriving" "tests/TestFiles/Deriving/DerivingComp.hs" 800 Nothing Nothing "lt" 3 [AtLeast 2, RForAll (\[_, _, x] -> isBool x)]

                , checkExpr "tests/TestFiles/Coercions" "tests/TestFiles/Coercions/Age.hs" 400 Nothing Nothing "born" 1 [ Exactly 1
                                                                                                                                  , RForAll (\[x] -> inCast x (\x' -> appNthArgIs x' (Lit (LitInt 0) ==) 1) (\(t1 :~ t2) -> isIntT t1 && typeNameIs t2 "Age"))]
                , checkExpr "tests/TestFiles/Coercions" "tests/TestFiles/Coercions/Age.hs" 400 Nothing Nothing "yearPasses" 2 [ AtLeast 1
                                                                                                                                        , RForAll (\[x, y] -> inCast x (const True) (\(_ :~ t2) -> typeNameIs t2 "Age")
                                                                                                                                                           && inCast y (const True) (\(_ :~ t2) -> typeNameIs t2 "Age") )]
                , checkExpr "tests/TestFiles/Coercions" "tests/TestFiles/Coercions/Age.hs" 400 Nothing Nothing "age" 2 [ AtLeast 1
                                                                                                                                 , RForAll (\[x, y] -> inCast x (const True) (\(_ :~ t2) -> typeNameIs t2 "Age") && isInt y (const True))]
                , checkExpr "tests/TestFiles/Coercions" "tests/TestFiles/Coercions/Age.hs" 400 Nothing Nothing "diffAge" 3 [ AtLeast 1
                                                                                                                                     , RForAll (\[x, y, z] -> inCast x (const True) (\(_ :~ t2) -> typeNameIs t2 "Age") 
                                                                                                                                                           && inCast y (const True) (\(_ :~ t2) -> typeNameIs t2 "Age")
                                                                                                                                                           && inCast z (const True) (\(_ :~ t2) -> typeNameIs t2 "Years"))]
                , checkExpr "tests/TestFiles/Coercions" "tests/TestFiles/Coercions/Age.hs" 400 Nothing Nothing "yearBefore" 2 [ AtLeast 5 ]
                , checkExpr "tests/TestFiles/Coercions" "tests/TestFiles/Coercions/NewType1.hs" 400 Nothing Nothing "add1N4" 2 [ Exactly 1
                                                                                                                                         , RForAll (\[x, y] -> inCast x (const True) (\(_ :~ t2) -> typeNameIs t2 "N4") 
                                                                                                                                                            && inCast y (const True) (\(_ :~ t2) -> typeNameIs t2 "N4"))]
                , checkExpr "tests/TestFiles/Coercions" "tests/TestFiles/Coercions/NewType1.hs" 400 Nothing Nothing "f" 2 [ Exactly 1
                                                                                                                                    , RForAll (\[x, y] -> inCast x (const True) (\(_ :~ t2) -> typeNameIs t2 "NewX") && dcHasName "X" y)]
                , checkExpr "tests/TestFiles/Coercions" "tests/TestFiles/Coercions/NewType1.hs" 400 Nothing Nothing "g" 2 [ Exactly 1
                                                                                                                                    , RForAll (\[x, y] -> dcHasName "X" x && inCast y (const True) (\(_ :~ t2) -> typeNameIs t2 "NewX"))]

                , checkExpr "tests/TestFiles/Coercions" "tests/TestFiles/Coercions/NewType1.hs" 400 Nothing Nothing "mapWInt" 3 [ AtLeast 2
                                                                                                                                , RForAll (\[_, x, y] -> isError y
                                                                                                                                                      || (inCast x (const True) (\(_ :~ t2) -> typeNameIs t2 "W") &&
                                                                                                                                                          inCast x (const True) (\(_ :~ t2) -> typeNameIs t2 "W"))) ]

                , checkExpr "tests/TestFiles/Coercions" "tests/TestFiles/Coercions/NewType1.hs" 400 Nothing Nothing "appLeftFloat" 3 [ AtLeast 2
                                                                                                                                               , RExists (\[_, _, y] -> inCast y (\y' -> dcInAppHasName "L" y' 3) (const True))
                                                                                                                                               , RExists (\[_, _, y] -> inCast y (\y' -> dcInAppHasName "R" y' 3) (const True))]
                , checkExpr "tests/TestFiles/Coercions" "tests/TestFiles/Coercions/NewType1.hs" 400 Nothing Nothing "getLIntFloat" 2 [ AtLeast 2
                                                                                                                                               , RExists (\[_, y] -> isInt y (const True))
                                                                                                                                               , RExists (\[_, y] -> isError y)]
                , checkExpr "tests/TestFiles/Coercions" "tests/TestFiles/Coercions/NewType1.hs" 400 Nothing Nothing "getRIntFloat" 2 [ AtLeast 2
                                                                                                                                               , RExists (\[_, y] -> isFloat y (const True))
                                                                                                                                               , RExists (\[_, y] -> isError y)]
                , checkExpr "tests/TestFiles/Coercions" "tests/TestFiles/Coercions/NewType1.hs" 400 Nothing Nothing "getCIntFloatDouble" 2 [ AtLeast 2
                                                                                                                                                     , RExists (\[_, y] -> isFloat y (const True))
                                                                                                                                                     , RExists (\[_, y] -> isError y)]
                , checkExpr "tests/TestFiles/Coercions" "tests/TestFiles/Coercions/NewType1.hs" 400 Nothing Nothing "getRIntFloatX'" 2 [ AtLeast 2
                                                                                                                                       , RExists (\[x, y] -> inCast x (\x' -> dcInAppHasName "TR" x' 4) (const True)
                                                                                                                                                          && isInt y (const True))
                                                                                                                                       , RExists (\[_, y] -> isError y)]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/Expr.hs" 400 Nothing Nothing "leadingLams" 2 [AtLeast 5, RForAll (\[_, y] -> noUndefined y)]
                -- , checkExpr "tests/TestFiles/Coercions" "tests/TestFiles/Coercions/GADT.hs" 400 Nothing Nothing "g" 2 [AtLeast 2
                --                                                                                                                 , RExists (\[x, y] -> x == Lit (LitInt 0) && y == App (Data (PrimCon I)) (Lit (LitInt 0)))
                --                                                                                                                 , RExists (\[x, _] -> x /= Lit (LitInt 0))]
                -- , checkExpr "tests/TestFiles/" "tests/TestFiles/HigherOrderList.hs" 400 Nothing Nothing "g" 3 [AtLeast  10] 
                
        ]

baseTests :: IO TestTree
baseTests =
    return . testGroup "Base"
        =<< sequence [
              checkInputOutput "tests/Samples/" "tests/Samples/Peano.hs" "Peano" "add" 400 3 [AtLeast 4]
            , checkInputOutput "tests/BaseTests/" "tests/BaseTests/ListTests.hs" "ListTests" "test" 1000 2 [AtLeast 1]
            , checkInputOutput "tests/BaseTests/" "tests/BaseTests/ListTests.hs" "ListTests" "maxMap" 1000 2 [AtLeast 4]
            , checkInputOutput "tests/BaseTests/" "tests/BaseTests/ListTests.hs" "ListTests" "minTest" 1000 2 [AtLeast 2]
            , checkInputOutput "tests/BaseTests/" "tests/BaseTests/ListTests.hs" "ListTests" "foldrTest2" 1000 2 [AtLeast 1]
            , checkInputOutput "tests/BaseTests/" "tests/BaseTests/Tuples.hs" "Tuples" "addTupleElems" 1000 2 [AtLeast 2]

            , checkInputOutput "tests/BaseTests/" "tests/BaseTests/MaybeTest.hs" "MaybeTest" "sumN" 1000 4 [AtLeast 6]
            , checkInputOutput "tests/BaseTests/" "tests/BaseTests/MaybeTest.hs" "MaybeTest" "lengthN" 1000 5 [AtLeast 6]
            , checkInputOutput "tests/BaseTests/" "tests/BaseTests/MaybeTest.hs" "MaybeTest" "average" 2000 5 [AtLeast 6]
            , checkInputOutput "tests/BaseTests/" "tests/BaseTests/MaybeTest.hs" "MaybeTest" "averageF" 2000 2 [AtLeast 6]
            , checkInputOutput "tests/BaseTests/" "tests/BaseTests/MaybeTest.hs" "MaybeTest" "maybeAvg" 200 4 [AtLeast 6]

            , checkInputOutput "tests/BaseTests/" "tests/BaseTests/Other.hs" "Other" "check4VeryEasy2" 600 1 [AtLeast 1]
        ]

primTests :: IO TestTree
primTests =
    return . testGroup "Prims"
        =<< sequence [
              checkInputOutput "tests/TestFiles/" "tests/TestFiles/Prim2.hs" "Prim2" "quotI1" 1000 3 [AtLeast 4]
            , checkInputOutput "tests/TestFiles/" "tests/TestFiles/Prim2.hs" "Prim2" "quotI2" 1000 3 [AtLeast 4]
            , checkInputOutput "tests/TestFiles/" "tests/TestFiles/Prim2.hs" "Prim2" "remI1" 1000 3 [AtLeast 4]
            , checkInputOutput "tests/TestFiles/" "tests/TestFiles/Prim2.hs" "Prim2" "remI2" 1000 3 [AtLeast 3]

            , checkInputOutput "tests/TestFiles/" "tests/TestFiles/Prim2.hs" "Prim2" "p1List" 300000 1 [AtLeast 1]
            , checkInputOutput "tests/TestFiles/" "tests/TestFiles/Prim2.hs" "Prim2" "p2List" 700000 1 [AtLeast 1]
            , checkInputOutput "tests/TestFiles/" "tests/TestFiles/Prim2.hs" "Prim2" "integerToFloatList" 150000 1 [AtLeast 1]
            , checkInputOutput "tests/TestFiles/" "tests/TestFiles/Prim2.hs" "Prim2" "sqrtList" 10000 1 [AtLeast 1]
        ]

checkExpr :: String -> String -> Int -> Maybe String -> Maybe String -> String -> Int -> [Reqs ([Expr] -> Bool)] -> IO TestTree
checkExpr proj src stps m_assume m_assert entry i reqList =
    checkExprReaches proj src stps m_assume m_assert Nothing entry i reqList

checkExprReaches :: String -> String -> Int -> Maybe String -> Maybe String -> Maybe String -> String -> Int -> [Reqs ([Expr] -> Bool)] -> IO TestTree
checkExprReaches proj src stps m_assume m_assert m_reaches entry i reqList = do
    checkExprWithConfig proj src m_assume m_assert m_reaches entry i (mkConfigTest {steps = stps}) reqList

checkExprWithConfig :: String -> String -> Maybe String -> Maybe String -> Maybe String -> String -> Int -> Config -> [Reqs ([Expr] -> Bool)] -> IO TestTree
checkExprWithConfig proj src m_assume m_assert m_reaches entry i config reqList = do
    res <- testFile proj src m_assume m_assert m_reaches entry config
    
    let ch = case res of
                Left _ -> False
                Right exprs -> checkExprGen (map (\(inp, out) -> inp ++ [out]) exprs) i reqList

    return . testCase src
        $ assertBool ("Assume/Assert for file " ++ src ++ 
                      " with functions [" ++ (fromMaybe "" m_assume) ++ "] " ++
                                      "[" ++ (fromMaybe "" m_assert) ++ "] " ++
                                              entry ++ " failed.\n") ch
 
testFile :: String -> String -> Maybe String -> Maybe String -> Maybe String -> String -> Config -> IO (Either SomeException [([Expr], Expr)])
testFile proj src m_assume m_assert m_reaches entry config =
    try (testFileWithConfig proj src m_assume m_assert m_reaches entry config)

testFileWithConfig :: String -> String -> Maybe String -> Maybe String -> Maybe String -> String -> Config -> IO ([([Expr], Expr)])
testFileWithConfig proj src m_assume m_assert m_reaches entry config = do
    (mb_modname, binds, tycons, cls, _, ex) <- translateLoaded proj src [] True config

    let (init_state, _) = initState binds tycons cls (fmap T.pack m_assume) (fmap T.pack m_assert) (fmap T.pack m_reaches) (isJust m_assert || isJust m_reaches) (T.pack entry) mb_modname ex config
    
    SomeSMTSolver con <- getSMT config
    let con' = GroupRelated (ADTSolver :?> con)

    r <- run (NonRedPCRed config
               :<~| StdRed con' config)
             (MaxOutputsHalter 
               :<~> ZeroHalter)
             NextOrderer con' [] config init_state

    closeIO con

    return $ map (\(_, i, o, _) -> (i, o)) r

checkLiquid :: FilePath -> FilePath -> String -> Int -> Int -> [Reqs ([Expr] -> Bool)] -> IO TestTree
checkLiquid proj fp entry stps i reqList = checkLiquidWithConfig proj fp entry i (mkConfigTest {steps = stps}) reqList

checkLiquidWithConfig :: FilePath -> FilePath -> String -> Int -> Config -> [Reqs ([Expr] -> Bool)] -> IO TestTree
checkLiquidWithConfig proj fp entry i config reqList = do
    res <- findCounterExamples' proj fp (T.pack entry) [] [] config

    let (ch, r) = case res of
                Left e -> (False, Left e)
                Right exprs -> (checkExprGen (map (\(_, inp, out, _) -> inp ++ [out]) exprs) i reqList, Right ())

    return . testCase fp
        $ assertBool ("Liquid test for file " ++ fp ++ 
                      " with function " ++ entry ++ " failed.\n" ++ show r) ch

checkAbsLiquid :: FilePath -> FilePath -> String -> Int -> Int -> [Reqs ([Expr] -> Expr -> [FuncCall] -> Bool)] -> IO TestTree
checkAbsLiquid proj fp entry stps i reqList = checkAbsLiquidWithConfig proj fp entry i (mkConfigTest {steps = stps}) reqList

checkAbsLiquidWithConfig :: FilePath -> FilePath -> String -> Int -> Config -> [Reqs ([Expr] -> Expr -> [FuncCall] -> Bool)] -> IO TestTree
checkAbsLiquidWithConfig proj fp entry i config reqList = do
    res <- findCounterExamples' proj fp (T.pack entry) [] [] config

    let (ch, r) = case res of
                Left e -> (False, Left e)
                Right exprs -> (checkAbsLHExprGen (map (\(s, inp, out, _) -> (s, inp, out)) exprs) i reqList, Right ())

    return . testCase fp
        $ assertBool ("Liquid test for file " ++ fp ++ 
                      " with function " ++ entry ++ " failed.\n" ++ show r) ch


findCounterExamples' :: FilePath -> FilePath -> T.Text -> [FilePath] -> [FilePath] -> Config -> IO (Either SomeException [(State [FuncCall], [Expr], Expr, Maybe FuncCall)])
findCounterExamples' proj fp entry libs lhlibs config = try (return . fst =<< findCounterExamples proj fp entry libs lhlibs config)

errors :: [Expr] -> Bool
errors e =
    case last e of
        Prim Error _ -> True
        _ -> False

mkConfigTest :: Config
mkConfigTest = mkConfigDef { higherOrderSolver = AllFuncs }

mkConfigTestWithMap :: Config
mkConfigTestWithMap = mkConfigTest { base = base mkConfigTest ++ [mapLib]}