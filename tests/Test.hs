{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Test.Tasty
import Test.Tasty.HUnit ( testCase, assertBool, assertFailure )
import Test.Tasty.Options
import Test.Tasty.Runners

import G2.Config

import G2.Interface
import G2.Language as G2

import Control.Exception
import Data.Maybe
import Data.Proxy
import Data.Tagged
import qualified Data.Text as T
import System.Environment
import System.FilePath
import Type.Reflection (Typeable)

import PeanoTest
import HigherOrderMathTest
import GetNthTest
import DefuncTest
import CaseTest
import Expr
import Simplifications
import Typing
import UnionFindTests
import UFMapTests

import RewriteVerify.RewriteVerifyTest
import G2.Translation

import InputOutputTest
import Reqs
import TestUtils

import qualified Data.Map.Lazy as M

-- Run with no arguments for default test cases.
-- All default test cases should pass.
-- Run with flag '--test-options="todo yes"' to run test cases corresponding to to-be-fixed bugs.
main :: IO ()
main = do
    as <- getArgs
    let todo = "--todo" `elem` as
    defaultMainWithIngredients
        (defaultIngredients ++ 
            [TestReporter 
                [ Option (Proxy :: Proxy ToDo) ] 
                (\_ _ -> Just (\_ -> return (\_ -> return False)))
            ])
        (if todo then todoTests else tests)

tests :: TestTree
tests = testGroup "Tests"
        [ sampleTests
        , testFileTests
        , extensionTests
        , baseTests
        , primTests
        , exprTests
        , typingTests
        , simplificationTests
        , ufMapQuickcheck
        , unionFindQuickcheck
        , rewriteTests
        ]

timeout :: Timeout
timeout = mkTimeout 1

-- Test based on examples that are also good for demos
sampleTests :: TestTree
sampleTests = testGroup "Samples"
    [
      checkExprAssert "tests/Samples/Peano.hs" 900 (Just "equalsFour") "add"
        [RForAll $ not . peano_4_out, AtLeast 10]
    , checkExprAssumeAssert "tests/Samples/Peano.hs" 900 (Just "fstIsEvenAddToFour") (Just "fstIsTwo") "add"
        [RExists peano_0_4, RExists peano_4_0, Exactly 2]
    , checkExprAssumeAssert "tests/Samples/Peano.hs" 1200 (Just "multiplyToFour") (Just "equalsFour") "add"
        [RExists peano_1_4_5, RExists peano_4_1_5, Exactly 2]
    , checkExprAssumeAssert "tests/Samples/Peano.hs" 750 (Just "eqEachOtherAndAddTo4") Nothing "add"
        [RForAll peano_2_2, Exactly 1]
    , checkExprAssumeAssert "tests/Samples/Peano.hs" 600 (Just "equalsFour") Nothing "add"
        [ RExists peano_0_4
        , RExists peano_1_3
        , RExists peano_2_2
        , RExists peano_3_1
        , RExists peano_4_0
        , Exactly 5]
    , checkExprAssumeAssert "tests/Samples/Peano.hs" 750 (Just "equalsFour") Nothing "multiply"
        [ RExists peano_1_4
        , RExists peano_2_2
        , RExists peano_4_1
        , Exactly 3]

    , checkExprAssume "tests/Samples/HigherOrderMath.hs" 800 (Just "isTrue0") "notNegativeAt0NegativeAt1"
        [RExists negativeSquareRes, AtLeast 1]
    , checkExprAssume "tests/Samples/HigherOrderMath.hs" 600 (Just "isTrue1") "fixed"
        [ RExists abs2NonNeg
        , RExists squareRes
        , RExists fourthPowerRes
        , RForAll allabs2NonNeg
        , AtLeast 4]
    , checkExpr "tests/Samples/HigherOrderMath.hs" 600 "fixed" [ RExists abs2NonNeg
                                                               , RExists squareRes
                                                               , RExists fourthPowerRes
                                                               , AtLeast 4]
    , checkExprAssumeAssert "tests/Samples/HigherOrderMath.hs" 600 (Just "isTrue2") Nothing "sameFloatArgLarger"
        [ RExists addRes
        , RExists subRes
        , AtLeast 2]
    , checkExpr "tests/Samples/HigherOrderMath.hs" 600 "functionSatisfies" [RExists functionSatisfiesRes, AtLeast 1]
    , checkExpr "tests/Samples/HigherOrderMath.hs" 1000 "approxSqrt" [AtLeast 2]
    -- The below test fails because Z3 returns unknown.
    -- , checkExprAssume "tests/Samples/HigherOrderMath.hs" 1200 (Just "isTrue2") "sameFloatArgLarger" 2
    --                                                             [ RExists approxSqrtRes
                                                                -- , RExists pythagoreanRes
                                                                -- , AtLeast 2]
    
    , checkExprAssumeAssert "tests/Samples/McCarthy91.hs" 1000 (Just "lessThan91") Nothing "mccarthy"
        [ RForAll (\[App _ (Lit (LitInt x)), _] -> x <= 100)
        , AtLeast 1]
    , checkExprAssumeAssert "tests/Samples/McCarthy91.hs" 400 (Just "greaterThan10Less") Nothing "mccarthy"
        [ RForAll (\[App _ (Lit (LitInt x)), _] -> x > 100)
        , AtLeast 1]
    , checkExprAssumeAssert "tests/Samples/McCarthy91.hs" 1000 (Just "lessThanNot91") Nothing "mccarthy" [Exactly 0]
    , checkExprAssumeAssert "tests/Samples/McCarthy91.hs" 1000 (Just "greaterThanNot10Less") Nothing "mccarthy"
        [Exactly 0]

    , checkInputOutput "tests/Samples/GetNth.hs" "getNth" 600 [AtLeast 10]
    , checkInputOutputs "tests/Samples/GetNthPoly.hs" [ ("getNthInt", 600, [AtLeast 10])
                                                      , ("getNthX", 600, [AtLeast 10])
                                                      , ("getNthPeano", 600, [AtLeast 10])
                                                      , ("getNthCListInt", 600, [AtLeast 10])
                                                      , ("getNthCListX", 600, [AtLeast 10])
                                                      , ("getNth", 1000, [AtLeast 10])

                                                      , ("cfmapInt", 1000, [AtLeast 10])
                                                      , ("cfmapIntX", 1600, [AtLeast 10])
                                                      , ("cfmapIntCListInt", 600, [AtLeast 2]) ]

    , checkExprReaches "tests/Samples/GetNthErr.hs" 800 Nothing Nothing (Just "error") "getNth"
        [AtLeast 8, RForAll errors]

    , checkInputOutputs "tests/Samples/FoldlUses.hs" [ ("sum_foldl", 1600, [AtLeast 3])
                                                     , ("dotProd", 1000, [AtLeast 3]) ]

    , checkInputOutputs "tests/Samples/FoldlUsesPoly.hs" [ ("sumMinAndMax", 600, [AtLeast 10])
                                                         , ("maxes", 400, [AtLeast 10])
                                                         , ("switchInt", 400, [AtLeast 1])
                                                         , ("getInInt", 400, [AtLeast 1])
                                                         , ("switchP", 400, [AtLeast 1]) ]

    , checkInputOutput "tests/Samples/NQueens.hs" "allQueensSafe" 2000 [AtLeast 14]

    ]

-- Tests that are intended to ensure a specific feature works, but that are not neccessarily interesting beyond that
testFileTests :: TestTree
testFileTests = testGroup "TestFiles"
    [
      checkExpr "tests/TestFiles/IfTest.hs" 400 "f"
        [ RForAll (\[App _ (Lit (LitInt x)), App _ (Lit (LitInt y)), App _ (Lit (LitInt r))] -> 
            if x == y then r == x + y else r == y)
        , AtLeast 2]

    , checkExprAssert "tests/TestFiles/AssumeAssert.hs" 400 (Just "assertGt5") "outShouldBeGt5" [Exactly 0]
    , checkExprAssert "tests/TestFiles/AssumeAssert.hs" 400 (Just "assertGt5") "outShouldBeGe5" [AtLeast 1]
    , checkExprAssumeAssert "tests/TestFiles/AssumeAssert.hs" 400
        (Just "assumeGt5") (Just "assertGt5") "outShouldBeGt5" [Exactly 0]
    , checkExprAssumeAssert "tests/TestFiles/AssumeAssert.hs" 400
        (Just "assumeGt5") (Just "assertGt5") "outShouldBeGe5" [Exactly 0]

    , checkInputOutputs "tests/TestFiles/Char.hs" [ ("char", 400, [Exactly 2]) ]

    , checkExpr "tests/TestFiles/CheckSq.hs" 400 "checkSq"
        [AtLeast 2, RExists (\[x, _] -> isInt x (\x' -> x' == 3 || x' == -3))]

    , checkExpr "tests/TestFiles/Defunc1.hs" 400 "f"
        [RExists defunc1Add1, RExists defunc1Multiply2, RExists defuncB, AtLeast 3]
    , checkInputOutputs "tests/TestFiles/Defunc1.hs" [ ("x", 400, [AtLeast 1])
                                                     , ("mapYInt", 600, [AtLeast 1])
                                                     , ("makeMoney", 600, [AtLeast 2])
                                                     , ("compZZ", 1600, [AtLeast 2])
                                                     , ("compZZ2", 1600, [AtLeast 2]) ]

    , checkInputOutput "tests/TestFiles/Defunc2.hs" "funcMap" 400 [AtLeast 30]

    , checkExpr "tests/TestFiles/MultCase.hs" 400 "f"
        [ RExists (\[App _ (Lit (LitInt x)), y] -> x == 2 && getBoolB y id)
        , RExists (\[App _ (Lit (LitInt x)), y] -> x == 1 && getBoolB y id)
        , RExists (\[App _ (Lit (LitInt x)), y] -> x /= 2 && x /= 1 && getBoolB y not)]

    , checkExprAssumeAssert "tests/TestFiles/LetFloating/LetFloating.hs" 400 (Just "output6") Nothing "f"
        [AtLeast 1, RExists (\[App _ (Lit (LitInt x)), _] -> x == 6)]
    , checkExprAssumeAssert "tests/TestFiles/LetFloating/LetFloating2.hs" 400 (Just "output16") Nothing "f"
        [AtLeast 1, RExists (\[App _ (Lit (LitInt x)), _] -> x == 15)]
    , checkExprAssumeAssert "tests/TestFiles/LetFloating/LetFloating3.hs" 600 (Just "output32") Nothing "f"
        [AtLeast 1, RExists (\[App _ (Lit (LitInt x)), _] -> x == 4)]
    , checkExprAssumeAssert "tests/TestFiles/LetFloating/LetFloating4.hs" 400 (Just "output12") Nothing "f"
        [AtLeast 1, RExists (\[App _ (Lit (LitInt x)), _] -> x == 11)]
    , checkExprAssumeAssert "tests/TestFiles/LetFloating/LetFloating5.hs" 400 (Just "output19") Nothing "f"
        [AtLeast 1, RForAll (\[App _ (Lit (LitInt x)), App _ (Lit (LitInt y)), _] -> x + y + 1 == 19)]
    , checkExprAssumeAssert "tests/TestFiles/LetFloating/LetFloating6.hs" 400 (Just "output32") Nothing "f"
        [AtLeast 1, RExists (\[App _ (Lit (LitInt x)), _] -> x == 25)]

    , checkExpr "tests/TestFiles/TypeClass/TypeClass1.hs" 400 "f" [RExists (\[x, y] -> x == y), Exactly 1]
    , checkExpr "tests/TestFiles/TypeClass/TypeClass2.hs" 400 "f" [RExists (\[x, y] -> x == y), Exactly 1]
    , checkExpr "tests/TestFiles/TypeClass/TypeClass3.hs" 400 "f"
        [RExists (\[x, y] -> getIntB x $ \x' -> getIntB y $ \y' -> x' + 8 == y'), Exactly 1]
    , checkExpr "tests/TestFiles/TypeClass/TypeClass4.hs" 1000 "f" [AtLeast 1]

    , checkExprAssumeAssert "tests/TestFiles/TypeClass/HKTypeClass1.hs" 400 (Just "largeJ") Nothing "extractJ"
        [RForAll (\[x, ly@(App _ (Lit (LitInt y)))] -> appNthArgIs x (ly ==) 2 && y > 100), Exactly 1]
    , checkExprAssumeAssert "tests/TestFiles/TypeClass/HKTypeClass1.hs" 400 (Just "largeE") Nothing "extractE"
        [RForAll (\[x, ly@(App _ (Lit (LitInt y)))] -> appNthArgIs x (ly ==) 4 && y > 100), Exactly 1]
    , checkExpr "tests/TestFiles/TypeClass/HKTypeClass1.hs" 400 "changeJ"
        [RForAll (\[_, x, y] -> dcInAppHasName "J" x 2 && (dcInAppHasName "J" y 2 || isError y)), AtLeast 2]

    , checkExpr "tests/TestFiles/Case1.hs" 400 "f"
        [ RExists (\[App _ (Lit (LitInt x)), y] -> x < 0 && dcHasName "A" y)
        , RExists (\[App _ (Lit (LitInt x)), y] -> x >= 0 && dcHasName "C" y), Exactly 2]
    , checkExpr "tests/TestFiles/Case2.hs" 400 "f"
        [ RExists exists1
        , RExists exists2
        , RExists exists3
        , RExists exists4
        , AtLeast 4]

    , checkExprAssumeAssert "tests/TestFiles/Guards.hs" 400 (Just "g") Nothing "f"
        [AtLeast 1, RExists (\[dc, _] -> getBoolB dc id)]

    , checkExprAssumeAssert "tests/TestFiles/Infinite.hs" 400 (Just "g") Nothing "f"
        [AtLeast 1, RExists (\[App _ (Lit (LitInt x)), _] -> x <= 100 && x /= 80)]

    , checkExpr "tests/TestFiles/Strictness1.hs" 400 "f"
        [AtLeast 1, RExists (\[(App x (App _ (Lit (LitInt y))))] -> dcHasName "A" x && y == 9)]

    , checkExpr "tests/TestFiles/Where1.hs" 400 "f"
        [ RExists (\[App _ (Lit (LitInt x)), App _ (Lit (LitInt y))] -> x == 4 && y == 1)
        , RExists (\[App _ (Lit (LitInt x)), App _ (Lit (LitInt y))] -> x /= 4 && y == 1) ]
    
    , checkInputOutputs "tests/TestFiles/Error/Error1.hs" [ ("f", 400, [AtLeast 1])
                                                          , ("g", 400, [AtLeast 1])
                                                          , ("f", 400, [AtLeast 1])
                                                          , ("f", 400, [AtLeast 1])
                                                          , ("g", 400, [AtLeast 1]) ]
    , checkInputOutputs "tests/TestFiles/Error/Undefined1.hs" [ ("undefined1", 400, [AtLeast 1])
                                                              , ("undefined2", 400, [AtLeast 1])]
    , checkInputOutput "tests/TestFiles/Error/IrrefutError.hs" "f" 400 [AtLeast 2]

    , checkInputOutputs "tests/TestFiles/BadNames1.hs" [ ("abs'", 400, [Exactly 2])
                                                       , ("xswitch", 400, [AtLeast 10]) ]

    , checkInputOutputs "tests/TestFiles/ListCallStack.hs" [ ("indexOf", 400, [AtLeast 2]) 
                                                           , ("headOf", 400, [AtLeast 2])
                                                           , ("tailOf", 400, [AtLeast 2])
                                                           , ("lastOf", 400, [AtLeast 2])
                                                           , ("initOf", 400, [AtLeast 2])
                                                           , ("cycleOf", 400, [AtLeast 2]) ]

    , checkExpr "tests/TestFiles/PolyDataTy1.hs" 400 "f"
        [Exactly 2, RExists (\[x, _, y] -> x == y), RExists (\[_, App _ x, y] -> x == y)]
    , checkExpr "tests/TestFiles/PolyDataTy1.hs" 400 "getFstXIntInt"
        [AtLeast 2, RExists (\[x, y] -> isApp x && isError y)]
    , checkExpr "tests/TestFiles/PolyDataTy1.hs" 400 "sum" [AtLeast 3, RExists (\[x, y] -> isApp x && isError y)]

    , checkExprAssumeAssert "tests/TestFiles/MultiSplit.hs" 1000 (Just "equals1") Nothing "f" [Exactly 0]

    , checkExpr "tests/TestFiles/MatchesFunc1.hs" 400 "f"
        [RExists (\[x, y] -> getIntB x $ \x' -> getIntB y $ \y' ->  y' == 6 + x'), AtLeast 1]

    , checkExpr "tests/TestFiles/RecordFields1.hs" 400 "f"
        [ RExists 
            (\[x, y] -> appNthArgIs x notCast 0
                     && appNthArgIs x (\x' -> getIntB x' $ \x'' -> getIntB y $ \y' -> x'' + 1 == y') 1)
        , Exactly 1]
    , checkExpr "tests/TestFiles/RecordFields1.hs" 400 "fCall" [RExists (\[x] -> isInt x ((==) 35)), Exactly 1]
    , checkExpr "tests/TestFiles/RecordFields1.hs" 400 "g"
        [ RExists (\[x, y] -> appNthArgIs x (dcHasName "A") 2 && appNthArgIs y (dcHasName "B") 2)
        , RExists (\[x, y] -> appNthArgIs x (dcHasName "B") 2 && appNthArgIs y (dcHasName "C") 2)
        , RExists (\[x, y] -> appNthArgIs x (dcHasName "C") 2 && appNthArgIs y (dcHasName "A") 2)
        , Exactly 3]

    , checkInputOutputs "tests/TestFiles/Deriving/DerivingSimple.hs" [ ("eq", 400, [AtLeast  2])
                                                                     , ("lt", 400, [AtLeast 2]) ]
    , checkInputOutputs "tests/TestFiles/Deriving/DerivingComp.hs" [ ("eq", 800, [AtLeast 2])
                                                                   , ("lt", 800, [AtLeast 2]) ]

    , checkInputOutputs "tests/TestFiles/Coercions/Age.hs" [ ("born", 400, [Exactly 1])
                                                           , ("yearPasses", 400, [AtLeast 1])
                                                           , ("age", 400, [AtLeast 1])
                                                           , ("diffAge", 400, [AtLeast 1])
                                                           , ("yearBefore", 400, [AtLeast 5])]
    , checkInputOutputs "tests/TestFiles/Coercions/NewType1.hs" [ ("add1N4", 400, [Exactly 1])
                                                                , ("f", 400, [Exactly 1])
                                                                , ("g", 400, [Exactly 1])
                                                                , ("mapWInt", 400, [AtLeast 2])
                                                                , ("appLeftFloat", 400, [AtLeast 2])
                                                                , ("getLIntFloat", 400, [AtLeast 2])
                                                                , ("getRIntFloat", 400, [AtLeast 2])
                                                                , ("getCIntFloatDouble", 400, [AtLeast 2])
                                                                , ("getRIntFloatX'", 400, [AtLeast 2])]

    , checkInputOutput "tests/TestFiles/Coercions/BadCoerce.hs" "f" 400 [AtLeast 1]
    , checkInputOutput "tests/TestFiles/Expr.hs" "leadingLams" 400 [AtLeast 5]

    , checkExprAssume "tests/TestFiles/Subseq.hs" 1200 (Just "assume") "subseqTest" [AtLeast 1]

    , checkInputOutputs "tests/TestFiles/Strings/Strings1.hs" [ ("con", 300, [AtLeast 10])
                                                              , ("eq", 700, [AtLeast 10])
                                                              , ("eqGt1", 700, [AtLeast 10])
                                                              , ("capABC", 150, [AtLeast 10])
                                                              , ("appendEq", 500, [AtLeast 5]) ]

    , checkExpr "tests/TestFiles/Strings/Strings1.hs" 1000 "exclaimEq"
        [AtLeast 5, RExists (\[_, _, r] -> dcHasName "True" r)]

    , checkExpr "tests/TestFiles/Sets/SetInsert.hs" 700 "prop" [AtLeast 3]
    
    , checkInputOutputs "tests/TestFiles/BadDC.hs" [ ("f", 400, [AtLeast 5])
                                                   , ("g", 400, [AtLeast 3]) ]

    , checkInputOutputsTemplate "tests/HigherOrder/HigherOrder.hs" [ ("f", 50, [AtLeast 5])
                                                                   , ("h", 100, [AtLeast 3])
                                                                   , ("assoc", 200, [AtLeast 5])
                                                                   , ("sf", 150, [AtLeast 5])
                                                                   , ("thirdOrder", 75, [AtLeast 10])
                                                                   , ("tupleTestMono", 175, [AtLeast 10])]
    , checkInputOutputsTemplate "tests/HigherOrder/PolyHigherOrder.hs" [ ("f", 50, [AtLeast 5])
                                                                       , ("h", 200, [AtLeast 3])
                                                                       , ("assoc", 200, [AtLeast 5])
                                                                       , ("sf", 150, [AtLeast 5])
                                                                       , ("tupleTest", 175, [AtLeast 8])]
    -- , checkInputOutput "tests/TestFiles/BadBool.hs" "BadBool" "f" 1400 [AtLeast 1]
    -- , checkExprAssumeAssert "tests/TestFiles/Coercions/GADT.hs" 400 Nothing Nothing "g" 2
    --     [ AtLeast 2
    --     , RExists (\[x, y] -> x == Lit (LitInt 0) && y == App (Data (PrimCon I)) (Lit (LitInt 0)))
    --     , RExists (\[x, _] -> x /= Lit (LitInt 0))]
    -- , checkExprAssumeAssert "tests/TestFiles/HigherOrderList.hs" 400 Nothing Nothing "g" [AtLeast  10] 
    
    ]

extensionTests :: TestTree
extensionTests = testGroup "Extensions"
    [
      checkInputOutputs "tests/TestFiles/Extensions/PatternSynonyms1.hs" [ ("isNineInt", 400, [AtLeast 2])
                                                                         , ("isNineInteger", 400, [AtLeast 2])
                                                                         , ("isNineFloat", 400, [AtLeast 2])
                                                                         , ("isFunc", 400, [AtLeast 2])
                                                                         , ("funcArg", 400, [AtLeast 2])
                                                                         
                                                                         , ("consArrow", 400, [AtLeast 2]) ]
    , checkInputOutputs "tests/TestFiles/Extensions/ViewPatterns1.hs" [ ("shapeToNumSides", 4000, [Exactly 4]) ]
    , checkInputOutputs "tests/TestFiles/Extensions/MultiParamTypeClasses1.hs" [ ("total", 2000, [Exactly 8])
                                                                               , ("totalGen", 2000, [AtLeast 2])
                                                                               , ("totalGenNum", 2000, [Exactly 2])
                                                                               , ("total3", 2000, [AtLeast 8])
                                                                               , ("totalGen3", 2000, [AtLeast 2])
                                                                               , ("totalGenNum3", 2000, [AtLeast 2])
                                                                               , ("testG", 2000, [AtLeast 2]) ]
    ]

baseTests ::  TestTree
baseTests = testGroup "Base"
    [
      checkInputOutput "tests/Samples/Peano.hs" "add" 400 [AtLeast 4]

    , checkInputOutputs "tests/BaseTests/ListTests.hs" [ ("test", 1000, [AtLeast 1])
                                                       , ("maxMap", 1000, [AtLeast 4])
                                                       , ("minTest", 1000, [AtLeast 2])
                                                       , ("foldrTest2", 1000, [AtLeast 1]) ]

    , checkInputOutput "tests/BaseTests/Tuples.hs" "addTupleElems" 1000 [AtLeast 2]

    , checkInputOutputs "tests/BaseTests/MaybeTest.hs" [ ("headMaybeInt", 1000, [AtLeast 2])
                                                       , ("sumN", 1000, [AtLeast 6])
                                                       , ("lengthN", 1000, [AtLeast 6]) ]

    , checkInputOutput "tests/BaseTests/Other.hs" "check4VeryEasy2" 600 [AtLeast 1]
    ]

primTests :: TestTree
primTests = testGroup "Prims"
    [
      checkInputOutputs "tests/Prim/Prim2.hs" [ ("quotI1", 1000, [AtLeast 4])
                                              , ("quotI2", 1000, [AtLeast 4])
                                              , ("remI1", 1000, [AtLeast 4])
                                              , ("remI2", 1000, [AtLeast 3])
                                              , ("remI3", 1000, [AtLeast 1])
                                              , ("remI4", 1000, [AtLeast 1])

                                              , ("p1List", 300000, [AtLeast 1])
                                              , ("p2List", 700000, [AtLeast 1])

                                              , ("integerToFloatList", 150000, [AtLeast 1]) ]

    , checkInputOutputs "tests/Prim/Prim3.hs" [ ("int2FloatTest", 1000, [AtLeast 1])
                                              , ("int2DoubleTest", 1000, [AtLeast 1]) ]

    , checkInputOutputs "tests/Prim/Prim4.hs" [ ("divIntTest", 1500, [AtLeast 4])
                                              , ("divIntegerTest", 1500, [AtLeast 1])
                                              , ("divIntegerTest2", 1500, [AtLeast 4])
                                              , ("divFloatTest", 1500, [AtLeast 1]) ]

    , checkInputOutputs "tests/Prim/DataTag.hs" [ ("dataToTag1", 1000, [Exactly 1])
                                                , ("dataToTag2", 1000, [AtLeast 1])
                                                , ("dataToTag3", 1000, [Exactly 5])
                                                , ("tagToEnum1", 1000, [AtLeast 1])
                                                , ("tagToEnum3", 1000, [AtLeast 4])
                                                , ("tagToEnum4", 1000, [AtLeast 4])
                                                , ("tagToEnum5", 1000, [Exactly 1])
                                                , ("tagToEnum6", 1000, [AtLeast 4]) ]

    , checkExpr "tests/Prim/DataTag.hs" 1000 "tagToEnum2" [Exactly 1, RForAll (\[r] -> isError r)]

    , checkInputOutputs "tests/Prim/Chr.hs" [ ("lowerLetters", 9000, [AtLeast 1])
                                            , ("allLetters", 20000, [AtLeast 1])
                                            , ("printBasedOnChr", 1500, [AtLeast 7])
                                            , ("printBasedOnOrd", 1500, [AtLeast 7]) ]
    ]

-- To Do Tests
--------------

todoTests :: TestTree
todoTests = testGroup "To Do"
    [
      checkExpr "tests/TestFiles/TypeClass/TypeClass5.hs" 800 "run" [AtLeast 1]
    , checkExpr "tests/TestFiles/TypeClass/TypeClass5.hs" 800 "run2" [AtLeast 0]
    , checkInputOutput "tests/Prim/Prim2.hs" "sqrtList" 10000 [AtLeast 1]
    
    , checkInputOutputs "tests/BaseTests/MaybeTest.hs" [ ("average", 2000, [AtLeast 6])
                                                       , ("averageF", 2000, [AtLeast 6])
                                                       , ("maybeAvg", 200, [AtLeast 6])
                                                       ]

    , checkInputOutputs "tests/Prim/Prim3.hs" [ ("float2IntTest", 1000, [AtLeast 1])
                                              , ("double2IntTest", 1000, [AtLeast 1])]
    ]

data ToDo = RunMain
          | RunToDo
          deriving (Eq, Typeable)


instance IsOption ToDo where
    defaultValue = RunMain
    parseValue s =
        let
            ws = words s
        in
        if "y" `elem` ws || "yes" `elem` ws then Just RunToDo else Nothing
    optionName = Tagged "todo"
    optionHelp = Tagged "Specifies whether to run the main, passing tests, or the todo tests."

-- Generic helpers for tests
----------------------------

checkExpr :: String -> Int -> String -> [Reqs ([Expr] -> Bool)] -> TestTree
checkExpr src stps entry reqList =
    checkExprReaches src stps Nothing Nothing Nothing entry reqList

checkExprAssume :: String -> Int -> Maybe String -> String -> [Reqs ([Expr] -> Bool)] -> TestTree
checkExprAssume src stps m_assume entry reqList =
    checkExprReaches src stps m_assume Nothing Nothing entry reqList

checkExprAssert :: String -> Int -> Maybe String -> String -> [Reqs ([Expr] -> Bool)] -> TestTree
checkExprAssert src stps m_assert entry reqList =
    checkExprReaches src stps Nothing m_assert Nothing entry reqList

checkExprAssumeAssert :: String
                      -> Int
                      -> Maybe String
                      -> Maybe String
                      -> String
                      -> [Reqs ([Expr] -> Bool)]
                      -> TestTree
checkExprAssumeAssert src stps m_assume m_assert entry reqList =
    checkExprReaches src stps m_assume m_assert Nothing entry reqList

checkExprReaches :: String
                 -> Int
                 -> Maybe String
                 -> Maybe String
                 -> Maybe String
                 -> String
                 -> [Reqs ([Expr] -> Bool)]
                 -> TestTree
checkExprReaches src stps m_assume m_assert m_reaches entry reqList = do
    checkExprWithConfig src m_assume m_assert m_reaches entry reqList
            (do
                config <- mkConfigTestIO
                return $ config {steps = stps})

checkExprWithMap :: String
                 -> Int
                 -> Maybe String
                 -> Maybe String
                 -> Maybe String
                 -> String
                 -> [Reqs ([Expr] -> Bool)]
                 -> TestTree
checkExprWithMap src stps m_assume m_assert m_reaches entry reqList = do
    checkExprWithConfig src m_assume m_assert m_reaches entry reqList
            (do
                config <- mkConfigTestWithMapIO
                return $ config {steps = stps})

checkExprWithSet :: String
                 -> Int
                 -> Maybe String
                 -> Maybe String
                 -> Maybe String
                 -> String
                 -> [Reqs ([Expr] -> Bool)]
                 -> TestTree
checkExprWithSet src stps m_assume m_assert m_reaches entry reqList = do
    checkExprWithConfig src m_assume m_assert m_reaches entry reqList
            (do
                config <- mkConfigTestWithSetIO
                return $ config {steps = stps})

checkExprWithConfig :: String
                    -> Maybe String
                    -> Maybe String
                    -> Maybe String
                    -> String
                    -> [Reqs ([Expr] -> Bool)]
                    -> IO Config
                    -> TestTree
checkExprWithConfig src m_assume m_assert m_reaches entry reqList config_f = do
    testCase src (do
        config <- config_f
        res <- testFile src m_assume m_assert m_reaches entry config
        
        let ch = case res of
                    Left _ -> False
                    Right exprs -> null $ checkExprGen (map (\(inp, out) -> inp ++ [out]) exprs) reqList
        assertBool ("Assume/Assert for file " ++ src
                                    ++ " with functions [" ++ (fromMaybe "" m_assume) ++ "] "
                                    ++ "[" ++ (fromMaybe "" m_assert) ++ "] "
                                    ++  entry ++ " failed.\n")
                   ch
        )

    -- return . testCase src
    --     $ assertBool ("Assume/Assert for file " ++ src ++ 
    --                   " with functions [" ++ (fromMaybe "" m_assume) ++ "] " ++
    --                                   "[" ++ (fromMaybe "" m_assert) ++ "] " ++
    --                                           entry ++ " failed.\n") ch
 
testFile :: String
         -> Maybe String
         -> Maybe String
         -> Maybe String
         -> String
         -> Config
         -> IO (Either SomeException [([Expr], Expr)])
testFile src m_assume m_assert m_reaches entry config =
    try (testFileWithConfig src m_assume m_assert m_reaches entry config)

testFileWithConfig :: String
                   -> Maybe String
                   -> Maybe String
                   -> Maybe String
                   -> String
                   -> Config
                   -> IO [([Expr], Expr)]
testFileWithConfig src m_assume m_assert m_reaches entry config = do
    let proj = takeDirectory src
    r <- doTimeout (timeLimit config)
            $ runG2FromFile 
                [proj]
                [src]
                (fmap T.pack m_assume)
                (fmap T.pack m_assert)
                (fmap T.pack m_reaches)
                (isJust m_assert || isJust m_reaches)
                (T.pack entry)
                simplTranslationConfig
                config

    let (states, _) = maybe (error "Timeout") fst r
    return $ map (\(ExecRes { conc_args = i, conc_out = o}) -> (i, o)) states 

-- For mergeState unit tests
checkFn :: Either String Bool -> String -> IO TestTree
checkFn f testName = do
    let res = f
    case res of
       Left e -> return . testCase testName $ assertFailure e
       Right _ -> return . testCase testName $ return ()

checkFnIO :: IO (Either String Bool) -> String -> IO TestTree
checkFnIO f testName = do
    res <- f
    case res of
        Left e -> return . testCase testName $ assertFailure e
        Right _ -> return . testCase testName $ return ()

errors :: [Expr] -> Bool
errors e =
    case last e of
        Prim Error _ -> True
        _ -> False
