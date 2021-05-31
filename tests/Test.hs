{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Options
import Test.Tasty.Runners

import G2.Config

import G2.Interface
import G2.Language as G2
import G2.Liquid.Interface

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

import InputOutputTest
import Reqs
import TestUtils

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
        , liquidTests
        , testFileTests
        , baseTests
        , primTests
        , exprTests
        , typingTests
        , simplificationTests
        , ufMapQuickcheck
        , unionFindQuickcheck
        ]

timeout :: Timeout
timeout = mkTimeout 1

-- Test based on examples that are also good for demos
sampleTests :: TestTree
sampleTests = testGroup "Samples"
    [
      checkExprAssert "tests/Samples/Peano.hs" 900 (Just "equalsFour") "add" 3 
        [RForAll $ not . peano_4_out, AtLeast 10]
    , checkExprAssumeAssert "tests/Samples/Peano.hs" 900 (Just "fstIsEvenAddToFour") (Just "fstIsTwo") "add" 3
        [RExists peano_0_4, RExists peano_4_0, Exactly 2]
    , checkExprAssumeAssert "tests/Samples/Peano.hs" 1200 (Just "multiplyToFour") (Just "equalsFour") "add" 3 
        [RExists peano_1_4_5, RExists peano_4_1_5, Exactly 2]
    , checkExprAssumeAssert "tests/Samples/Peano.hs" 750 (Just "eqEachOtherAndAddTo4") Nothing "add" 3 
        [RForAll peano_2_2, Exactly 1]
    , checkExprAssumeAssert "tests/Samples/Peano.hs" 600 (Just "equalsFour") Nothing "add" 3 
        [ RExists peano_0_4
        , RExists peano_1_3
        , RExists peano_2_2
        , RExists peano_3_1
        , RExists peano_4_0
        , Exactly 5]
    , checkExprAssumeAssert "tests/Samples/Peano.hs" 750 (Just "equalsFour") Nothing "multiply" 3
        [ RExists peano_1_4
        , RExists peano_2_2
        , RExists peano_4_1
        , Exactly 3]

    , checkExprAssume "tests/Samples/HigherOrderMath.hs" 800 (Just "isTrue0") "notNegativeAt0NegativeAt1" 2
        [RExists negativeSquareRes, AtLeast 1]
    , checkExprAssume "tests/Samples/HigherOrderMath.hs" 600 (Just "isTrue1") "fixed" 3
        [ RExists abs2NonNeg
        , RExists squareRes
        , RExists fourthPowerRes
        , RForAll allabs2NonNeg
        , AtLeast 4]
    , checkExpr "tests/Samples/HigherOrderMath.hs" 600 "fixed" 3 [ RExists abs2NonNeg
                                                                 , RExists squareRes
                                                                 , RExists fourthPowerRes
                                                                 , AtLeast 4]
    , checkExprAssumeAssert "tests/Samples/HigherOrderMath.hs" 600 (Just "isTrue2") Nothing "sameFloatArgLarger" 3 
        [ RExists addRes
        , RExists subRes
        , AtLeast 2]
    , checkExpr "tests/Samples/HigherOrderMath.hs" 600 "functionSatisfies" 4 [RExists functionSatisfiesRes, AtLeast 1]
    , checkExpr "tests/Samples/HigherOrderMath.hs" 1000 "approxSqrt" 3 [AtLeast 2]
    -- The below test fails because Z3 returns unknown.
    -- , checkExprAssume "tests/Samples/HigherOrderMath.hs" 1200 (Just "isTrue2") "sameFloatArgLarger" 2
    --                                                             [ RExists approxSqrtRes
                                                                -- , RExists pythagoreanRes
                                                                -- , AtLeast 2]
    
    , checkExprAssumeAssert "tests/Samples/McCarthy91.hs" 1000 (Just "lessThan91") Nothing "mccarthy" 2
        [ RForAll (\[App _ (Lit (LitInt x)), _] -> x <= 100)
        , AtLeast 1]
    , checkExprAssumeAssert "tests/Samples/McCarthy91.hs" 400 (Just "greaterThan10Less") Nothing "mccarthy" 2 
        [ RForAll (\[App _ (Lit (LitInt x)), _] -> x > 100)
        , AtLeast 1]
    , checkExprAssumeAssert "tests/Samples/McCarthy91.hs" 1000 (Just "lessThanNot91") Nothing "mccarthy" 2 [Exactly 0]
    , checkExprAssumeAssert "tests/Samples/McCarthy91.hs" 1000 (Just "greaterThanNot10Less") Nothing "mccarthy" 2 
        [Exactly 0]

    , checkExpr "tests/Samples/GetNth.hs" 600 "getNth" 3 [AtLeast 10, RForAll getNthTest]
    , checkExpr "tests/Samples/GetNthPoly.hs" 600 "getNthInt" 3 [AtLeast 10, RForAll getNthErrTest]
    , checkExpr "tests/Samples/GetNthPoly.hs" 600 "getNthX" 3 [AtLeast 10, RForAll getNthErrGenTest]
    , checkExpr "tests/Samples/GetNthPoly.hs" 600 "getNthPeano" 3 [AtLeast 10, RForAll getNthErrGenTest]
    , checkExpr "tests/Samples/GetNthPoly.hs" 600 "getNthCListInt" 3 [AtLeast 10, RForAll getNthErrGenTest2']
    , checkExpr "tests/Samples/GetNthPoly.hs" 600 "getNthCListX" 3 [AtLeast 10, RForAll getNthErrGenTest2]
    , checkExpr "tests/Samples/GetNthPoly.hs" 1000 "getNth" 4 [AtLeast 10]

    , checkExpr "tests/Samples/GetNthPoly.hs" 1000 "cfmapInt" 3 [AtLeast 10, RForAll cfmapTest]
    , checkExpr "tests/Samples/GetNthPoly.hs" 1600 "cfmapIntX" 3 [AtLeast 10, RForAll cfmapTest]
    , checkExpr "tests/Samples/GetNthPoly.hs" 600 "cfmapIntCListInt" 3 [AtLeast 2, RForAll cfmapTest]

    , checkExprReaches "tests/Samples/GetNthErr.hs" 800 Nothing Nothing (Just "error") "getNth" 3
        [AtLeast 8, RForAll errors]

    , checkExpr "tests/Samples/FoldlUses.hs" 1600 "sum" 2 [AtLeast 3]
    , checkExpr "tests/Samples/FoldlUses.hs" 1000 "dotProd" 3 [AtLeast 3]

    , checkExpr "tests/Samples/FoldlUsesPoly.hs" 600 "sumMinAndMax" 5 [AtLeast 10]
    , checkExpr "tests/Samples/FoldlUsesPoly.hs" 400 "maxes" 7 [AtLeast 10]
    , checkExpr "tests/Samples/FoldlUsesPoly.hs" 400 "switchInt" 2 [AtLeast 1]
    , checkExpr "tests/Samples/FoldlUsesPoly.hs" 400 "getInInt" 2 [AtLeast 1]
    , checkExpr "tests/Samples/FoldlUsesPoly.hs" 400 "switchP" 6 [AtLeast 1]
    ]

liquidTests :: TestTree
liquidTests = testGroup "Liquid" 
    [
      checkLiquid "tests/Liquid/SimpleMath.hs" "abs2" 2000 2
        [RForAll (\[x, y] -> isDouble x ((==) 0) && isDouble y ((==) 0)), Exactly 1]
    , checkLiquid "tests/Liquid/SimpleMath.hs" "add" 800 3 
        [RForAll (\[x, y, z] -> isInt x $ \x' -> isInt y $ \y' -> isInt z $ \z' -> x' > z' || y' > z'), AtLeast 1]
    , checkLiquid "tests/Liquid/SimpleMath.hs" "subToPos" 1000 3 
        [ RForAll (\[x, y, z] -> isInt x $ \x' -> isInt y $ \y' -> isInt z $ \z' -> x' > 0 && x' >= y' && z' <= 0)
        , AtLeast 1]
    , checkLiquidWithNoCutOff "tests/Liquid/SimpleMath.hs" "fib" 4000 2
        [RForAll (\[x, y] -> isInt x $ \x' -> isInt y $ \y' -> x' > y'), AtLeast 3]
    , checkLiquidWithNoCutOff "tests/Liquid/SimpleMath.hs" "fib'" 6000 2
        [RForAll (\[x, y] -> isInt x $ \x' -> isInt y $ \y' -> x' > y'), AtLeast 3]
    , checkLiquid "tests/Liquid/SimpleMath.hs" "xSqPlusYSq" 1000 3 
        [RForAll (\[x, y, z] -> isInt x $ \x' -> isInt y $ \y' -> isInt z $ \z' -> x' + y' >= z'), AtLeast 1]

    , checkLiquid "tests/Liquid/SimplePoly.hs" "snd2Int" 800 3
        [ RForAll (\[x, y, z] -> isInt x $ \x' -> isInt y $ \y' -> isInt z $ \z' -> x' /= y' && y' == z')
        , Exactly 1]
    , checkLiquid "tests/Liquid/SimplePoly.hs" "sumPair" 800 2
        [ AtLeast 1
        , RForAll (\[App (App _ x) y, z] -> isInt x $ \x' -> isInt y $ \y' -> isInt z $ \z' ->  x' > z' || y' > z')]
    , checkLiquid "tests/Liquid/SimplePoly.hs" "switchInt" 600 2
        [ Exactly 1
        , RForAll (\[App (App _ x) _, App (App _ _) y] -> getIntB x $ \ x' -> getIntB y $ \ y' -> x' == y')]

    , checkLiquid "tests/Liquid/Peano.hs" "add" 1400 3
        [RForAll (\[x, y, _] -> x `eqIgT` zeroPeano || y `eqIgT` zeroPeano), AtLeast 5]
    , checkLiquid "tests/Liquid/Peano.hs" "fromInt" 600 2
        [RForAll (\[x, y] -> isInt x (\x' -> x' == 0)  && y `eqIgT` zeroPeano), AtLeast 1]

    , checkLiquidWithNoCutOff "tests/Liquid/GetNth.hs" "getNthInt" 2700 3 [AtLeast 3, RForAll getNthErrors]
    , checkLiquidWithCutOff "tests/Liquid/GetNth.hs" "sumC" 2000 1000 2
        [AtLeast 3, RForAll (\[_, y] -> isInt y $ (==) 0)]
    , checkLiquidWithNoCutOff "tests/Liquid/GetNth.hs" "getNth" 2700 4 [AtLeast 3]
    , checkLiquidWithCutOff "tests/Liquid/GetNth.hs" "sumCList" 2000 1000 4 [AtLeast 3]

    , checkLiquid "tests/Liquid/DataRefTest.hs" "addMaybe" 1000 3 
        [AtLeast 1, RForAll (\[_, y, z] -> isInt y $ \y' -> appNthArgIs z (\z' -> isInt z' $ \z'' -> z'' <= y') 2)]
    , checkLiquid "tests/Liquid/DataRefTest.hs" "addMaybe2" 2000 3
        [AtLeast 1, RForAll (\[x, _, _] -> appNthArgIs x (\x' -> isInt x' $ \x'' -> x'' >= 0) 2)
                  , RForAll (\[_, y, z] -> isInt y $ \y' -> appNthArgIs z (\z' -> isInt z' $ \z'' -> z'' <= y') 2)]
    , checkLiquid "tests/Liquid/DataRefTest.hs" "getLeftInts" 2000 2 
        [AtLeast 1, RForAll (\[x, _] -> dcInAppHasName "Right" x 3)]
    , checkLiquid "tests/Liquid/DataRefTest.hs" "sumSameInts" 2000 3 
        [AtLeast 1, RForAll (\[x, y, _] -> dcInAppHasName "Right" x 3 && dcInAppHasName "Left" y 3)]
    , checkLiquid "tests/Liquid/DataRefTest.hs" "sub1" 1200 4 [AtLeast 1]

    , checkLiquid "tests/Liquid/NumOrd.hs" "subTuple" 1200 3 [AtLeast 1]

    , checkLiquid "tests/Liquid/CommentMeasures.hs" "d" 1000 2 [AtLeast 1]
    , checkLiquid "tests/Liquid/CommentMeasures.hs" "unpackCP'" 100000 2 [Exactly 0]
    , checkLiquid "tests/Liquid/CommentMeasures.hs" "unpackBool" 1000 2
        [AtLeast 1, RForAll (\[_, r] -> getBoolB r (== False))]
    , checkLiquid "tests/Liquid/CommentMeasures.hs" "sumSameOneOfs" 100000 3 [Exactly 0]
    , checkLiquid "tests/Liquid/CommentMeasures.hs" "gets2As" 2000 3 
        [AtLeast 1, RExists (\[x, y, _] -> buriedDCName "B" x && buriedDCName "B" y)]
    , checkLiquid "tests/Liquid/CommentMeasures.hs" "gets2As'" 1000 3 
        [AtLeast 1, RExists (\[x, y, _] -> buriedDCName "A" x && buriedDCName "B" y)
                  , RExists (\[x, y, _] -> buriedDCName "B" x && buriedDCName "A" y)]
    , checkLiquid "tests/Liquid/CommentMeasures.hs" "ge4gt5" 1000 2 
        [AtLeast 1, RForAll (\[x, y] -> appNth x 1 $ \x' -> isInt x' $ \x'' -> isInt y $ \y' ->  x'' == 4 && y' == 5)]

    , checkLiquid "tests/Liquid/ConcatList.hs" "concat2" 800 3 [AtLeast 2]
    , checkLiquid "tests/Liquid/ConcatList.hs" "concat3" 800 3 [AtLeast 2]
    , checkLiquid "tests/Liquid/ConcatList.hs" "concat5" 1600 3 [AtLeast 1]

    , checkLiquidWithMap "tests/Liquid/Tests/Group3.lhs" "f" 2200 1 [AtLeast 1]

    , checkLiquid "tests/Liquid/Nonused.hs" "g" 2000 1 [AtLeast 1]

    -- , checkLiquid "tests/Liquid/HigherOrderRef.hs" "f1" 2000 3 [Exactly 0]
    -- , checkLiquid "tests/Liquid/HigherOrderRef.hs" "f2" 2000 3 [AtLeast 4, RForAll (\[_, x, y] -> x == y)]
    -- , checkLiquid "tests/Liquid/HigherOrderRef.hs" "f3" 2000 3 [Exactly 0]
    -- , checkLiquid "tests/Liquid/HigherOrderRef.hs" "f4" 2000 3
    --     [AtLeast 4, RForAll (\[_, x, _] -> isInt x $ \x' -> x' == 0)]
    -- , checkLiquid "tests/Liquid/HigherOrderRef.hs" "f5" 2000 3 [Exactly 0]
    -- , checkLiquid "tests/Liquid/HigherOrderRef.hs" "f6" 2000 3 [AtLeast 10]
    -- , checkLiquid "tests/Liquid/HigherOrderRef.hs" "f7" 2000 3 
    --    [AtLeast 10, RForAll (\[x, _, y] -> isInt x $ \x' -> isInt y $ \y' -> x' == y')]
    -- , checkLiquid "tests/Liquid/HigherOrderRef.hs" "f8" 2000 3 [AtLeast 10]
    -- , checkLiquid "tests/Liquid/HigherOrderRef.hs" "callf" 2000 3 [AtLeast 1]

    -- , checkLiquid "tests/Liquid/Error/Error1.hs" "f" 600 2 [AtLeast 1]
    , checkLiquid "tests/Liquid/Error/Error2.hs" "f1" 2000 4 [AtLeast 1]
    , checkLiquid "tests/Liquid/ZipWith.lhs" "distance" 1000 4 [AtLeast 3]

    , checkLiquid "tests/Liquid/HigherOrder2.hs" "f" 2000 2 [Exactly 0]
    , checkLiquid "tests/Liquid/HigherOrder2.hs" "h" 2000 2 [AtLeast 1]
    , checkLiquid "tests/Liquid/HigherOrder3.hs" "m" 600 2 [AtLeast 1]

    , checkLiquid "tests/Liquid/Ordering.hs" "oneOrOther" 1000 2 [Exactly 0]

    , checkLiquid "tests/Liquid/AddKV.lhs" "empty" 1000 3 [Exactly 0]

    , checkLiquid "tests/Liquid/PropSize.hs" "prop_size" 2000 1 [AtLeast 1]
    , checkLiquid "tests/Liquid/PropSize2.hs" "prop_size" 2000 1 [AtLeast 1]

    , checkLiquidWithMap "tests/Liquid/WhereFuncs.lhs" "f" 1000 3 [Exactly 0]
    , checkLiquidWithMap "tests/Liquid/WhereFuncs.lhs" "g" 1000 3 [Exactly 0]

    , checkLiquid "tests/Liquid/PropConcat.lhs" "prop_concat" 1000 1 [AtLeast 1]

    , checkLiquid "tests/Liquid/Distance.lhs" "distance" 1000 4 [AtLeast 1]
    , checkLiquid "tests/Liquid/MultModules/CallZ.lhs" "callZ" 1000 3 [AtLeast 1]
    , checkAbsLiquid "tests/Liquid/AddToEven.hs" "f" 2500 1
        [ AtLeast 1
        , RForAll $ \[i] r [(FuncCall { funcName = Name n _ _ _, returns = fcr }) ]
            -> n == "g"
                && isInt i (\i' -> i' `mod` 2 == 0  &&
                                    isInt r (\r' -> isInt fcr (\fcr' -> r' == i' + fcr')))]
    , checkAbsLiquid "tests/Liquid/AddToEven4.hs" "f" 2000 1 [ AtLeast 1]

    , checkAbsLiquid "tests/Liquid/Concat.hs" "prop_concat" 1000 0 [ AtLeast 1]

    , checkLiquid "tests/Liquid/ListTests.lhs" "r" 1000 1 [Exactly 0]
    , checkLiquid "tests/Liquid/ListTests.lhs" "prop_map" 1500 3 [AtLeast 3]
    , checkLiquid "tests/Liquid/ListTests.lhs" "prop_concat_1" 1500 1 [AtLeast 1]
    , checkAbsLiquid "tests/Liquid/ListTests2.lhs" "prop_map" 2000 4
        [ AtLeast 2
        , RForAll (\[_, _, f, _] _ [(FuncCall { funcName = Name n _ _ _, arguments = [_, _, _, _, f', _] }) ] -> 
                    n == "map" && f == f') ]
    , checkAbsLiquid "tests/Liquid/ListTests2.lhs" "prop_size" 2000 0
        [ AtLeast 1
        , RForAll (\[] _ [(FuncCall { funcName = Name n _ _ _, returns = r }) ]
            -> n == "length2" && getIntB r (/= 3)) ]

    , checkLiquid "tests/Liquid/MapReduceTest2.lhs" "mapReduce" 1500 3 [Exactly 0]

    , checkLiquid "tests/Liquid/MeasErr.hs" "f" 1500 2 [Exactly 0]

    , checkAbsLiquid "tests/Liquid/Replicate.hs" "replicate" 2000 3
        [ AtLeast 1
        , RExists (\_ _ [(FuncCall { funcName = Name n _ _ _ }) ] -> n == "foldl") ]
    , checkAbsLiquid "tests/Liquid/Replicate.hs" "r" 2000 2
        [ AtLeast 1
        , RExists (\_ _ [(FuncCall { funcName = Name n _ _ _ }) ] -> n == "foldl") ]

    , checkAbsLiquid "tests/Liquid/AbsTypeClass.hs" "callF" 1000 1
        [ AtLeast 1
        , RExists (\_ _ [(FuncCall { funcName = Name n _ _ _ }) ] -> n == "f") ]
    , checkAbsLiquid "tests/Liquid/AbsTypeClassVerified.hs" "callF" 10000 1 [ Exactly 0 ]

    , checkLiquid "tests/Liquid/Tree.hs" "sumPosTree" 1000 2 [AtLeast 1]
    , checkLiquid "tests/Liquid/Error4.hs" "extractRights" 1000 1 [AtLeast 1]
    , checkLiquid "tests/Liquid/PostFalse.hs" "f" 2000 1 [AtLeast 1]

    , checkLiquid "tests/Liquid/TypeSym.hs" "f" 500 1 []

    , checkLiquid "tests/Liquid/CorrectDict.hs" "f" 2000 2 [AtLeast 1]

    , checkAbsLiquid "tests/Liquid/ZipWith3.hs" "prop_zipWith" 400 1 [ AtLeast 3]

    , checkAbsLiquid "tests/Liquid/Length.hs" "prop_size" 1000 0
        [ AtLeast 1
        , RForAll (\_ _ [ _ ]  -> True)]

    , checkLiquidWithConfig "tests/Liquid/NestedLength.hs" "nested" 2 [AtLeast 1]
                            (do config <- mkConfigTestIO; return $ config {add_tyvars = True})
    , checkLiquidWithConfig "tests/Liquid/AddTyVars.hs" "f" 3 [AtLeast 1]
                            (do config <- mkConfigTestIO; return $ config {add_tyvars = True, steps = 400}) 
    , checkLiquidWithConfig "tests/Liquid/AddTyVars.hs" "g" 3 [AtLeast 1]
                            (do config <- mkConfigTestIO; return $ config {add_tyvars = True, steps = 400}) 
    , checkLiquidWithConfig "tests/Liquid/AddTyVars.hs" "h" 3[AtLeast 1]
                            (do config <- mkConfigTestIO; return $ config {add_tyvars = True, steps = 400}) 

    , checkLiquid "tests/Liquid/Polymorphism/Poly1.hs" "f" 1000 1 [Exactly 0]
    , checkLiquid "tests/Liquid/Polymorphism/Poly2.hs" "f" 600 1 [Exactly 0]

    , checkLiquidWithSet "tests/Liquid/Sets/Sets1.hs" "prop_union_assoc" 2500 6 [AtLeast 3]
    , checkLiquidWithSet "tests/Liquid/Sets/Sets1.hs" "prop_intersection_comm" 1000 5 [AtLeast 5]
    , checkLiquidWithSet "tests/Liquid/Sets/Sets2.hs" "badIdList" 1000 4 [AtLeast 1]
    , checkLiquidWithSet "tests/Liquid/Sets/Sets2.hs" "append" 1000 5 [AtLeast 1]
    , checkLiquidWithSet "tests/Liquid/Sets/Sets3.hs" "filter" 1800 3 [AtLeast 1]

    -- Abstract counterexamples
    , checkAbsLiquid "tests/Liquid/Polymorphism/Poly3.hs" "f" 800 1
        [ AtLeast 4
        , RForAll (\_ _ [ FuncCall { funcName = Name n _ _ _} ]  -> n == "fil")]
    , checkLiquid "tests/Liquid/Polymorphism/Poly4.hs" "f" 600 1 [Exactly 0]
    , checkAbsLiquid "tests/Liquid/Polymorphism/Poly5.hs" "call" 600 1 [AtLeast 1]
    , checkAbsLiquid "tests/Liquid/Polymorphism/Poly6.hs" "f" 1000 1
        [ AtLeast 1
        , RForAll (\_ _ [ FuncCall { returns = r } ] ->
                    case r of { Prim Undefined _-> False; _ -> True})
        ]
    , checkAbsLiquid "tests/Liquid/Polymorphism/Poly7.hs" "prop_f" 2000 1 [AtLeast 1]
    , checkAbsLiquid "tests/Liquid/Polymorphism/Poly8.hs" "prop" 2000 0
        [ AtLeast 1
        , RForAll (\_ _ [ FuncCall { funcName = Name n _ _ _ } ] -> n == "func")]
    , checkAbsLiquid "tests/Liquid/Polymorphism/Poly9.hs" "prop" 2000 0
        [ AtLeast 1
        , RForAll (\_ _ [ FuncCall { funcName = Name n _ _ _ } ] -> n == "func")]
    , checkAbsLiquid "tests/Liquid/Polymorphism/Poly10.hs" "prop" 2000 0
        [ AtLeast 1 ]
    , checkAbsLiquid "tests/Liquid/Polymorphism/Poly11.hs" "call" 700 1
        [ AtLeast 1
        , RForAll (\_ _ [ FuncCall { funcName = Name n _ _ _ } ] -> n == "higher")]
    , checkAbsLiquid "tests/Liquid/Polymorphism/Poly12.hs" "prop" 3000 1
        [ AtLeast 1
        , RForAll (\_ _ [ FuncCall { funcName = Name n _ _ _ } ] -> n == "map")]
    , checkAbsLiquid "tests/Liquid/Polymorphism/Poly13.hs" "call" 1000 0
        [ AtLeast 1
        , RForAll (\_ _ [ FuncCall { funcName = Name n _ _ _ } ] -> n == "f")]
    , checkAbsLiquid "tests/Liquid/Polymorphism/Poly14.hs" "initCall" 1000 0 [ AtLeast 1]
    , checkAbsLiquid "tests/Liquid/Polymorphism/Poly15.hs" "call" 1000 0 [ AtLeast 1]
    , checkAbsLiquid "tests/Liquid/Polymorphism/Poly16.hs" "call" 1000 2 
        [ AtLeast 1
        , RForAll (\ _ _ [ FuncCall { arguments = [_, _, a] } ] -> case a of Prim _ _ -> False; _ -> True )]
    , checkAbsLiquid "tests/Liquid/Polymorphism/Poly17.hs" "empty2" 1000 1 [ AtLeast 1]
    , checkAbsLiquid "tests/Liquid/Polymorphism/Poly18.hs" "f" 500 1 [ AtLeast 1]
    ]

-- Tests that are intended to ensure a specific feature works, but that are not neccessarily interesting beyond that
testFileTests :: TestTree
testFileTests = testGroup "TestFiles"
    [
      checkExpr "tests/TestFiles/IfTest.hs" 400 "f" 3
        [ RForAll (\[App _ (Lit (LitInt x)), App _ (Lit (LitInt y)), App _ (Lit (LitInt r))] -> 
            if x == y then r == x + y else r == y)
        , AtLeast 2]

    , checkExprAssert "tests/TestFiles/AssumeAssert.hs" 400 (Just "assertGt5") "outShouldBeGt5" 2 [Exactly 0]
    , checkExprAssert "tests/TestFiles/AssumeAssert.hs" 400 (Just "assertGt5") "outShouldBeGe5" 2 [AtLeast 1]
    , checkExprAssumeAssert "tests/TestFiles/AssumeAssert.hs" 400
        (Just "assumeGt5") (Just "assertGt5") "outShouldBeGt5" 2 [Exactly 0]
    , checkExprAssumeAssert "tests/TestFiles/AssumeAssert.hs" 400
        (Just "assumeGt5") (Just "assertGt5") "outShouldBeGe5" 2 [Exactly 0]

    , checkExpr "tests/TestFiles/CheckSq.hs" 400 "checkSq" 2 
        [AtLeast 2, RExists (\[x, _] -> isInt x (\x' -> x' == 3))]

    , checkExpr "tests/TestFiles/Defunc1.hs" 400 "f" 2
        [RExists defunc1Add1, RExists defunc1Multiply2, RExists defuncB, AtLeast 3]
    , checkExpr "tests/TestFiles/Defunc1.hs" 400 "x" 2 [AtLeast 1]
    , checkExpr "tests/TestFiles/Defunc1.hs" 600 "mapYInt" 3 [AtLeast 1]
    , checkExpr "tests/TestFiles/Defunc1.hs" 600 "makeMoney" 3 [AtLeast 2]
    , checkExpr "tests/TestFiles/Defunc1.hs" 1600 "compZZ" 4 [AtLeast 2, RForAll (\[_, _, _, x] -> getBoolB x not)]
    , checkExpr "tests/TestFiles/Defunc1.hs" 1600 "compZZ2" 4 [AtLeast 2, RForAll (\[_, _, _, x] -> getBoolB x not)]

    , checkExpr "tests/TestFiles/Defunc2.hs" 400 "funcMap" 3 [RForAll defunc2Check, AtLeast 30]

    , checkExpr "tests/TestFiles/MultCase.hs" 400 "f" 2
        [ RExists (\[App _ (Lit (LitInt x)), y] -> x == 2 && getBoolB y id)
        , RExists (\[App _ (Lit (LitInt x)), y] -> x == 1 && getBoolB y id)
        , RExists (\[App _ (Lit (LitInt x)), y] -> x /= 2 && x /= 1 && getBoolB y not)]

    , checkExprAssumeAssert "tests/TestFiles/LetFloating/LetFloating.hs" 400 (Just "output6") Nothing "f" 2
        [AtLeast 1, RExists (\[App _ (Lit (LitInt x)), _] -> x == 6)]
    , checkExprAssumeAssert "tests/TestFiles/LetFloating/LetFloating2.hs" 400 (Just "output16") Nothing "f" 2
        [AtLeast 1, RExists (\[App _ (Lit (LitInt x)), _] -> x == 15)]
    , checkExprAssumeAssert "tests/TestFiles/LetFloating/LetFloating3.hs" 600 (Just "output32") Nothing "f" 2
        [AtLeast 1, RExists (\[App _ (Lit (LitInt x)), _] -> x == 4)]
    , checkExprAssumeAssert "tests/TestFiles/LetFloating/LetFloating4.hs" 400 (Just "output12") Nothing "f" 2
        [AtLeast 1, RExists (\[App _ (Lit (LitInt x)), _] -> x == 11)]
    , checkExprAssumeAssert "tests/TestFiles/LetFloating/LetFloating5.hs" 400 (Just "output19") Nothing "f" 3
        [AtLeast 1, RForAll (\[App _ (Lit (LitInt x)), App _ (Lit (LitInt y)), _] -> x + y + 1 == 19)]
    , checkExprAssumeAssert "tests/TestFiles/LetFloating/LetFloating6.hs" 400 (Just "output32") Nothing "f" 2
        [AtLeast 1, RExists (\[App _ (Lit (LitInt x)), _] -> x == 25)]

    , checkExpr "tests/TestFiles/TypeClass/TypeClass1.hs" 400 "f" 2 [RExists (\[x, y] -> x == y), Exactly 1]
    , checkExpr "tests/TestFiles/TypeClass/TypeClass2.hs" 400 "f" 2 [RExists (\[x, y] -> x == y), Exactly 1]
    , checkExpr "tests/TestFiles/TypeClass/TypeClass3.hs" 400 "f" 2
        [RExists (\[x, y] -> getIntB x $ \x' -> getIntB y $ \y' -> x' + 8 == y'), Exactly 1]
    , checkExprWithMap "tests/TestFiles/TypeClass/TypeClass4.hs" 1000 Nothing Nothing Nothing "f" 1 [AtLeast 1]

    , checkExprAssumeAssert "tests/TestFiles/TypeClass/HKTypeClass1.hs" 400 (Just "largeJ") Nothing "extractJ" 2 
        [RForAll (\[x, ly@(App _ (Lit (LitInt y)))] -> appNthArgIs x (ly ==) 2 && y > 100), Exactly 1]
    , checkExprAssumeAssert "tests/TestFiles/TypeClass/HKTypeClass1.hs" 400 (Just "largeE") Nothing "extractE" 2
        [RForAll (\[x, ly@(App _ (Lit (LitInt y)))] -> appNthArgIs x (ly ==) 4 && y > 100), Exactly 1]
    , checkExpr "tests/TestFiles/TypeClass/HKTypeClass1.hs" 400 "changeJ" 3
        [RForAll (\[_, x, y] -> dcInAppHasName "J" x 2 && (dcInAppHasName "J" y 2 || isError y)), AtLeast 2]

    , checkExpr "tests/TestFiles/Case1.hs" 400 "f" 2
        [ RExists (\[App _ (Lit (LitInt x)), y] -> x < 0 && dcHasName "A" y)
        , RExists (\[App _ (Lit (LitInt x)), y] -> x >= 0 && dcHasName "C" y), Exactly 2]
    , checkExpr "tests/TestFiles/Case2.hs" 400 "f" 2 
        [ RExists exists1
        , RExists exists2
        , RExists exists3
        , RExists exists4
        , AtLeast 4]

    , checkExprAssumeAssert "tests/TestFiles/Guards.hs" 400 (Just "g") Nothing "f" 2
        [AtLeast 1, RExists (\[dc, _] -> getBoolB dc id)]

    , checkExprAssumeAssert "tests/TestFiles/Infinite.hs" 400 (Just "g") Nothing "f" 2
        [AtLeast 1, RExists (\[App _ (Lit (LitInt x)), _] -> x <= 100 && x /= 80)]

    , checkExpr "tests/TestFiles/Strictness1.hs" 400 "f" 1
        [AtLeast 1, RExists (\[(App x (App _ (Lit (LitInt y))))] -> dcHasName "A" x && y == 9)]

    , checkExpr "tests/TestFiles/Where1.hs" 400 "f" 2
        [ RExists (\[App _ (Lit (LitInt x)), App _ (Lit (LitInt y))] -> x == 4 && y == 1)
        , RExists (\[App _ (Lit (LitInt x)), App _ (Lit (LitInt y))] -> x /= 4 && y == 1) ]
    
    , checkExpr "tests/TestFiles/Error/Error1.hs" 400 "f" 2 [AtLeast 1, RForAll(errors)]
    , checkExpr "tests/TestFiles/Error/Error1.hs" 400 "g" 2 [AtLeast 1, RForAll(errors)]
    , checkExpr "tests/TestFiles/Error/Error2.hs" 400 "f" 1 [AtLeast 1, RForAll(errors)]
    , checkExpr "tests/TestFiles/Error/Error3.hs" 400 "f" 2 [AtLeast 1, RForAll(errors)]
    , checkExpr "tests/TestFiles/Error/Error3.hs" 400 "g" 2 [AtLeast 1, RForAll(not . errors)]
    , checkExpr "tests/TestFiles/Error/Undefined1.hs" 400 "undefined1" 2 [AtLeast 1, RForAll(errors)]
    , checkExpr "tests/TestFiles/Error/Undefined1.hs" 400 "undefined2" 2 [AtLeast 1, RForAll(errors)]

    , checkExpr "tests/TestFiles/BadNames1.hs" 400 "abs'" 2 [Exactly 2]
    , checkExpr "tests/TestFiles/BadNames1.hs" 400 "xswitch" 2 [AtLeast 10]

    , checkExpr "tests/TestFiles/PolyDataTy1.hs" 400 "f" 3
        [Exactly 2, RExists (\[x, _, y] -> x == y), RExists (\[_, App _ x, y] -> x == y)]
    , checkExpr "tests/TestFiles/PolyDataTy1.hs" 400 "getFstXIntInt" 2
        [AtLeast 2, RExists (\[x, y] -> isApp x && isError y)]
    , checkExpr "tests/TestFiles/PolyDataTy1.hs" 400 "sum" 2 [AtLeast 3, RExists (\[x, y] -> isApp x && isError y)]

    , checkExprAssumeAssert "tests/TestFiles/MultiSplit.hs" 1000 (Just "equals1") Nothing "f" 3 [Exactly 0]

    , checkExpr "tests/TestFiles/MatchesFunc1.hs" 400 "f" 2
        [RExists (\[x, y] -> getIntB x $ \x' -> getIntB y $ \y' ->  y' == 6 + x'), AtLeast 1]

    , checkExpr "tests/TestFiles/RecordFields1.hs" 400 "f" 2
        [ RExists 
            (\[x, y] -> appNthArgIs x notCast 0
                     && appNthArgIs x (\x' -> getIntB x' $ \x'' -> getIntB y $ \y' -> x'' + 1 == y') 1)
        , Exactly 1]
    , checkExpr "tests/TestFiles/RecordFields1.hs" 400 "fCall" 1 [RExists (\[x] -> isInt x ((==) 35)), Exactly 1]
    , checkExpr "tests/TestFiles/RecordFields1.hs" 400 "g" 2
        [ RExists (\[x, y] -> appNthArgIs x (dcHasName "A") 2 && appNthArgIs y (dcHasName "B") 2)
        , RExists (\[x, y] -> appNthArgIs x (dcHasName "B") 2 && appNthArgIs y (dcHasName "C") 2)
        , RExists (\[x, y] -> appNthArgIs x (dcHasName "C") 2 && appNthArgIs y (dcHasName "A") 2)
        , Exactly 3]

    , checkExpr "tests/TestFiles/Deriving/DerivingSimple.hs" 400 "eq" 3 [AtLeast  2, RForAll (\[_, _, x] -> isBool x)]
    , checkExpr "tests/TestFiles/Deriving/DerivingSimple.hs" 400 "lt" 3 [AtLeast 2, RForAll (\[_, _, x] -> isBool x)]
    , checkExpr "tests/TestFiles/Deriving/DerivingComp.hs" 800 "eq" 3 [AtLeast 2, RForAll (\[_, _, x] -> isBool x)]
    , checkExpr "tests/TestFiles/Deriving/DerivingComp.hs" 800 "lt" 3 [AtLeast 2, RForAll (\[_, _, x] -> isBool x)]

    , checkExpr "tests/TestFiles/Coercions/Age.hs" 400 "born" 1
        [ Exactly 1
        , RForAll (\[x] -> inCast x 
                            (\x' -> appNthArgIs x' (Lit (LitInt 0) ==) 1) 
                            (\(t1 :~ t2) -> isIntT t1 && typeNameIs t2 "Age"))]
    , checkExpr "tests/TestFiles/Coercions/Age.hs" 400 "yearPasses" 2
        [ AtLeast 1
        , RForAll (\[x, y] -> inCast x (const True) (\(_ :~ t2) -> typeNameIs t2 "Age")
                           && inCast y (const True) (\(_ :~ t2) -> typeNameIs t2 "Age") )]
    , checkExpr "tests/TestFiles/Coercions/Age.hs" 400 "age" 2
        [ AtLeast 1
        , RForAll (\[x, y] -> inCast x (const True) (\(_ :~ t2) -> typeNameIs t2 "Age") && isInt y (const True))]
    , checkExpr "tests/TestFiles/Coercions/Age.hs" 400 "diffAge" 3
        [ AtLeast 1
        , RForAll (\[x, y, z] -> inCast x (const True) (\(_ :~ t2) -> typeNameIs t2 "Age") 
                              && inCast y (const True) (\(_ :~ t2) -> typeNameIs t2 "Age")
                              && inCast z (const True) (\(_ :~ t2) -> typeNameIs t2 "Years"))]
    , checkExpr "tests/TestFiles/Coercions/Age.hs" 400 "yearBefore" 2 [ AtLeast 5 ]
    , checkExpr "tests/TestFiles/Coercions/NewType1.hs" 400 "add1N4" 2
        [ Exactly 1
        , RForAll (\[x, y] -> inCast x (const True) (\(_ :~ t2) -> typeNameIs t2 "N4") 
                           && inCast y (const True) (\(_ :~ t2) -> typeNameIs t2 "N4"))]
    , checkExpr "tests/TestFiles/Coercions/NewType1.hs" 400 "f" 2
        [ Exactly 1
        , RForAll (\[x, y] -> inCast x (const True) (\(_ :~ t2) -> typeNameIs t2 "NewX") && dcHasName "X" y)]
    , checkExpr "tests/TestFiles/Coercions/NewType1.hs" 400 "g" 2
        [ Exactly 1
        , RForAll (\[x, y] -> dcHasName "X" x && inCast y (const True) (\(_ :~ t2) -> typeNameIs t2 "NewX"))]

    , checkExpr "tests/TestFiles/Coercions/NewType1.hs" 400 "mapWInt" 3
        [ AtLeast 2
        , RForAll (\[_, x, y] -> isError y
                             || (inCast x (const True) (\(_ :~ t2) -> typeNameIs t2 "W")
                             &&  inCast x (const True) (\(_ :~ t2) -> typeNameIs t2 "W"))) ]

    , checkExpr "tests/TestFiles/Coercions/NewType1.hs" 400 "appLeftFloat" 3
        [ AtLeast 2
        , RExists (\[_, _, y] -> inCast y (\y' -> dcInAppHasName "L" y' 3) (const True))
        , RExists (\[_, _, y] -> inCast y (\y' -> dcInAppHasName "R" y' 3) (const True))]
    , checkExpr "tests/TestFiles/Coercions/NewType1.hs" 400 "getLIntFloat" 2
        [ AtLeast 2
        , RExists (\[_, y] -> isInt y (const True))
        , RExists (\[_, y] -> isError y)]
    , checkExpr "tests/TestFiles/Coercions/NewType1.hs" 400 "getRIntFloat" 2 
        [ AtLeast 2
        , RExists (\[_, y] -> isFloat y (const True))
        , RExists (\[_, y] -> isError y)]
    , checkExpr "tests/TestFiles/Coercions/NewType1.hs" 400 "getCIntFloatDouble" 2
        [ AtLeast 2
        , RExists (\[_, y] -> isFloat y (const True))
        , RExists (\[_, y] -> isError y)]
    , checkExpr "tests/TestFiles/Coercions/NewType1.hs" 400 "getRIntFloatX'" 2 
        [ AtLeast 2
        , RExists (\[x, y] -> inCast x (\x' -> dcInAppHasName "TR" x' 4) (const True)
                          && isInt y (const True))
        , RExists (\[_, y] -> isError y)]
    , checkInputOutput "tests/TestFiles/Coercions/BadCoerce.hs" "BadCoerce" "f" 400 3 [AtLeast 1]
    , checkExpr "tests/TestFiles/Expr.hs" 400 "leadingLams" 2 [AtLeast 5, RForAll (\[_, y] -> noUndefined y)]

    , checkInputOutput "tests/TestFiles/Strings/Strings1.hs" "Strings1" "con" 300 3 [AtLeast 10]
    , checkInputOutput "tests/TestFiles/Strings/Strings1.hs" "Strings1" "eq" 700 3 [AtLeast 10]
    , checkInputOutput "tests/TestFiles/Strings/Strings1.hs" "Strings1" "eqGt1" 700 3 [AtLeast 10]
    , checkInputOutput "tests/TestFiles/Strings/Strings1.hs" "Strings1" "capABC" 150 2 [AtLeast 10]
    , checkInputOutput "tests/TestFiles/Strings/Strings1.hs" "Strings1" "appendEq" 500 2 [AtLeast 5]
    , checkExpr "tests/TestFiles/Strings/Strings1.hs" 1000 "exclaimEq" 3
        [AtLeast 5, RExists (\[_, _, r] -> dcHasName "True" r)]
    
    , checkInputOutput "tests/TestFiles/BadDC.hs" "BadDC" "f" 400 2 [AtLeast 5]
    , checkInputOutput "tests/TestFiles/BadDC.hs" "BadDC" "g" 400 2 [AtLeast 3]
    -- , checkInputOutput "tests/TestFiles/BadBool.hs" "BadBool" "f" 1400 4 [AtLeast 1]
    -- , checkExprAssumeAssert "tests/TestFiles/Coercions/GADT.hs" 400 Nothing Nothing "g" 2
    --     [ AtLeast 2
    --     , RExists (\[x, y] -> x == Lit (LitInt 0) && y == App (Data (PrimCon I)) (Lit (LitInt 0)))
    --     , RExists (\[x, _] -> x /= Lit (LitInt 0))]
    -- , checkExprAssumeAssert "tests/TestFiles/HigherOrderList.hs" 400 Nothing Nothing "g" 3 [AtLeast  10] 
    
    ]

baseTests ::  TestTree
baseTests = testGroup "Base"
    [
      checkInputOutput "tests/Samples/Peano.hs" "Peano" "add" 400 3 [AtLeast 4]
    , checkInputOutput "tests/BaseTests/ListTests.hs" "ListTests" "test" 1000 2 [AtLeast 1]
    , checkInputOutput "tests/BaseTests/ListTests.hs" "ListTests" "maxMap" 1000 2 [AtLeast 4]
    , checkInputOutput "tests/BaseTests/ListTests.hs" "ListTests" "minTest" 1000 2 [AtLeast 2]
    , checkInputOutput "tests/BaseTests/ListTests.hs" "ListTests" "foldrTest2" 1000 2 [AtLeast 1]
    , checkInputOutput "tests/BaseTests/Tuples.hs" "Tuples" "addTupleElems" 1000 2 [AtLeast 2]

    , checkInputOutput "tests/BaseTests/MaybeTest.hs" "MaybeTest" "headMaybeInt" 1000 2 [AtLeast 2]
    , checkInputOutput "tests/BaseTests/MaybeTest.hs" "MaybeTest" "sumN" 1000 4 [AtLeast 6]
    , checkInputOutput "tests/BaseTests/MaybeTest.hs" "MaybeTest" "lengthN" 1000 5 [AtLeast 6]

    , checkInputOutput "tests/BaseTests/Other.hs" "Other" "check4VeryEasy2" 600 1 [AtLeast 1]
    ]

primTests :: TestTree
primTests = testGroup "Prims"
    [
      checkInputOutput "tests/Prim/Prim2.hs" "Prim2" "quotI1" 1000 3 [AtLeast 4]
    , checkInputOutput "tests/Prim/Prim2.hs" "Prim2" "quotI2" 1000 3 [AtLeast 4]
    , checkInputOutput "tests/Prim/Prim2.hs" "Prim2" "remI1" 1000 3 [AtLeast 4]
    , checkInputOutput "tests/Prim/Prim2.hs" "Prim2" "remI2" 1000 3 [AtLeast 3]

    , checkInputOutput "tests/Prim/Prim2.hs" "Prim2" "p1List" 300000 1 [AtLeast 1]
    , checkInputOutput "tests/Prim/Prim2.hs" "Prim2" "p2List" 700000 1 [AtLeast 1]
    , checkInputOutput "tests/Prim/Prim2.hs" "Prim2" "integerToFloatList" 150000 1 [AtLeast 1]

    , checkInputOutput "tests/Prim/Prim3.hs" "Prim3" "int2FloatTest" 1000 2 [AtLeast 1]
    , checkInputOutput "tests/Prim/Prim3.hs" "Prim3" "int2DoubleTest" 1000 2 [AtLeast 1]
    ]

-- To Do Tests
--------------

todoTests :: TestTree
todoTests = testGroup "To Do"
    [
      checkLiquid "tests/Liquid/TyApps.hs" "goodGet" 1000 4 [Exactly 0]
    , checkLiquid "tests/Liquid/TyApps.hs" "getPosInt" 1000 4
        [ AtLeast 1
        , RForAll (\[_, _, (App _ x), y] -> getIntB x $ \x' -> getIntB y $ \y' -> x' == y' && y' == 10)]
    , checkLiquid "tests/Liquid/TyApps.hs" "getPos" 1000 4
        [ AtLeast 1
        , RExists (\[_, _, (App _ x), y] -> getIntB x $ \x' -> getIntB y $ \y' -> x' == y' && y' == 10)]
    , checkLiquid "tests/Liquid/FoldrTests.hs" "max2" 1000 2 [Exactly 0]
    , checkLiquid "tests/Liquid/FoldrTests.hs" "max3" 1000 2 [Exactly 0]
    , checkLiquid "tests/Liquid/SimpleAnnot.hs" "simpleF" 1000 1 [Exactly 0]
    , checkLiquid "tests/Liquid/Ordering.hs" "lt" 1000 2 [AtLeast 1]
    , checkLiquid "tests/Liquid/Ordering.hs" "gt" 1000 2 [AtLeast 1]
    , checkLiquid "tests/Liquid/WhereFuncs2.hs" "hCalls" 1000 3 [AtLeast 1]
    , checkLiquid "tests/Liquid/WhereFuncs2.hs" "i" 1000 2 [AtLeast 1]
    , checkAbsLiquid "tests/Liquid/AddToEvenWhere.hs" "f" 2000 1
        [ AtLeast 1
        , RForAll (\[i] r [(FuncCall { funcName = Name n _ _ _, returns = r' }) ]
                        -> n == "g" && isInt i (\i' -> i' `mod` 2 == 0) && r == r' )]
    , checkLiquid "tests/Liquid/ListTests.lhs" "concat" 1000 2 [AtLeast 3]
    , checkLiquidWithMap "tests/Liquid/MapReduceTest.lhs" "mapReduce" 1500 2
        [Exactly 0]
    , checkLiquid "tests/Liquid/NearestTest.lhs" "nearest" 1500 1 [Exactly 1]

    , checkAbsLiquid "tests/Liquid/ListTests2.lhs" "replicate" 2000 3
        [ AtLeast 3
        , RForAll (\[_, nA, aA] _ [(FuncCall { funcName = Name n _ _ _, arguments = [_, _, nA', aA'] }) ]
            -> n == "replicate" && nA == nA' && aA == aA') ]


    , checkExpr "tests/TestFiles/TypeClass/TypeClass5.hs" 800 "run" 2 [AtLeast 1]
    , checkExpr "tests/TestFiles/TypeClass/TypeClass5.hs" 800 "run2" 2 [AtLeast 0]
    , checkInputOutput "tests/Prim/Prim2.hs" "Prim2" "sqrtList" 10000 1 [AtLeast 1]
    
    , checkInputOutput "tests/BaseTests/MaybeTest.hs" "MaybeTest" "average" 2000 5 [AtLeast 6]
    , checkInputOutput "tests/BaseTests/MaybeTest.hs" "MaybeTest" "averageF" 2000 2 [AtLeast 6]
    , checkInputOutput "tests/BaseTests/MaybeTest.hs" "MaybeTest" "maybeAvg" 200 4 [AtLeast 6]

    , checkInputOutput "tests/Prim/Prim3.hs" "Prim3" "float2IntTest" 1000 2 [AtLeast 1]
    , checkInputOutput "tests/Prim/Prim3.hs" "Prim3" "double2IntTest" 1000 2 [AtLeast 1]
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

checkExpr :: String -> Int -> String -> Int -> [Reqs ([Expr] -> Bool)] -> TestTree
checkExpr src stps entry i reqList =
    checkExprReaches src stps Nothing Nothing Nothing entry i reqList

checkExprAssume :: String -> Int -> Maybe String -> String -> Int -> [Reqs ([Expr] -> Bool)] -> TestTree
checkExprAssume src stps m_assume entry i reqList =
    checkExprReaches src stps m_assume Nothing Nothing entry i reqList

checkExprAssert :: String -> Int -> Maybe String -> String -> Int -> [Reqs ([Expr] -> Bool)] -> TestTree
checkExprAssert src stps m_assert entry i reqList =
    checkExprReaches src stps Nothing m_assert Nothing entry i reqList

checkExprAssumeAssert :: String
                      -> Int
                      -> Maybe String
                      -> Maybe String
                      -> String
                      -> Int
                      -> [Reqs ([Expr] -> Bool)]
                      -> TestTree
checkExprAssumeAssert src stps m_assume m_assert entry i reqList =
    checkExprReaches src stps m_assume m_assert Nothing entry i reqList

checkExprReaches :: String
                 -> Int
                 -> Maybe String
                 -> Maybe String
                 -> Maybe String
                 -> String
                 -> Int
                 -> [Reqs ([Expr] -> Bool)]
                 -> TestTree
checkExprReaches src stps m_assume m_assert m_reaches entry i reqList = do
    checkExprWithConfig src m_assume m_assert m_reaches entry i reqList
            (do
                config <- mkConfigTestIO
                return $ config {steps = stps})

checkExprWithMap :: String
                 -> Int
                 -> Maybe String
                 -> Maybe String
                 -> Maybe String
                 -> String
                 -> Int
                 -> [Reqs ([Expr] -> Bool)]
                 -> TestTree
checkExprWithMap src stps m_assume m_assert m_reaches entry i reqList = do
    checkExprWithConfig src m_assume m_assert m_reaches entry i reqList
            (do
                config <- mkConfigTestWithMapIO
                return $ config {steps = stps})

checkExprWithConfig :: String
                    -> Maybe String
                    -> Maybe String
                    -> Maybe String
                    -> String
                    -> Int
                    -> [Reqs ([Expr] -> Bool)]
                    -> IO Config
                    -> TestTree
checkExprWithConfig src m_assume m_assert m_reaches entry i reqList config_f = do
    testCase src (do
        config <- config_f
        res <- testFile src m_assume m_assert m_reaches entry config
        
        let ch = case res of
                    Left _ -> False
                    Right exprs -> null $ checkExprGen (map (\(inp, out) -> inp ++ [out]) exprs) i reqList
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
                []
                (fmap T.pack m_assume)
                (fmap T.pack m_assert)
                (fmap T.pack m_reaches)
                (isJust m_assert || isJust m_reaches)
                (T.pack entry)
                config

    let (states, _) = maybe (error "Timeout") fst r
    return $ map (\(ExecRes { conc_args = i, conc_out = o}) -> (i, o)) states 

checkLiquidWithNoCutOff :: FilePath -> String -> Int -> Int -> [Reqs ([Expr] -> Bool)] -> TestTree
checkLiquidWithNoCutOff fp entry stps i reqList = do
    checkLiquidWithConfig fp entry i reqList
        (do config <- mkConfigTestIO
            return $ config {steps = stps, cut_off = stps})

checkLiquid :: FilePath -> String -> Int -> Int -> [Reqs ([Expr] -> Bool)] -> TestTree
checkLiquid fp entry stps i reqList = do
    checkLiquidWithConfig  fp entry i reqList
        (do config <- mkConfigTestIO
            return $ config {steps = stps})

checkLiquidWithSet :: FilePath -> String -> Int -> Int -> [Reqs ([Expr] -> Bool)] -> TestTree
checkLiquidWithSet fp entry stps i reqList = do
    checkLiquidWithConfig  fp entry i reqList
        (do config <- mkConfigTestWithSetIO
            return $ config {steps = stps})

checkLiquidWithCutOff :: FilePath -> String -> Int -> Int -> Int -> [Reqs ([Expr] -> Bool)] -> TestTree
checkLiquidWithCutOff fp entry stps co i reqList = do
    checkLiquidWithConfig fp entry i reqList
        (do config <- mkConfigTestIO
            return $ config {steps = stps, cut_off = co})

checkLiquidWithMap :: FilePath -> String -> Int -> Int -> [Reqs ([Expr] -> Bool)] -> TestTree
checkLiquidWithMap fp entry stps i reqList = do
    checkLiquidWithConfig fp entry i reqList
        (do config <- mkConfigTestWithMapIO
            return $ config {steps = stps} )

checkLiquidWithConfig :: FilePath -> String -> Int -> [Reqs ([Expr] -> Bool)] -> IO Config -> TestTree
checkLiquidWithConfig fp entry i reqList config_f = 
    testCase fp (do
        config <- config_f
        res <- findCounterExamples' fp (T.pack entry) [] [] config

        let (ch, r) = case res of
                    Nothing -> (False, Right [Time])
                    Just (Left e) -> (False, Left e)
                    Just (Right exprs) ->
                        let
                            r_ = checkExprGen
                                    (map (\(ExecRes { conc_args = inp, conc_out = out}) -> inp ++ [out]) exprs)
                                    i
                                    reqList
                        in
                        (null r_, Right r_)

        assertBool ("Liquid test for file " ++ fp ++ 
                    " with function " ++ entry ++ " failed.\n" ++ show r) ch
        )

checkAbsLiquid :: FilePath -> String -> Int -> Int -> [Reqs ([Expr] -> Expr -> [FuncCall] -> Bool)] -> TestTree
checkAbsLiquid fp entry stps i reqList = do
    checkAbsLiquidWithConfig fp entry i reqList
        (do config <- mkConfigTestIO
            return $ config {steps = stps} )

checkAbsLiquidWithConfig :: FilePath
                         -> String
                         -> Int
                         -> [Reqs ([Expr]
                         -> Expr
                         -> [FuncCall]
                         -> Bool)]
                         -> IO Config
                         -> TestTree
checkAbsLiquidWithConfig fp entry i reqList config_f = do
    testCase fp (do
        config <- config_f
        res <- findCounterExamples' fp (T.pack entry) [] [] config

        let (ch, r) = case res of
                    Nothing -> (False, Right [])
                    Just (Left e) -> (False, Left e)
                    Just (Right exprs) ->
                        let
                            te = checkAbsLHExprGen
                                    (map (\(ExecRes { final_state = s, conc_args = inp, conc_out = out})
                                            -> (s, inp, out)
                                         ) exprs
                                    ) i reqList
                        in
                        (null te, Right te)

        assertBool ("Liquid test for file " ++ fp ++ 
                    " with function " ++ entry ++ " failed.\n" ++ show r) ch
        )

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

findCounterExamples' :: FilePath
                     -> T.Text
                     -> [FilePath]
                     -> [FilePath]
                     -> Config
                     -> IO (Maybe (Either SomeException [ExecRes AbstractedInfo]))
findCounterExamples' fp entry libs lhlibs config =
    let
        proj = takeDirectory fp
    in
    doTimeout (timeLimit config)
        $ try (return . fst. fst =<< findCounterExamples [proj] [fp] entry libs lhlibs config)

errors :: [Expr] -> Bool
errors e =
    case last e of
        Prim Error _ -> True
        _ -> False
