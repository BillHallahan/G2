{-# LANGUAGE FlexibleContexts #-}

module Main where

import Test.Tasty
import Test.Tasty.HUnit

import G2.Internals.Interface
import G2.Internals.Language as G2
import G2.Internals.Translation
import G2.Internals.Solver
import G2.Internals.Liquid.Interface

import Data.Maybe

import PeanoTest
import HigherOrderMathTest
import GetNthTest
import DefuncTest
import CaseTest
import TestUtils


-- | Requirements
-- We use these to define checks on tests returning function inputs
--     RForall f -- All the returned inputs satisfy the function f
--     RExists f -- At least one of the returned inputs satisfies the function f
--     AtLeast x -- At least x inputs are returned
--     AtMost  x -- At most x inputs are returned
--     Exactly x -- Exactly x inputs are returned
data Reqs = RForAll ([Expr] -> Bool) 
          | RExists ([Expr] -> Bool)
          | AtLeast Int
          | AtMost Int
          | Exactly Int

main :: IO ()
main = defaultMain
       =<< tests

tests :: IO TestTree
tests = return . testGroup "Tests"
    =<< sequence [
          sampleTests
        , liquidTests
        , testFileTests
        ]

timeout :: Timeout
timeout = mkTimeout 1

-- Test based on examples that are also good for demos
sampleTests :: IO TestTree
sampleTests =
    return . testGroup "Samples"
        =<< sequence [
                  checkExprWithOutput "tests/Samples/" "tests/Samples/Peano.hs" 900 Nothing (Just "equalsFour") "add" 3 [RForAll $ not . peano_4_out, AtLeast 10]
                , checkExpr "tests/Samples/" "tests/Samples/Peano.hs" 900 (Just "fstIsEvenAddToFour") (Just "fstIsTwo") "add" 2 [RExists peano_0_4, RExists peano_4_0, Exactly 2]
                , checkExpr "tests/Samples/" "tests/Samples/Peano.hs" 1000 (Just "multiplyToFour") (Just "equalsFour") "add" 2 [RExists peano_1_4, RExists peano_4_1, Exactly 2]
                , checkExpr "tests/Samples/" "tests/Samples/Peano.hs" 750 (Just "eqEachOtherAndAddTo4") Nothing "add" 2 [RForAll peano_2_2, Exactly 1]
                , checkExpr "tests/Samples/" "tests/Samples/Peano.hs" 600 (Just "equalsFour") Nothing "add" 2 [RExists peano_0_4, RExists peano_1_3, RExists peano_2_2, RExists peano_3_1, RExists peano_4_0, Exactly 5]
                , checkExpr "tests/Samples/" "tests/Samples/Peano.hs" 750 (Just "equalsFour") Nothing "multiply" 2 [RExists peano_1_4, RExists peano_2_2, RExists peano_4_1, Exactly 3]

                , checkExpr "tests/Samples/" "tests/Samples/HigherOrderMath.hs" 400 (Just "isTrue0") Nothing "notNegativeAt0NegativeAt1" 1 [RExists negativeSquareRes, AtLeast 1]
                , checkExpr "tests/Samples/" "tests/Samples/HigherOrderMath.hs" 600 (Just "isTrue1") Nothing "fixed" 2 [RExists abs2NonNeg, RExists squareRes, RExists fourthPowerRes, RForAll allabs2NonNeg, AtLeast 4]
                , checkExpr "tests/Samples/" "tests/Samples/HigherOrderMath.hs" 600 (Just "isTrue2") Nothing "sameFloatArgLarger" 2 [RExists addRes, RExists subRes, AtLeast 2]
                , checkExprWithOutput "tests/Samples/" "tests/Samples/HigherOrderMath.hs" 400 Nothing Nothing "functionSatisfies" 4 [RExists functionSatisfiesRes, AtLeast 1]
                -- -- The below test fails because Z3 returns unknown.
                -- , checkExpr "tests/Samples/" "tests/Samples/HigherOrderMath.hs" 1200 (Just "isTrue2") Nothing "sameFloatArgLarger" 2 [RExists approxSqrtRes, RExists pythagoreanRes, AtLeast 2]
                
                , checkExpr "tests/Samples/" "tests/Samples/McCarthy91.hs" 1000 (Just "lessThan91") Nothing "mccarthy" 1 [RForAll (\[App _ (Lit (LitInt x))] -> x <= 100), AtLeast 1]
                , checkExpr "tests/Samples/" "tests/Samples/McCarthy91.hs" 400 (Just "greaterThan10Less") Nothing "mccarthy" 1 [RForAll (\[App _ (Lit (LitInt x))] -> x > 100), AtLeast 1]
                , checkExpr "tests/Samples/" "tests/Samples/McCarthy91.hs" 1000 (Just "lessThanNot91") Nothing "mccarthy" 1 [Exactly 0]
                , checkExpr "tests/Samples/" "tests/Samples/McCarthy91.hs" 1000 (Just "greaterThanNot10Less") Nothing "mccarthy" 1 [Exactly 0]

                , checkExprWithOutput "tests/Samples/" "tests/Samples/GetNth.hs" 600 Nothing Nothing "getNth" 3 [AtLeast 10, RForAll getNthTest]
                , checkExprWithOutput "tests/Samples/" "tests/Samples/GetNthPoly.hs" 600 Nothing Nothing "getNthInt" 3 [AtLeast 10, RForAll getNthErrTest]
                , checkExprWithOutput "tests/Samples/" "tests/Samples/GetNthPoly.hs" 600 Nothing Nothing "getNthX" 3 [AtLeast 10, RForAll getNthErrGenTest]
                , checkExprWithOutput "tests/Samples/" "tests/Samples/GetNthPoly.hs" 600 Nothing Nothing "getNthPeano" 3 [AtLeast 10, RForAll getNthErrGenTest] -- 533
                , checkExprWithOutput "tests/Samples/" "tests/Samples/GetNthPoly.hs" 600 Nothing Nothing "getNthCListInt" 3 [AtLeast 10, RForAll getNthErrGenTest2']
                , checkExprWithOutput "tests/Samples/" "tests/Samples/GetNthPoly.hs" 600 Nothing Nothing "getNthCListX" 3 [AtLeast 10, RForAll getNthErrGenTest2]
                , checkExprWithOutput "tests/Samples/" "tests/Samples/GetNthPoly.hs" 1000 Nothing Nothing "getNth" 3 [AtLeast 10]

                , checkExprWithOutput "tests/Samples/" "tests/Samples/GetNthPoly.hs" 600 Nothing Nothing "cfmapInt" 3 [AtLeast 10, RForAll cfmapTest]
                , checkExprWithOutput "tests/Samples/" "tests/Samples/GetNthPoly.hs" 1200 Nothing Nothing "cfmapIntX" 3 [AtLeast 10, RForAll cfmapTest]
                , checkExprWithOutput "tests/Samples/" "tests/Samples/GetNthPoly.hs" 1400 Nothing Nothing "cfmapIntCListInt" 3 [AtLeast 10, RForAll cfmapTest]

                , checkExprReaches "tests/Samples/" "tests/Samples/GetNthErr.hs" 800 Nothing Nothing (Just "error") "getNth" 3 [AtLeast 8, RForAll errors]

                , checkExprWithOutput "tests/Samples/" "tests/Samples/FoldlUses.hs" 1600 Nothing Nothing "sum" 2 [AtLeast 3]
                , checkExprWithOutput "tests/Samples/" "tests/Samples/FoldlUses.hs" 1000 Nothing Nothing "dotProd" 3 [AtLeast 3]

                , checkExprWithOutput "tests/Samples/" "tests/Samples/FoldlUsesPoly.hs" 600 Nothing Nothing "sumMinAndMax" 2 [AtLeast 10]
                , checkExprWithOutput "tests/Samples/" "tests/Samples/FoldlUsesPoly.hs" 400 Nothing Nothing "maxes" 3 [AtLeast 10]
                , checkExprWithOutput "tests/Samples/" "tests/Samples/FoldlUsesPoly.hs" 400 Nothing Nothing "switchInt" 2 [AtLeast 1]
                , checkExprWithOutput "tests/Samples/" "tests/Samples/FoldlUsesPoly.hs" 400 Nothing Nothing "getInInt" 2 [AtLeast 1]
                , checkExprWithOutput "tests/Samples/" "tests/Samples/FoldlUsesPoly.hs" 400 Nothing Nothing "switchP" 2 [AtLeast 1]
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
                , checkLiquid "tests/Liquid" "tests/Liquid/SimplePoly.hs" "switchInt" 400 2 [Exactly 1, RForAll (\[App (App _ x) _, App (App _ _) y] -> getIntB x $ \ x' -> getIntB y $ \ y' -> x' == y')]

                , checkLiquid "tests/Liquid" "tests/Liquid/Peano.hs" "add" 2000 3 [RForAll (\[x, y, _] -> x `eqIgT` zeroPeano || y `eqIgT` zeroPeano), AtLeast 5]
                , checkLiquid "tests/Liquid" "tests/Liquid/Peano.hs" "fromInt" 600 2 [RForAll (\[x, y] -> isInt x (\x' -> x' == 0)  && y `eqIgT` zeroPeano), AtLeast 1]

                , checkLiquid "tests/Liquid" "tests/Liquid/GetNth.hs" "getNthInt" 4000 3 [AtLeast 3, RForAll getNthErrors]
                , checkLiquid "tests/Liquid" "tests/Liquid/GetNth.hs" "sumC" 1500 2 [AtLeast 3, RForAll (\[_, y] -> isInt y $ (==) 0)]
                , checkLiquid "tests/Liquid" "tests/Liquid/GetNth.hs" "getNth" 4000 3 [AtLeast 3]
                , checkLiquid "tests/Liquid" "tests/Liquid/GetNth.hs" "sumCList" 2000 2 [AtLeast 3]

                , checkLiquid "tests/Liquid" "tests/Liquid/DataRefTest.hs" "addMaybe" 1000 3 
                    [AtLeast 2, RForAll (\[_, y, z] -> isInt y $ \y' -> appNthArgIs z (\z' -> isInt z' $ \z'' -> z'' <= y') 2)]
                , checkLiquid "tests/Liquid" "tests/Liquid/DataRefTest.hs" "addMaybe2" 2000 3 
                    [AtLeast 2, RForAll (\[x, _, _] -> appNthArgIs x (\x' -> isInt x' $ \x'' -> x'' >= 0) 1)
                              , RForAll (\[_, y, z] -> isInt y $ \y' -> appNthArgIs z (\z' -> isInt z' $ \z'' -> z'' <= y') 2)]
                , checkLiquid "tests/Liquid" "tests/Liquid/DataRefTest.hs" "getLeftInts" 2000 2 
                    [AtLeast 1, RForAll (\[x, _] -> dcInAppHasName "Right" x 1)]
                , checkLiquid "tests/Liquid" "tests/Liquid/DataRefTest.hs" "sumSameInts" 2000 3 
                    [AtLeast 1, RForAll (\[x, y, _] -> dcInAppHasName "Right" x 1 && dcInAppHasName "Left" y 1)]
                , checkLiquid "tests/Liquid" "tests/Liquid/DataRefTest.hs" "sub1" 1200 2 [AtLeast 1]
        ]

-- Tests that are intended to ensure a specific feature works, but that are not neccessarily interesting beyond that
testFileTests :: IO TestTree
testFileTests = 
    return . testGroup "TestFiles"
        =<< sequence [
                  checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/IfTest.hs" 400 Nothing Nothing "f" 3 [RForAll (\[App _ (Lit (LitInt x)), App _ (Lit (LitInt y)), App _ (Lit (LitInt r))] -> if x == y then r == x + y else r == y), AtLeast 2]

                , checkExpr "tests/TestFiles/" "tests/TestFiles/AssumeAssert.hs" 400 Nothing (Just "assertGt5") "outShouldBeGt5" 1 [Exactly 0]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/AssumeAssert.hs" 400 Nothing (Just "assertGt5") "outShouldBeGe5" 1 [AtLeast 1]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/AssumeAssert.hs" 400 (Just "assumeGt5") (Just "assertGt5") "outShouldBeGt5" 1 [Exactly 0]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/AssumeAssert.hs" 400 (Just "assumeGt5") (Just "assertGt5") "outShouldBeGe5" 1 [Exactly 0]

                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/Defunc1.hs" 400 Nothing Nothing "f" 2 [RExists defunc1Add1, RExists defunc1Multiply2, RExists defuncB, AtLeast 3]
                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/Defunc2.hs" 400 Nothing Nothing "funcMap" 3 [RForAll defunc2Check, AtLeast 30]

                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/MultCase.hs" 400 Nothing Nothing "f" 2
                    [ RExists (\[App _ (Lit (LitInt x)), y] -> x == 2 && getBoolB y id)
                    , RExists (\[App _ (Lit (LitInt x)), y] -> x == 1 && getBoolB y id)
                    , RExists (\[App _ (Lit (LitInt x)), y] -> x /= 2 && x /= 1 && getBoolB y not)]

                , checkExpr "tests/TestFiles/" "tests/TestFiles/LetFloating/LetFloating.hs" 400 (Just "output6") Nothing "f" 1 [AtLeast 1, RExists (\[App _ (Lit (LitInt x))] -> x == 6)]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/LetFloating/LetFloating2.hs" 400 (Just "output16") Nothing "f" 1 [AtLeast 1, RExists (\[App _ (Lit (LitInt x))] -> x == 15)]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/LetFloating/LetFloating3.hs" 600 (Just "output32") Nothing "f" 1 [AtLeast 1, RExists (\[App _ (Lit (LitInt x))] -> x == 4)]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/LetFloating/LetFloating4.hs" 400 (Just "output12") Nothing "f" 1 [AtLeast 1, RExists (\[App _ (Lit (LitInt x))] -> x == 11)]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/LetFloating/LetFloating5.hs" 400 (Just "output19") Nothing "f" 2 [AtLeast 1, RForAll (\[App _ (Lit (LitInt x)), App _ (Lit (LitInt y))] -> x + y + 1 == 19)]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/LetFloating/LetFloating6.hs" 400 (Just "output32") Nothing "f" 1 [AtLeast 1, RExists (\[App _ (Lit (LitInt x))] -> x == 25)]

                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/TypeClass/TypeClass1.hs" 400 Nothing Nothing "f" 2 [RExists (\[x, y] -> x == y), Exactly 1]
                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/TypeClass/TypeClass2.hs" 400 Nothing Nothing "f" 2 [RExists (\[x, y] -> x == y), Exactly 1]
                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/TypeClass/TypeClass3.hs" 400 Nothing Nothing "f" 2 [RExists (\[x, y] -> getIntB x $ \x' -> getIntB y $ \y' -> x' + 8 == y'), Exactly 1]
                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/TypeClass/HKTypeClass1.hs" 400 (Just "largeJ") Nothing "extractJ" 2 [RForAll (\[x, ly@(App _ (Lit (LitInt y)))] -> appNthArgIs x (ly ==) 1 && y > 100), Exactly 1]
                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/TypeClass/HKTypeClass1.hs" 400 (Just "largeE") Nothing "extractE" 2 [RForAll (\[x, ly@(App _ (Lit (LitInt y)))] -> appNthArgIs x (ly ==) 2 && y > 100), Exactly 1]
                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/TypeClass/HKTypeClass1.hs" 400 Nothing Nothing "changeJ" 3 [RForAll (\[_, x, y] -> dcInAppHasName "J" x 1 && dcInAppHasName "J" y 2), AtLeast 2]

                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/Case1.hs" 400 Nothing Nothing "f" 2 [ RExists (\[App _ (Lit (LitInt x)), y] -> x < 0 && dcHasName "A" y)
                                                                                                              , RExists (\[App _ (Lit (LitInt x)), y] -> x >= 0 && dcHasName "C" y), Exactly 2]
                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/Case2.hs" 400 Nothing Nothing "f" 2 
                        [ RExists exists1
                        , RExists exists2
                        , RExists exists3
                        , RExists exists4
                        , AtLeast 4]

                , checkExpr "tests/TestFiles/" "tests/TestFiles/Guards.hs" 400 (Just "g") Nothing "f" 1 [AtLeast 1, RExists (\[dc] -> getBoolB dc id)]

                , checkExpr "tests/TestFiles/" "tests/TestFiles/Infinite.hs" 400 (Just "g") Nothing "f" 1 [AtLeast 1, RExists (\[App _ (Lit (LitInt x))] -> x <= 100 && x /= 80)]

                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/Strictness1.hs" 400 Nothing Nothing "f" 1 [AtLeast 1, RExists (\[(App x (App _ (Lit (LitInt y))))] -> dcHasName "A" x && y == 9)]

                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/Where1.hs" 400 Nothing Nothing "f" 2 [ RExists (\[App _ (Lit (LitInt x)), App _ (Lit (LitInt y))] -> x == 4 && y == 1)
                                                                                                           , RExists (\[App _ (Lit (LitInt x)), App _ (Lit (LitInt y))] -> x /= 4 && y == 1) ]
                
                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/Error/Error1.hs" 400 Nothing Nothing "f" 2 [AtLeast 1, RForAll(errors)]
                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/Error/Error1.hs" 400 Nothing Nothing "g" 2 [AtLeast 1, RForAll(errors)]
                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/Error/Error2.hs" 400 Nothing Nothing "f" 1 [AtLeast 1, RForAll(errors)]
                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/Error/Error3.hs" 400 Nothing Nothing "f" 2 [AtLeast 1, RForAll(errors)]
                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/Error/Error3.hs" 400 Nothing Nothing "g" 2 [AtLeast 1, RForAll(not . errors)]

                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/BadNames1.hs" 400 Nothing Nothing "abs'" 2 [Exactly 2]
                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/BadNames1.hs" 400 Nothing Nothing "xswitch" 2 [AtLeast 10]

                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/PolyDataTy1.hs" 400 Nothing Nothing "f" 3 [Exactly 2, RExists (\[x, _, y] -> x == y), RExists (\[_, App _ x, y] -> x == y)]
                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/PolyDataTy1.hs" 400 Nothing Nothing "getFstXIntInt" 2 [AtLeast 2, RExists (\[x, y] -> isApp x && isError y)]
                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/PolyDataTy1.hs" 400 Nothing Nothing "sum" 2 [AtLeast 3, RExists (\[x, y] -> isApp x && isError y)]

                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/MultiSplit.hs" 1000 (Just "equals1") Nothing "f" 3 [Exactly 0]

                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/MatchesFunc1.hs" 400 Nothing Nothing "f" 2 [RExists (\[x, y] -> getIntB x $ \x' -> getIntB y $ \y' ->  y' == 6 + x'), AtLeast 1]

                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/RecordFields1.hs" 400 Nothing Nothing "f" 2 [RExists (\[x, y] -> appNthArgIs x notCast 0 && appNthArgIs x (\x' -> getIntB x' $ \x'' -> getIntB y $ \y' -> x'' + 1 == y') 1), Exactly 1]
                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/RecordFields1.hs" 400 Nothing Nothing "fCall" 1 [RExists (\[x] -> isInt x ((==) 35)), Exactly 1]
                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/RecordFields1.hs" 400 Nothing Nothing "g" 2 [RExists (\[x, y] -> appNthArgIs x (dcHasName "A") 2 && appNthArgIs y (dcHasName "B") 2)
                                                                                                                      , RExists (\[x, y] -> appNthArgIs x (dcHasName "B") 2 && appNthArgIs y (dcHasName "C") 2)
                                                                                                                      , RExists (\[x, y] -> appNthArgIs x (dcHasName "C") 2 && appNthArgIs y (dcHasName "A") 2)
                                                                                                                      , Exactly 3]

                -- -- , checkExprWithOutput "tests/TestFiles/Deriving" "tests/TestFiles/Deriving/DerivingSimple.hs" 400 Nothing Nothing "eq" 3 [AtLeast  2, RForAll (\[_, _, x] -> isBool x)]
                -- -- , checkExprWithOutput "tests/TestFiles/Deriving" "tests/TestFiles/Deriving/DerivingSimple.hs" 400 Nothing Nothing "lt" 3 [AtLeast 2, RForAll (\[_, _, x] -> isBool x)]
                -- -- , checkExprWithOutput "tests/TestFiles/Deriving" "tests/TestFiles/Deriving/DerivingComp.hs" 400 Nothing Nothing "eq" 3 [AtLeast 2, RForAll (\[_, _, x] -> isBool x)]
                -- -- , checkExprWithOutput "tests/TestFiles/Deriving" "tests/TestFiles/Deriving/DerivingComp.hs" 400 Nothing Nothing "lt" 3 [AtLeast 2, RForAll (\[_, _, x] -> isBool x)]

                , checkExprWithOutput "tests/TestFiles/Coercions" "tests/TestFiles/Coercions/Age.hs" 400 Nothing Nothing "born" 1 [ Exactly 1
                                                                                                                                  , RForAll (\[x] -> inCast x (\x' -> appNthArgIs x' (Lit (LitInt 0) ==) 1) (\(t1 :~ t2) -> isIntT t1 && typeNameIs t2 "Age"))]
                , checkExprWithOutput "tests/TestFiles/Coercions" "tests/TestFiles/Coercions/Age.hs" 400 Nothing Nothing "yearPasses" 2 [ AtLeast 1
                                                                                                                                        , RForAll (\[x, y] -> inCast x (const True) (\(_ :~ t2) -> typeNameIs t2 "Age")
                                                                                                                                                           && inCast y (const True) (\(_ :~ t2) -> typeNameIs t2 "Age") )]
                , checkExprWithOutput "tests/TestFiles/Coercions" "tests/TestFiles/Coercions/Age.hs" 400 Nothing Nothing "age" 2 [ AtLeast 1
                                                                                                                                 , RForAll (\[x, y] -> inCast x (const True) (\(_ :~ t2) -> typeNameIs t2 "Age") && isInt y (const True))]
                , checkExprWithOutput "tests/TestFiles/Coercions" "tests/TestFiles/Coercions/Age.hs" 400 Nothing Nothing "diffAge" 3 [ AtLeast 1
                                                                                                                                     , RForAll (\[x, y, z] -> inCast x (const True) (\(_ :~ t2) -> typeNameIs t2 "Age") 
                                                                                                                                                           && inCast y (const True) (\(_ :~ t2) -> typeNameIs t2 "Age")
                                                                                                                                                           && inCast z (const True) (\(_ :~ t2) -> typeNameIs t2 "Years"))]
                , checkExprWithOutput "tests/TestFiles/Coercions" "tests/TestFiles/Coercions/Age.hs" 400 Nothing Nothing "yearBefore" 2 [ AtLeast 5 ]
                , checkExprWithOutput "tests/TestFiles/Coercions" "tests/TestFiles/Coercions/NewType1.hs" 400 Nothing Nothing "add1N4" 2 [ Exactly 1
                                                                                                                                         , RForAll (\[x, y] -> inCast x (const True) (\(_ :~ t2) -> typeNameIs t2 "N4") 
                                                                                                                                                            && inCast y (const True) (\(_ :~ t2) -> typeNameIs t2 "N4"))]
                , checkExprWithOutput "tests/TestFiles/Coercions" "tests/TestFiles/Coercions/NewType1.hs" 400 Nothing Nothing "f" 2 [ Exactly 1
                                                                                                                                    , RForAll (\[x, y] -> inCast x (const True) (\(_ :~ t2) -> typeNameIs t2 "NewX") && dcHasName "X" y)]
                , checkExprWithOutput "tests/TestFiles/Coercions" "tests/TestFiles/Coercions/NewType1.hs" 400 Nothing Nothing "g" 2 [ Exactly 1
                                                                                                                                    , RForAll (\[x, y] -> dcHasName "X" x && inCast y (const True) (\(_ :~ t2) -> typeNameIs t2 "NewX"))]

                , checkExprWithOutput "tests/TestFiles/Coercions" "tests/TestFiles/Coercions/NewType1.hs" 400 Nothing Nothing "mapWInt" 3 [ AtLeast 2
                                                                                                                                          , RForAll (\[_, x, y] -> inCast x (const True) (\(_ :~ t2) -> typeNameIs t2 "W")
                                                                                                                                                                && inCast x (const True) (\(_ :~ t2) -> typeNameIs t2 "W")) ]

                , checkExprWithOutput "tests/TestFiles/Coercions" "tests/TestFiles/Coercions/NewType1.hs" 400 Nothing Nothing "appLeftFloat" 3 [ AtLeast 2
                                                                                                                                               , RExists (\[_, _, y] -> inCast y (\y' -> dcInAppHasName "L" y' 3) (const True))
                                                                                                                                               , RExists (\[_, _, y] -> inCast y (\y' -> dcInAppHasName "R" y' 3) (const True))]
                , checkExprWithOutput "tests/TestFiles/Coercions" "tests/TestFiles/Coercions/NewType1.hs" 400 Nothing Nothing "getLIntFloat" 2 [ AtLeast 2
                                                                                                                                               , RExists (\[_, y] -> isInt y (const True))
                                                                                                                                               , RExists (\[_, y] -> isError y)]
                , checkExprWithOutput "tests/TestFiles/Coercions" "tests/TestFiles/Coercions/NewType1.hs" 400 Nothing Nothing "getRIntFloat" 2 [ AtLeast 2
                                                                                                                                               , RExists (\[_, y] -> isFloat y (const True))
                                                                                                                                               , RExists (\[_, y] -> isError y)]
                , checkExprWithOutput "tests/TestFiles/Coercions" "tests/TestFiles/Coercions/NewType1.hs" 400 Nothing Nothing "getCIntFloatDouble" 2 [ AtLeast 2
                                                                                                                                                     , RExists (\[_, y] -> isFloat y (const True))
                                                                                                                                                     , RExists (\[_, y] -> isError y)]
                , checkExprWithOutput "tests/TestFiles/Coercions" "tests/TestFiles/Coercions/NewType1.hs" 400 Nothing Nothing "getRIntFloatX'" 2 [ AtLeast 2
                                                                                                                                                 , RExists (\[x, y] -> inCast x (\x' -> dcInAppHasName "TR" x' 1) (const True)
                                                                                                                                                                    && isInt y (const True))
                                                                                                                                                 , RExists (\[x, y] -> isError y)]
                -- , checkExprWithOutput "tests/TestFiles/Coercions" "tests/TestFiles/Coercions/GADT.hs" 400 Nothing Nothing "g" 2 [AtLeast 2
                --                                                                                                                 , RExists (\[x, y] -> x == Lit (LitInt 0) && y == App (Data (PrimCon I)) (Lit (LitInt 0)))
                --                                                                                                                 , RExists (\[x, _] -> x /= Lit (LitInt 0))]
                
        ]


checkExpr :: String -> String -> Int -> Maybe String -> Maybe String -> String -> Int -> [Reqs] -> IO TestTree
checkExpr proj src steps m_assume m_assert entry i reqList = do
    exprs <- return . map fst =<< testFile proj src steps m_assume m_assert Nothing entry

    let ch = checkExpr' exprs i reqList

    return . testCase src
        $ assertBool ("Assume/Assert for file " ++ src ++ 
                      " with functions [" ++ (fromMaybe "" m_assume) ++ "] " ++
                                      "[" ++ (fromMaybe "" m_assert) ++ "] " ++
                                              entry ++ " failed.\n") ch

checkExprWithOutput :: String -> String -> Int -> Maybe String -> Maybe String -> String -> Int -> [Reqs] -> IO TestTree
checkExprWithOutput proj src steps m_assume m_assert entry i reqList =
    checkExprReaches proj src steps m_assume m_assert Nothing entry i reqList

checkExprReaches :: String -> String -> Int -> Maybe String -> Maybe String -> Maybe String -> String -> Int -> [Reqs] -> IO TestTree
checkExprReaches proj src steps m_assume m_assert m_reaches entry i reqList = do
    exprs <- return . map (\(inp, out) -> inp ++ [out]) =<< testFile proj src steps m_assume m_assert m_reaches entry
    
    let ch = checkExpr' exprs i reqList

    return . testCase src
        $ assertBool ("Assume/Assert for file " ++ src ++ 
                      " with functions [" ++ (fromMaybe "" m_assume) ++ "] " ++
                                      "[" ++ (fromMaybe "" m_assert) ++ "] " ++
                                              entry ++ " failed.\n") ch

-- | Checks conditions on given expressions
checkExpr' :: [[Expr]] -> Int -> [Reqs] -> Bool
checkExpr' exprs i reqList =
    let
        argChecksAll = and . map (\f -> all (givenLengthCheck i f) exprs) $ [f | RForAll f <- reqList]
        argChecksEx = and . map (\f -> any (givenLengthCheck i f) exprs) $ [f | RExists f <- reqList]
        checkAtLeast = and . map ((>=) (length exprs)) $ [x | AtLeast x <- reqList]
        checkAtMost = and . map ((<=) (length exprs)) $ [x | AtMost x <- reqList]
        checkExactly = and . map ((==) (length exprs)) $ [x | Exactly x <- reqList]

        checkArgCount = and . map ((==) i . length) $ exprs
    in
    argChecksAll && argChecksEx && checkAtLeast && checkAtMost && checkExactly && checkArgCount

testFile :: String -> String -> Int -> Maybe String -> Maybe String -> Maybe String -> String -> IO ([([Expr], Expr)])
testFile proj src steps m_assume m_assert m_reaches entry = do
    (mod, binds, tycons, cls) <- translateLoaded proj src "./defs/PrimDefs.hs" True
    -- (mod, binds, tycons, cls) <- translateLoaded proj src "../base-4.9.1.0/Prelude.hs" True

    let init_state = initState binds tycons cls m_assume m_assert m_reaches (isJust m_assert || isJust m_reaches) entry (Just mod)

    hhp <- getZ3ProcessHandles

    r <- run smt2 hhp steps init_state

    return $ map (\(_, _, i, o, _) -> (i, o)) r

checkLiquid :: FilePath -> FilePath -> String -> Int -> Int -> [Reqs] -> IO TestTree
checkLiquid proj fp entry steps i reqList = do
    r <- findCounterExamples proj "./defs/PrimDefs.hs" fp entry steps
    -- r <- findCounterExamples proj "../base-4.9.1.0/Prelude.hs" fp entry steps

    let exprs = map (\(_, _, inp, out, _) -> inp ++ [out]) r

    let ch = checkExpr' exprs i reqList

    return . testCase fp
        $ assertBool ("Liquid test for file " ++ fp ++ 
                      " with function " ++ entry ++ " failed.\n") ch

givenLengthCheck :: Int -> ([Expr] -> Bool) -> [Expr] -> Bool
givenLengthCheck i f e = if length e == i then f e else False

errors :: [Expr] -> Bool
errors e =
    case last e of
        Prim Error _ -> True
        _ -> False
