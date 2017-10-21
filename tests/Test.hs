{-# LANGUAGE FlexibleContexts #-}

module Main where

import Test.Tasty
import Test.Tasty.HUnit

import G2.Internals.Interface
import G2.Internals.Language as G2
import G2.Internals.Translation
import G2.Internals.SMT

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
        , testFileTests
        ]

timeout :: Timeout
timeout = mkTimeout 1

-- Test based on examples that are also good for demos
sampleTests :: IO TestTree
sampleTests =
    return . testGroup "Samples"
        =<< sequence [
                  checkExpr "tests/samples/" "tests/samples/Peano.hs" 700 (Just "fstIsEvenAddToFour") (Just "fstIsTwo") "add" 2 [RExists peano_0_4, RExists peano_4_0, Exactly 2]
                , checkExpr "tests/samples/" "tests/samples/Peano.hs" 900 (Just "multiplyToFour") (Just "equalsFour") "add" 2 [RExists peano_1_4, RExists peano_4_1, Exactly 2]
                , checkExpr "tests/samples/" "tests/samples/Peano.hs" 650 (Just "eqEachOtherAndAddTo4") Nothing "add" 2 [RForAll peano_2_2, Exactly 1]
                , checkExpr "tests/samples/" "tests/samples/Peano.hs" 400 (Just "equalsFour") Nothing "add" 2 [RExists peano_0_4, RExists peano_1_3, RExists peano_2_2, RExists peano_3_1, RExists peano_4_0, Exactly 5]
                , checkExpr "tests/samples/" "tests/samples/Peano.hs" 550 (Just "equalsFour") Nothing "multiply" 2 [RExists peano_1_4, RExists peano_2_2, RExists peano_4_1, Exactly 3]

                , checkExpr "tests/samples/" "tests/samples/HigherOrderMath.hs" 400 (Just "isTrue0") Nothing "notNegativeAt0NegativeAt1" 1 [RExists negativeSquareRes, AtLeast 1]
                , checkExpr "tests/samples/" "tests/samples/HigherOrderMath.hs" 400 (Just "isTrue1") Nothing "fixed" 2 [RExists abs2NonNeg, RExists squareRes, RExists fourthPowerRes, AtLeast 4]
                , checkExpr "tests/samples/" "tests/samples/HigherOrderMath.hs" 600 (Just "isTrue2") Nothing "sameDoubleArgLarger" 2 [RExists addRes, RExists subRes, AtLeast 2]

                -- The below test fails because Z3 returns unknown.
                , checkExpr "tests/samples/" "tests/samples/HigherOrderMath.hs" 1200 (Just "isTrue2") Nothing "sameDoubleArgLarger" 2 [RExists approxSqrtRes, RExists pythagoreanRes, AtLeast 2]
                
                , checkExprWithOutput "tests/samples/" "tests/samples/HigherOrderMath.hs" 400 Nothing Nothing "functionSatisfies" 4 [RExists functionSatisfiesRes, AtLeast 1]

                , checkExpr "tests/samples/" "tests/samples/McCarthy91.hs" 400 (Just "lessThan91") Nothing "mccarthy" 1 [RForAll (\[Lit (LitInt x)] -> x <= 100), AtLeast 1]
                , checkExpr "tests/samples/" "tests/samples/McCarthy91.hs" 400 (Just "greaterThan10Less") Nothing "mccarthy" 1 [RForAll (\[Lit (LitInt x)] -> x > 100), AtLeast 1]
                , checkExpr "tests/samples/" "tests/samples/McCarthy91.hs" 1000 (Just "lessThanNot91") Nothing "mccarthy" 1 [Exactly 0]
                , checkExpr "tests/samples/" "tests/samples/McCarthy91.hs" 1000 (Just "greaterThanNot10Less") Nothing "mccarthy" 1 [Exactly 0]

                , checkExprWithOutput "tests/samples/" "tests/samples/GetNth.hs" 400 Nothing Nothing "getNth" 3 [AtLeast 10, RForAll getNthTest]

                , checkExprReaches "tests/samples/" "tests/samples/GetNthErr.hs" 400 Nothing Nothing (Just "error") "getNth" 3 [AtLeast 6, RForAll errors]

                , checkExprWithOutput "tests/samples/" "tests/samples/FoldlUses.hs" 900 Nothing Nothing "sum" 2 [AtLeast 3]
                , checkExprWithOutput "tests/samples/" "tests/samples/FoldlUses.hs" 400 Nothing Nothing "dotProd" 3 [AtLeast 3]
        ]

-- Tests that are intended to ensure a specific feature works, but that are not neccessarily interesting beyond that
testFileTests :: IO TestTree
testFileTests = 
    return . testGroup "Samples"
        =<< sequence [
                  checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/IfTest.hs" 400 Nothing Nothing "f" 3 [RForAll (\[Lit (LitInt x), Lit (LitInt y), (Lit (LitInt r))] -> if x == y then r == x + y else r == y), AtLeast 2]

                , checkExpr "tests/TestFiles/" "tests/TestFiles/AssumeAssert.hs" 400 Nothing (Just "assertGt5") "outShouldBeGt5" 1 [Exactly 0]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/AssumeAssert.hs" 400 Nothing (Just "assertGt5") "outShouldBeGe5" 1 [AtLeast 1]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/AssumeAssert.hs" 400 (Just "assumeGt5") (Just "assertGt5") "outShouldBeGt5" 1 [Exactly 0]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/AssumeAssert.hs" 400 (Just "assumeGt5") (Just "assertGt5") "outShouldBeGe5" 1 [Exactly 0]

                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/Defunc1.hs" 400 Nothing Nothing "f" 2 [RExists defunc1Add1, RExists defunc1Multiply2, RExists defuncB, AtLeast 3]
                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/Defunc2.hs" 400 Nothing Nothing "funcMap" 3 [RForAll defunc2Check, AtLeast 30]

                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/MultCase.hs" 400 Nothing Nothing "f" 2
                    [ RExists (\[Lit (LitInt x), y] -> x == 2 && y == (Lit $ LitBool True))
                    , RExists (\[Lit(LitInt x), y] -> x == 1 && y == (Lit $ LitBool False))
                    , RExists (\[Lit (LitInt x), y] -> x /= 2 && x /= 1 && y == (Lit $ LitBool False))]

                , checkExpr "tests/TestFiles/" "tests/TestFiles/LetFloating.hs" 400 (Just "output6") Nothing "f" 1 [AtLeast 1, RExists (\[Lit (LitInt x)] -> x == 6)]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/LetFloating2.hs" 400 (Just "output16") Nothing "f" 1 [AtLeast 1, RExists (\[Lit (LitInt x)] -> x == 15)]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/LetFloating3.hs" 400 (Just "output32") Nothing "f" 1 [AtLeast 1, RExists (\[Lit (LitInt x)] -> x == 4)]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/LetFloating4.hs" 400 (Just "output12") Nothing "f" 1 [AtLeast 1, RExists (\[Lit (LitInt x)] -> x == 11)]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/LetFloating5.hs" 400 (Just "output19") Nothing "f" 2 [AtLeast 1, RForAll (\[Lit (LitInt x), Lit (LitInt y)] -> x + y + 1 == 19)]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/LetFloating6.hs" 400 (Just "output32") Nothing "f" 1 [AtLeast 1, RExists (\[Lit (LitInt x)] -> x == 25)]

                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/TypeClass1.hs" 400 Nothing Nothing "f" 2 [RExists (\[x, y] -> x == y), AtLeast 1]

                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/Case1.hs" 400 Nothing Nothing "f" 2 [RExists (\[Lit (LitInt x), y] -> x < 0 && dataConHasName "A" y), RExists (\[Lit (LitInt x), y] -> x >= 0 && dataConHasName "C" y), Exactly 2]
                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/Case2.hs" 400 Nothing Nothing "f" 2 
                        [ RExists exists1
                        , RExists exists2
                        , RExists exists3
                        , RExists exists4
                        , AtLeast 4]

                , checkExpr "tests/TestFiles/" "tests/TestFiles/Guards.hs" 400 (Just "g") Nothing "f" 1 [AtLeast 1, RExists (\[Lit (LitBool x)] -> x)]

                , checkExpr "tests/TestFiles/" "tests/TestFiles/Infinite.hs" 400 (Just "g") Nothing "f" 1 [AtLeast 1, RExists (\[Lit (LitInt x)] -> x <= 100 && x /= 80)]

                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/Strictness1.hs" 400 Nothing Nothing "f" 1 [AtLeast 1, RExists (\[(App x (Lit (LitInt y)))] -> dataConHasName "A" x && y == 9)]

                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/Where1.hs" 400 Nothing Nothing "f" 2 [ RExists (\[Lit (LitInt x), App _ (Lit (LitInt y))] -> x == 4 && y == 1)
                                                                                                           , RExists (\[Lit (LitInt x), App _ (Lit (LitInt y))] -> x /= 4 && y == 1) ]
                
                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/Error1.hs" 400 Nothing Nothing "f" 2 [AtLeast 1, RForAll(errors)]
                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/Error1.hs" 400 Nothing Nothing "g" 2 [AtLeast 1, RForAll(errors)]
                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/Error2.hs" 400 Nothing Nothing "f" 1 [AtLeast 1, RForAll(errors)]
                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/Error3.hs" 400 Nothing Nothing "f" 2 [AtLeast 1, RForAll(errors)]

                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/BadNames1.hs" 400 Nothing Nothing "abs'" 2 [Exactly 2]
                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/BadNames1.hs" 400 Nothing Nothing "xswitch" 2 [AtLeast 10]

                , checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/PolyDataTy1.hs" 400 Nothing Nothing "f" 3 [Exactly 2, RExists (\[x, _, y] -> x == y), RExists (\[_, App _ x, y] -> x == y)]
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
    exprs <- return . map (\(inp, out) -> inp ++ [out]) =<<  testFile proj src steps m_assume m_assert m_reaches entry
    
    let ch = checkExpr' (exprs) i reqList

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
    (binds, tycons) <- translation proj src "./defs/PrimDefs.hs"

    let init_state = initState binds tycons m_assume m_assert m_reaches (isJust m_assert || isJust m_reaches) entry

    hhp <- getZ3ProcessHandles

    r <- run smt2 hhp steps init_state

    return $ map (\(_, _, i, o) -> (i, o)) r

givenLengthCheck :: Int -> ([Expr] -> Bool) -> [Expr] -> Bool
givenLengthCheck i f e = if length e == i then f e else False

errors :: [Expr] -> Bool
errors e =
    case last e of
        Prim Error _ -> True
        _ -> False
