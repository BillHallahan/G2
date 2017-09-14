{-# LANGUAGE FlexibleContexts #-}

module Main where

import Test.Tasty
import Test.Tasty.HUnit

import GHC

import G2.Internals.Interface
import G2.Internals.Language as G2
import G2.Internals.Translation
import G2.Internals.Preprocessing
import G2.Internals.Execution
import G2.Internals.SMT


import Data.List
import qualified Data.Map  as M
import Data.Maybe
import qualified Data.Monoid as Mon
import Data.Tuple

import PeanoTest
import HigherOrderMathTest

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
main = defaultMain =<< tests


tests = return . testGroup "Tests"
    =<< sequence [
           sampleTests
        , testFileTests
        ]

-- Test based on examples that are also good for demos
sampleTests :: IO TestTree
sampleTests =
    return . testGroup "Samples"
        =<< sequence [
                  checkExpr "tests/samples/" "tests/samples/Peano.hs" 615 (Just "fstIsEvenAddToFour") (Just "fstIsTwo") "add" 2 [RExists peano_0_4, RExists peano_4_0, Exactly 2]
                -- , checkExpr "tests/samples/" "tests/samples/Peano.hs" (Just "multiplyToFour") (Just "equalsFour") "add" 2 [RExists peano_1_4, RExists peano_4_1, Exactly 2]
                , checkExpr "tests/samples/" "tests/samples/Peano.hs" 400 (Just "equalsFour") Nothing "add" 2 [RExists peano_0_4, RExists peano_1_3, RExists peano_2_2, RExists peano_3_1, RExists peano_4_0, Exactly 5]
                , checkExpr "tests/samples/" "tests/samples/Peano.hs" 600 (Just "eqEachOtherAndAddTo4") Nothing "add" 2 [RForAll peano_2_2, Exactly 1]
                , checkExpr "tests/samples/" "tests/samples/Peano.hs" 400 (Just "equalsFour") Nothing "multiply" 2 [RExists peano_1_4, RExists peano_2_2, RExists peano_4_1, Exactly 3]

                , checkExpr "tests/samples/" "tests/samples/HigherOrderMath.hs" 400 (Just "isTrue0") Nothing "notNegativeAt0NegativeAt1" 1 [RExists negativeSquareRes, AtLeast 1]
                , checkExpr "tests/samples/" "tests/samples/HigherOrderMath.hs" 400 (Just "isTrue1") Nothing "fixed" 2 [RExists abs2NonNeg, RExists squareRes, RExists fourthPowerRes, AtLeast 4]
                , checkExpr "tests/samples/" "tests/samples/HigherOrderMath.hs" 400 (Just "isTrue2") Nothing "sameDoubleArgLarger" 2 [RExists addRes, RExists subRes, RExists pythagoreanRes, AtLeast 2]
                , checkExprWithOutput "tests/samples/" "tests/samples/HigherOrderMath.hs" Nothing Nothing "functionSatisfies" 4 [RExists functionSatisfiesRes, AtLeast 1]

                , checkExpr "tests/samples/" "tests/samples/McCarthy91.hs" 400 (Just "lessThan91") Nothing "mccarthy" 1 [RForAll (\[Lit (LitInt x)] -> x <= 100), AtLeast 1]
                , checkExpr "tests/samples/" "tests/samples/McCarthy91.hs" 400 (Just "greaterThan10Less") Nothing "mccarthy" 1 [RForAll (\[Lit (LitInt x)] -> x > 100), AtLeast 1]
                -- , checkExpr "tests/samples/" "tests/samples/McCarthy91.hs" (Just "lessThanNot91") Nothing "mccarthy" 1 [Exactly 0]
                -- , checkExpr "tests/samples/" "tests/samples/McCarthy91.hs" (Just "greaterThanNot10Less") Nothing "mccarthy" 1 [Exactly 0]
        ]

-- Tests that are intended to ensure a specific feature works, but that are not neccessarily interesting beyond that
testFileTests :: IO TestTree
testFileTests = 
    return . testGroup "Samples"
        =<< sequence [
                  checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/IfTest.hs" Nothing Nothing "f" 3 [RForAll (\[Lit (LitInt x), Lit (LitInt y), (Lit (LitInt r))] -> if x == y then r == x + y else r == y), AtLeast 2]

                , checkExpr "tests/TestFiles/" "tests/TestFiles/AssumeAssert.hs" 400 Nothing (Just "assertGt5") "outShouldBeGt5" 1 [Exactly 0]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/AssumeAssert.hs" 400 Nothing (Just "assertGt5") "outShouldBeGe5" 1 [AtLeast 1]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/AssumeAssert.hs" 400 (Just "assumeGt5") (Just "assertGt5") "outShouldBeGt5" 1 [Exactly 0]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/AssumeAssert.hs" 400 (Just "assumeGt5") (Just "assertGt5") "outShouldBeGe5" 1 [Exactly 0]

                -- , checkExpr "tests/TestFiles/" "tests/TestFiles/MultCase.hs" Nothing Nothing "f" 2
                    -- [ RExists (\[Lit (LitDouble x), y] -> x == 2 && y == (Lit $ LitBool True))
                --     , RExists (\[Const(CDouble x), y] -> x == 1 && y == (Data $ PrimCon DFalse))
                    -- , RExists (\[Lit (LitDouble x), y] -> x /= 2 && x /= 1 && y == (Lit $ LitBool False))]

                , checkExpr "tests/TestFiles/" "tests/TestFiles/LetFloating.hs" 400 (Just "output6") Nothing "f" 1 [AtLeast 1, RExists (\[Lit (LitInt x)] -> x == 6)]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/LetFloating2.hs" 400 (Just "output16") Nothing "f" 1 [AtLeast 1, RExists (\[Lit (LitInt x)] -> x == 15)]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/LetFloating3.hs" 400 (Just "output32") Nothing "f" 1 [AtLeast 1, RExists (\[Lit (LitInt x)] -> x == 4)]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/LetFloating4.hs" 400 (Just "output19") Nothing "f" 2 [AtLeast 1, RForAll (\[Lit (LitInt x), Lit (LitInt y)] -> x + y + 1 == 19)]
        ]


checkExpr :: String -> String -> Int -> Maybe String -> Maybe String -> String -> Int -> [Reqs] -> IO TestTree
checkExpr proj src steps m_assume m_assert entry i reqList = do
    exprs <- return . map fst =<< testFile proj src steps m_assume m_assert entry

    let ch = checkExpr' exprs i reqList

    putStrLn $ "exprs = " ++ show exprs

    return . testCase src
        $ assertBool ("Assume/Assert for file " ++ src ++ 
                      " with functions [" ++ (fromMaybe "" m_assume) ++ "] " ++
                                      "[" ++ (fromMaybe "" m_assert) ++ "] " ++
                                              entry ++ " failed.\n") ch

checkExprWithOutput :: String -> String -> Maybe String -> Maybe String -> String -> Int -> [Reqs] -> IO TestTree
checkExprWithOutput proj src m_assume m_assert entry i reqList = do
    exprs <- return . map (\(a, b) -> a ++ [b]) =<<  testFile proj src 400 m_assume m_assert entry

    let ch = checkExpr' (exprs) i reqList

    return . testCase src
        $ assertBool ("Assume/Assert for file " ++ src ++ 
                      " with functions [" ++ (fromMaybe "" m_assume) ++ "] " ++
                                      "[" ++ (fromMaybe "" m_assert) ++ "] " ++
                                              entry ++ " failed.\n") ch

-- | Checks conditions on given expressions
--   Helper for checkExprOutput checkExprReach
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

testFile :: String -> String -> Int -> Maybe String -> Maybe String -> String -> IO ([([Expr], Expr)])
testFile proj src steps m_assume m_assert entry = do
    (binds, tycons) <- translation proj src "./defs/PrimDefs.hs"

    let init_state = initState binds tycons m_assume m_assert entry

    hhp <- getZ3ProcessHandles

    r <- run smt2 hhp steps init_state

    return $ map (\(_, i, o) -> (i, o)) r

givenLengthCheck :: Int -> ([Expr] -> Bool) -> [Expr] -> Bool
givenLengthCheck i f e = if length e == i then f e else False

-- CLEAN THIS UP!
lookupFromNamesMap :: M.Map G2.Name G2.Name -> G2.Name -> G2.Name
lookupFromNamesMap nMap n =
    case M.lookup n nMap of
                Just f -> f
                Nothing -> error ("Function " ++ show n ++ " not recognized.")


replaceDataConName :: M.Map G2.Name G2.Name -> Expr -> Expr
replaceDataConName conMap = modify (replaceDataConName' conMap)
    where
        replaceDataConName' :: M.Map G2.Name G2.Name -> Expr -> Expr
        replaceDataConName' conMap (Data (DataCon n t ts)) =
            case M.lookup n conMap of
                        Just n' -> (Data (DataCon n' t ts))
                        Nothing -> error (show n ++ " not recognized.")
        replaceDataConName' _ e = e
