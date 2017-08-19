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
main = do return ()
    --defaultMain =<< tests

{-
tests = return . testGroup "Tests"
    =<< sequence [
          sampleTests
        , testFileTests
        ]

-- Test based on examples that are also good for demos
sampleTests =
    return . testGroup "Samples"
        =<< sequence [
                -- , checkExpr "tests/samples/" "tests/samples/Peano.hs" (Just "fstIsEvenAddToFour") (Just "fstIsTwo") "add" 2 [RExists peano_0_4, RExists peano_4_0, Exactly 2]
                -- , checkExpr "tests/samples/" "tests/samples/Peano.hs" (Just "multiplyToFour") (Just "equalsFour") "add" 2 [RExists peano_1_4, RExists peano_4_1, Exactly 2]
                  checkExpr "tests/samples/" "tests/samples/Peano.hs" (Just "equalsFour") Nothing "add" 2 [RExists peano_0_4, RExists peano_1_3, RExists peano_2_2, RExists peano_3_1, RExists peano_4_0, Exactly 5]
                , checkExpr "tests/samples/" "tests/samples/Peano.hs" (Just "eqEachOtherAndAddTo4") Nothing "add" 2 [RForAll peano_2_2, Exactly 1]
                , checkExpr "tests/samples/" "tests/samples/Peano.hs" (Just "equalsFour") Nothing "multiply" 2 [RExists peano_1_4, RExists peano_2_2, RExists peano_4_1, Exactly 3]

                , checkExpr "tests/samples/" "tests/samples/HigherOrderMath.hs" (Just "isTrue0") Nothing "notNegativeAt0NegativeAt1" 1 [RExists negativeSquareRes, AtLeast 1]
                , checkExpr "tests/samples/" "tests/samples/HigherOrderMath.hs" (Just "isTrue1") Nothing "fixed" 2 [RExists abs2NonNeg, RExists abs2Neg, RExists squareRes, RExists fourthPowerRes, AtLeast 4]
                , checkExpr "tests/samples/" "tests/samples/HigherOrderMath.hs" (Just "isTrue2") Nothing "sameDoubleArgLarger" 2 [RExists addRes, RExists subRes, RExists pythagoreanRes, AtLeast 2]
                , checkExprWithOutput "tests/samples/" "tests/samples/HigherOrderMath.hs" Nothing Nothing "functionSatisfies" 4 [RExists functionSatisfiesRes, AtLeast 1]

                , checkExpr "tests/samples/" "tests/samples/McCarthy91.hs" (Just "lessThan91") Nothing "mccarthy" 1 [RForAll (\[Lit (LitInt x)] -> x <= 100), AtLeast 1]
                , checkExpr "tests/samples/" "tests/samples/McCarthy91.hs" (Just "greaterThan10Less") Nothing "mccarthy" 1 [RForAll (\[Lit (LitInt x)] -> x > 100), AtLeast 1]
                , checkExpr "tests/samples/" "tests/samples/McCarthy91.hs" (Just "lessThanNot91") Nothing "mccarthy" 1 [Exactly 0]
                , checkExpr "tests/samples/" "tests/samples/McCarthy91.hs" (Just "greaterThanNot10Less") Nothing "mccarthy" 1 [Exactly 0]
        ]

-- Tests that are intended to ensure a specific feature works, but that are not neccessarily interesting beyond that
testFileTests = 
    return . testGroup "Samples"
        =<< sequence [
                  checkExprWithOutput "tests/TestFiles/" "tests/TestFiles/IfTest.hs" Nothing Nothing "f" 3 [RForAll (\[Lit (LitInt x), Lit (LitInt y), (Lit (LitInt r))] -> if x == y then r == x + y else r == y), AtLeast 2]

                , checkExpr "tests/TestFiles/" "tests/TestFiles/AssumeAssert.hs" Nothing (Just "assertGt5") "outShouldBeGt5" 1 [Exactly 0]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/AssumeAssert.hs" Nothing (Just "assertGt5") "outShouldBeGe5" 1 [AtLeast 1]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/AssumeAssert.hs" (Just "assumeGt5") (Just "assertGt5") "outShouldBeGt5" 1 [Exactly 0]
                , checkExpr "tests/TestFiles/" "tests/TestFiles/AssumeAssert.hs" (Just "assumeGt5") (Just "assertGt5") "outShouldBeGe5" 1 [Exactly 0]

                -- , checkExpr "tests/TestFiles/" "tests/TestFiles/MultCase.hs" Nothing Nothing "f" 2
                --     [ RExists (\[Const(CDouble x), y] -> x == 2 && y == (Data $ PrimCon DTrue))
                --     , RExists (\[Const(CDouble x), y] -> x == 1 && y == (Data $ PrimCon DFalse))
                --     , RExists (\[Const(CDouble x), y] -> x /= 2 && x /= 1 && y == (Data $ PrimCon DFalse))]
        ]


checkExpr :: String -> String -> Maybe String -> Maybe String -> String -> Int -> [Reqs] -> IO TestTree
checkExpr proj src m_assume m_assert entry i reqList = do
    exprs <- return . map fst =<< testFile proj src m_assume m_assert entry

    let ch = checkExpr' exprs i reqList

    return . testCase src
        $ assertBool ("Assume/Assert for file " ++ src ++ 
                      " with functions [" ++ (fromMaybe "" m_assume) ++ "] " ++
                                      "[" ++ (fromMaybe "" m_assert) ++ "] " ++
                                              entry ++ " failed.\n") ch

checkExprWithOutput :: String -> String -> Maybe String -> Maybe String -> String -> Int -> [Reqs] -> IO TestTree
checkExprWithOutput proj src m_assume m_assert entry i reqList = do
    exprs <- return . map (\(a, b) -> a ++ [b]) =<<  testFile proj src m_assume m_assert entry

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

testFile :: String -> String -> Maybe String -> Maybe String -> String -> IO ([([Expr], Expr)])
testFile proj src m_assume m_assert entry = do
    (tenv, eenv, varN, conN) <- hskToG2 proj src

    let revVarN = M.fromList . map swap $ M.toList varN

    let entry' = lookupFromNamesMap varN entry
    let assume = return . lookupFromNamesMap varN =<< m_assume
    let assert = return . lookupFromNamesMap varN =<< m_assert

    let init_state = initState tenv eenv assume assert entry'

    hhp <- getZ3ProcessHandles

    in_out <- run smt2 hhp 200 init_state
    
    mapM (\(inArg, ex) -> do
            let inArg' = map (maybeReplaceVarName revVarN) . map (replaceDataConName conN) $ inArg
            let ex' = replaceDataConName conN ex
            return (inArg', ex')
        ) in_out

givenLengthCheck :: Int -> ([Expr] -> Bool) -> [Expr] -> Bool
givenLengthCheck i f e = if length e == i then f e else False

-- CLEAN THIS UP!
lookupFromNamesMap :: M.Map G2.Name G2.Name -> G2.Name -> G2.Name
lookupFromNamesMap nMap n =
    case M.lookup n nMap of
                Just f -> f
                Nothing -> error ("Function " ++ n ++ " not recognized.")

maybeReplaceVarName :: M.Map G2.Name G2.Name -> Expr -> Expr
maybeReplaceVarName nMap v@(Var n t) =
    case M.lookup n nMap of
        Just n' -> Var n' t
        Nothing -> v
maybeReplaceVarName _ e = e

replaceDataConName :: M.Map G2.Name G2.Name -> Expr -> Expr
replaceDataConName conMap = modify (replaceDataConName' conMap)
    where
        replaceDataConName' :: M.Map G2.Name G2.Name -> Expr -> Expr
        replaceDataConName' conMap (Data (DataCon n i t ts)) =
            case M.lookup n conMap of
                        Just n' -> (Data (DataCon n' i t ts))
                        Nothing -> error (n ++ " not recognized.")
        replaceDataConName' _ e = e
-}
