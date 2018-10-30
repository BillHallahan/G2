module Reqs ( Reqs (..)
            , checkExprGen
            , checkAbsLHExprGen ) where

import G2.Internals.Language

-- | Requirements
-- We use these to define checks on tests returning function inputs
--     RForall f -- All the returned inputs satisfy the function f
--     RExists f -- At least one of the returned inputs satisfies the function f
--     AtLeast x -- At least x inputs are returned
--     AtMost  x -- At most x inputs are returned
--     Exactly x -- Exactly x inputs are returned
data Reqs c = RForAll c
              | RExists c
              | AtLeast Int
              | AtMost Int
              | Exactly Int

data TestErrors = BadArgCount
                | TooMany
                | TooFew
                | NotExactly
                | ArgsForAllFailed
                | ArgsExistFailed deriving (Show)

-- | Checks conditions on given expressions
checkExprGen :: [[Expr]] -> Int -> [Reqs ([Expr] -> Bool)] -> Bool
checkExprGen exprs i reqList =
    let
        argChecksAll = and . map (\f -> all (givenLengthCheck i f) exprs) $ [f | RForAll f <- reqList]
        argChecksEx = and . map (\f -> any (givenLengthCheck i f) exprs) $ [f | RExists f <- reqList]
        checkL = null $ checkLengths exprs i reqList
    in
    argChecksAll && argChecksEx && checkL

givenLengthCheck :: Int -> ([Expr] -> Bool) -> [Expr] -> Bool
givenLengthCheck i f e = if length e == i then f e else False

checkAbsLHExprGen :: [(State [FuncCall], [Expr], Expr)] -> Int -> [Reqs ([Expr] -> Expr -> [FuncCall] -> Bool)] -> [TestErrors] 
checkAbsLHExprGen exprs i reqList =
    let
        argChecksAll =
            if and . map (\f -> all (\(s, es, e) -> lhGivenLengthCheck i f es e (track s)) exprs) $ [f | RForAll f <- reqList]
                then []
                else [ArgsForAllFailed]
        argChecksEx =
            if and . map (\f -> any (\(s, es, e) -> lhGivenLengthCheck i f es e (track s)) exprs) $ [f | RExists f <- reqList]
                then []
                else [ArgsExistFailed]
        checkL = checkLengths (map (\(_, e, _) -> e) exprs) i reqList
    in
    argChecksAll ++ argChecksEx ++ checkL

lhGivenLengthCheck :: Int -> ([Expr] -> Expr -> [FuncCall] -> Bool) -> [Expr] -> Expr -> [FuncCall] -> Bool
lhGivenLengthCheck i f es e fc = if length es == i then f es e fc else False

checkLengths :: [[Expr]] -> Int -> [Reqs c] -> [TestErrors]
checkLengths exprs i reqList =
    let
        checkAtLeast = if and . map ((>=) (length exprs)) $ [x | AtLeast x <- reqList] then [] else [TooFew]
        checkAtMost = if and . map ((<=) (length exprs)) $ [x | AtMost x <- reqList] then [] else [TooMany]
        checkExactly = if and . map ((==) (length exprs)) $ [x | Exactly x <- reqList] then [] else [NotExactly]

        checkArgCount = if and . map ((==) i . length) $ exprs then [] else [BadArgCount]
    in
    checkAtLeast ++ checkAtMost ++ checkExactly ++ checkArgCount

