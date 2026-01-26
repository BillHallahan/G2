module Reqs ( Reqs (..)
            , TestErrors (..)
            , checkExprGen ) where

import G2.Language
import G2.Interface.ExecRes

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

data TestErrors = BadArgCount [Int]
                | TooMany
                | TooFew
                | NotExactly
                | ArgsForAllFailed
                | ArgsExistFailed 
                | Time deriving (Show)

toExprList :: ExecRes t -> [Expr]
toExprList (ExecRes { final_state = State { error_raised = True }, conc_args = inp }) = inp ++ [Prim Error TyBottom]
toExprList (ExecRes { conc_args = inp, conc_out = out }) = inp ++ [out]

-- | Checks conditions on given expressions
checkExprGen :: [ExecRes t] -> [Reqs ([Expr] -> Bool)] -> [TestErrors]
checkExprGen ers reqList =
    let
        exprs = map toExprList ers

        argChecksAll = if and . map (\f -> all f exprs) $ [f | RForAll f <- reqList]
                        then []
                        else [ArgsForAllFailed]
        argChecksEx = if and . map (\f -> any f exprs) $ [f | RExists f <- reqList]
                        then []
                        else [ArgsExistFailed]
        checkL = checkLengths exprs reqList
    in
    argChecksAll ++ argChecksEx ++ checkL

checkLengths :: [[Expr]] -> [Reqs c] -> [TestErrors]
checkLengths exprs reqList =
    let
        checkAtLeast = if and . map ((>=) (length exprs)) $ [x | AtLeast x <- reqList] then [] else [TooFew]
        checkAtMost = if and . map ((<=) (length exprs)) $ [x | AtMost x <- reqList] then [] else [TooMany]
        checkExactly = if and . map ((==) (length exprs)) $ [x | Exactly x <- reqList] then [] else [NotExactly]
    in
    checkAtLeast ++ checkAtMost ++ checkExactly

