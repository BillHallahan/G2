{-# LANGUAGE OverloadedStrings #-}

module ExecSkip (execSkipTests) where

import G2.Execution.Internals.ExecSkip
import G2.Language
import qualified G2.Language.ExprEnv as E

import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import qualified Data.Text as T

import Test.Tasty
import Test.Tasty.HUnit ( testCase, assertBool )

execSkipTests :: TestTree
execSkipTests =
    testGroup "ExecSkip"
    [
      testCase "ExecSkip Memoization 1" $ assertBool "Memoization lookup returns Skip" execSkipLookup1
    , testCase "ExecSkip Memoization 2" $ assertBool "Memoization lookup returns Exec" execSkipLookup2
    , testCase "ExecSkip Memoization 3" $ assertBool "Memoization lookup updates Exec to Skip" execSkipLookup3
    , testCase "reachesSym Memoization 1" $ assertBool "Memoization lookup returns NotReachesSym" reachesSymLookup1
    , testCase "reachesSym Memoization 2" $ assertBool "Memoization lookup returns ReachesSym" reachesSymLookup2
    , testCase "reachesSym Memoization 3" $ assertBool "Memoization lookup updates ReachesSym to NotReachesSym" reachesSymLookup3
    ]

name :: T.Text -> Name
name n = Name n Nothing 0 ProvOther

-------------------------------------------------------------------------------
-- checkDelayability Memoization Tests
-------------------------------------------------------------------------------

isSkip :: ExecOrSkip -> Bool
isSkip Skip = True
isSkip _ = False

isExec :: ExecOrSkip -> Bool
isExec = not . isSkip

-- | x is mapped to SKIP in the memo table, so we should not need x's definition
execSkipLookup1 :: Bool
execSkipLookup1 =
    let
        x = name "x"
        
        eenv = E.fromList [ (x, error "looked up definition") ]
        e = Var (Id x TyLitInt)
        ng = mkNameGen (eenv, e)
        exec_names = HS.empty
        memo = HM.fromList [(x, Skip)]
    in
    isSkip . fst $ checkDelayability eenv e ng exec_names memo

-- | x, y, z, and f are all EXEC and not in SWHNF, so should just be able to look in memo table
execSkipLookup2 :: Bool
execSkipLookup2 =
    let
        x = name "x"
        y = name "y"
        z = name "z"
        f = name "f"

        err_e = Let (error "looking too deep") (error "looking too deep")
        
        eenv = E.fromList [ (x, err_e)
                          , (y, err_e)
                          , (z, err_e)
                          , (f, err_e)]
        e = Var (Id x TyLitInt)
        ng = mkNameGen (eenv, e)
        exec_names = HS.fromList [f]
        memo = HM.fromList [(x, ExecI y), (y, ExecI z), (z, ExecI f)]
    in
    isExec . fst $ checkDelayability eenv e ng exec_names memo

-- | x, y, and f are all EXEC in the memo table, but z has been rewritten and is now a SKIP.
-- Based on this, we should figure out that x is a SKIP.  We should then have memoized that y
-- is also SKIP
execSkipLookup3 :: Bool
execSkipLookup3 =
    let
        x = name "x"
        y = name "y"
        z = name "z"
        f = name "f"

        -- Do checks with x
        err_e = Let (error "looking too deep") (error "looking too deep")
        
        eenv = E.fromList [ (x, Var (Id y TyLitInt))
                          , (y, Var (Id z TyLitInt))
                          , (z, Lit (LitInt 9))
                          , (f, err_e)]
        e = Var (Id x TyLitInt)
        ng = mkNameGen (eenv, e)
        exec_names = HS.fromList [f]
        memo = HM.fromList [(x, ExecI y), (y, ExecI z), (z, ExecI f)]

        (x_es, memo') = checkDelayability eenv e ng exec_names memo

        -- Now do checks with y- memoization result for y should have been updated
        eenv' = E.fromList [ (x, err_e)
                           , (y, err_e)
                           , (z, err_e)
                           , (f, err_e)]
        e' = Var (Id y TyLitInt)

        (y_es, _) = checkDelayability eenv' e' ng exec_names memo'
    in
    isSkip x_es && isSkip y_es

-------------------------------------------------------------------------------
-- reachesSymbolic Memoization Tests
-------------------------------------------------------------------------------

-- | x is mapped to NotReachesSymbolic in the memo table, so we should not need x's definition
reachesSymLookup1 :: Bool
reachesSymLookup1 =
    let
        x = name "x"
        
        eenv = E.fromList [ (x, error "looked up definition") ]
        e = Var (Id x TyLitInt)
        memo = HM.fromList [(x, NotReachesSym)]
    in
    not . fst $ reachesSymbolic memo eenv e

-- | x, y, z, and f are all ReachesSymbolic and not in SWHNF, so should just be able to look in memo table
reachesSymLookup2 :: Bool
reachesSymLookup2 =
    let
        x = name "x"
        y = name "y"
        z = name "z"
        f = name "f"

        err_e = Let (error "looking too deep") (error "looking too deep")
        
        eenv = E.insertSymbolic (Id f TyLitInt) $ 
               E.fromList [ (x, err_e)
                          , (y, err_e)
                          , (z, err_e)]
        e = Var (Id x TyLitInt)
        memo = HM.fromList [(x, ReachesSym (Just y)), (y, ReachesSym (Just z)), (z, ReachesSym (Just f))]
    in
    fst $ reachesSymbolic memo eenv e

-- | x, y, and f are all ReachesSymbolic in the memo table, but z has been rewritten and is now NotReachesSymbolic.
-- Based on this, we should figure out that x is NotReachesSymbolic.  We should then have memoized that y
-- is also NotReachesSymbolic
reachesSymLookup3 :: Bool
reachesSymLookup3 =
    let
        x = name "x"
        y = name "y"
        z = name "z"
        f = name "f"

        -- Do checks with x
        err_e = Let (error "looking too deep") (error "looking too deep")
        
        eenv = E.insertSymbolic (Id f TyLitInt) $ 
               E.fromList [ (x, Var (Id y TyLitInt))
                          , (y, Var (Id z TyLitInt))
                          , (z, Lit (LitInt 9)) ]
        e = Var (Id x TyLitInt)
        memo = HM.fromList [(x, ReachesSym (Just y)), (y, ReachesSym (Just z)), (z, ReachesSym (Just f))]

        (x_rs, memo') = reachesSymbolic memo eenv e

        -- Now do checks with y- memoization result for y should have been updated
        eenv' = E.fromList [ (x, err_e)
                           , (y, err_e)
                           , (z, err_e)
                           , (f, err_e)]
        e' = Var (Id y TyLitInt)

        (y_rs, _) = reachesSymbolic memo' eenv' e'
    in
    not x_rs && not y_rs