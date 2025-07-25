{-# LANGUAGE FlexibleContexts #-}

module RewriteVerify.RewriteVerifyTest ( rewriteTests ) where

import qualified Data.Map as M
import Data.Maybe
import qualified Data.Text as T

import G2.Config
import G2.Interface
import G2.Language
import G2.Translation

import G2.Equiv.Config
import G2.Equiv.Verifier
import G2.Equiv.Summary

import Data.List

import qualified G2.Solver as S

import Test.Tasty
import Test.Tasty.HUnit

findRule :: [RewriteRule] -> String -> RewriteRule
findRule rule_list rule_name =
  let tentry = T.pack rule_name
      rule = find (\r -> tentry == ru_name r) rule_list
  in case rule of
      Just r -> r
      Nothing -> error $ "not found " ++ show rule_name

acceptRule ::  (ASTContainer t Type, ASTContainer t Expr) => Config -> State t -> Bindings -> RewriteRule -> IO Bool
acceptRule config init_state bindings rule = do
  res <- checkRule config nebulaConfig init_state bindings [] rule
  return (case res of
    S.SAT _ -> error "Satisfiable"
    S.UNSAT _ -> True
    _ -> error "Failed to Produce a Result")

rejectRule :: (ASTContainer t Type, ASTContainer t Expr) => Config -> State t -> Bindings -> RewriteRule -> IO Bool
rejectRule config init_state bindings rule = do
  res <- checkRule config nebulaConfig init_state bindings [] rule
  return (case res of
    S.SAT _ -> True
    S.UNSAT _ -> error "Unsatisfiable"
    _ -> error "Failed to Produce a Result")

nebulaConfig :: NebulaConfig
nebulaConfig = NC { limit = 20
                  , num_lemmas = 2
                  , print_summary = SM False False False False
                  , use_labeled_errors = UseLabeledErrors
                  , log_states = NoLog
                  , log_rule = Nothing
                  , symbolic_unmapped = False
                  , sync = False}

good_names :: [String]
good_names = [ "addOneCommutative"
             , "doubleNegative"
             , "maybeForceZero"
             , "maxWithSelf"
             , "addOneJust"
             , "justJust" ]

good_src :: String
good_src = "tests/RewriteVerify/Correct/SimpleCorrect.hs"

bad_names :: [String]
bad_names = [ "badMaybeForce"
            , "badNegation"
            , "badMax"
            , "badMaxLeft"
            , "badJust"
            , "badTuple"
            , "badFF" ]

bad_src :: String
bad_src = "tests/RewriteVerify/Incorrect/SimpleIncorrect.hs"

coinduction_good_names :: [String]
coinduction_good_names = [ --"forceIdempotent"
                           "dropNoRecursion"
                        --  , "mapTake"
                        --  , "takeIdempotent"
                         --, "doubleReverse"
                         , "doubleMap"
                         , "mapIterate" ]

coinduction_good_src :: String
coinduction_good_src = "tests/RewriteVerify/Correct/CoinductionCorrect.hs"

coinduction_bad_names :: [String]
coinduction_bad_names = [ "forceDoesNothing"
                        , "badDropSum"
                        , "doubleTake"
                        , "badDoubleReverse" ]

coinduction_bad_src :: String
coinduction_bad_src = "tests/RewriteVerify/Incorrect/CoinductionIncorrect.hs"

higher_good_names :: [String]
higher_good_names = [ "doubleMap"
                    , "mapIterate"
                    -- , "mapTake"
                    , "mapFilter" ]

higher_good_src :: String
higher_good_src = "tests/RewriteVerify/Correct/HigherOrderCorrect.hs"

higher_bad_names :: [String]
higher_bad_names = [ "direct"
                   , "symFuncInfExpr"
                   , "symFuncPoly"
                   , "symFuncNat" ]

higher_bad_src :: String
higher_bad_src = "tests/RewriteVerify/Incorrect/HigherOrderIncorrect.hs"

tree_good_names :: [String]
tree_good_names = [ -- "doubleTree"
                    -- "doubleTreeOriginal"
                    "doubleMapTree" ]

tree_good_src :: String
tree_good_src = "tests/RewriteVerify/Correct/TreeCorrect.hs"

tree_bad_names :: [String]
tree_bad_names = [ "badSize"
                 , "treeMapBackward" ]

tree_bad_src :: String
tree_bad_src = "tests/RewriteVerify/Incorrect/TreeIncorrect.hs"

multi_lemma_good_names :: [String]
multi_lemma_good_names = [ "p55Z"
                         , "p55nil"
                         , "p55Znil"
                         , "p80Z"
                         , "p80nil"
                         , "p80Znil" ]

multi_lemma_good_src :: String
multi_lemma_good_src = "tests/RewriteVerify/Correct/Zeno.hs"

empty_config :: IO Config
empty_config = getConfigDirect

rvTest :: (Config -> State () -> Bindings -> RewriteRule -> IO Bool) ->
          String -> [String] -> TestTree
rvTest check src rule_names =
  withResource
    (do
        proj <- guessProj Nothing src
        config <- empty_config
        initialStateNoStartFunc proj [src]
                  (simplTranslationConfig {simpl = True, load_rewrite_rules = True})
                  config
    )
    (\_ -> return ())
    (\isb -> testGroup ("Rules " ++ src)
           $ map (\rule_name -> testCase ("Rule " ++ rule_name) $ do
                    (init_state, bindings) <- isb
                    config <- empty_config
                    let rule = findRule (rewrite_rules bindings) rule_name
                    r <- doTimeout 180 $ check config init_state bindings rule
                    case r of
                        Nothing -> error "TIMEOUT"
                        Just r' | r' -> return ()
                                | otherwise -> error "test failed") rule_names)

rewriteVerifyTestsGood :: TestTree
rewriteVerifyTestsGood =
  rvTest acceptRule good_src good_names

rewriteVerifyTestsBad :: TestTree
rewriteVerifyTestsBad =
  rvTest rejectRule bad_src bad_names

coinductionTestsGood :: TestTree
coinductionTestsGood =
  rvTest acceptRule coinduction_good_src coinduction_good_names

coinductionTestsBad :: TestTree
coinductionTestsBad =
  rvTest rejectRule coinduction_bad_src coinduction_bad_names

higherOrderTestsGood :: TestTree
higherOrderTestsGood =
  rvTest acceptRule higher_good_src higher_good_names

higherOrderTestsBad :: TestTree
higherOrderTestsBad =
  rvTest rejectRule higher_bad_src higher_bad_names

treeTestsGood :: TestTree
treeTestsGood =
  rvTest acceptRule tree_good_src tree_good_names

treeTestsBad :: TestTree
treeTestsBad =
  rvTest rejectRule tree_bad_src tree_bad_names

typeSymsTestsGood :: TestTree
typeSymsTestsGood =
  rvTest acceptRule "tests/RewriteVerify/Correct/TypeSyms.hs" ["parBuffer"]

instTypeRed :: TestTree
instTypeRed =
  rvTest acceptRule "tests/RewriteVerify/Correct/TestZeno.hs" ["p12"]

multiLemmaTestsGood :: TestTree
multiLemmaTestsGood =
  rvTest acceptRule multi_lemma_good_src multi_lemma_good_names

rewriteTests :: TestTree
rewriteTests = testGroup "Rewrite Tests"
        [ rewriteVerifyTestsGood
        , rewriteVerifyTestsBad
        , coinductionTestsGood
        , coinductionTestsBad
        , higherOrderTestsGood
        , higherOrderTestsBad
        , treeTestsGood
        , treeTestsBad
        , typeSymsTestsGood
        , instTypeRed
        , multiLemmaTestsGood
        ]


