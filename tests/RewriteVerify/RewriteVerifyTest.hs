module RewriteVerify.RewriteVerifyTest
    ( rewriteVerifyTestsGood
    , rewriteVerifyTestsBad
    , coinductionTestsGood
    , coinductionTestsBad
    ) where

-- TODO better test suite naming?

import qualified Data.Map as M
import Data.Maybe
import qualified Data.Text as T

import G2.Config
import G2.Interface
import G2.Language
import G2.Translation

import G2.Equiv.Verifier

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
      Nothing -> error "not found"

acceptRule :: Config -> State t -> Bindings -> RewriteRule -> IO ()
acceptRule config init_state bindings rule = do
  res <- checkRule config init_state bindings rule
  return (case res of
    S.SAT _ -> error "Satisfiable"
    S.UNSAT _ -> ()
    _ -> error "Failed to Produce a Result")

rejectRule :: Config -> State t -> Bindings -> RewriteRule -> IO ()
rejectRule config init_state bindings rule = do
  res <- checkRule config init_state bindings rule
  return (case res of
    S.SAT _ -> ()
    S.UNSAT _ -> error "Unsatisfiable"
    _ -> error "Failed to Produce a Result")

good_names :: [String]
good_names = [ "addOneCommutative"
             , "doubleNegative"
             , "maybeForceZero"
             , "maxWithSelf"
             , "addOneJust" ]

good_src :: String
good_src = "tests/RewriteVerify/Correct/SimpleCorrect.hs"

bad_names :: [String]
bad_names = [ "badMaybeForce"
            , "badNegation"
            , "badMax"
            , "badMaxLeft" ]

bad_src :: String
bad_src = "tests/RewriteVerify/Incorrect/SimpleIncorrect.hs"

coinduction_good_names :: [String]
coinduction_good_names = [ -- "forceIdempotent"
                         -- , "dropNoRecursion"
                         -- , "takeIdempotent"
                         -- , "doubleReverse" ]
                         "doubleMap" ]
                         -- , "mapIterate" ]

coinduction_good_src :: String
coinduction_good_src = "tests/RewriteVerify/Correct/CoinductionCorrect.hs"

coinduction_bad_names :: [String]
coinduction_bad_names = [ "forceDoesNothing"
                        , "badDropSum"
                        , "doubleTake"
                        , "badDoubleReverse" ]

coinduction_bad_src :: String
coinduction_bad_src = "tests/RewriteVerify/Incorrect/CoinductionIncorrect.hs"

-- no need for general mkMapSrc
libs :: [String]
libs = maybeToList $ strArg "mapsrc" [] M.empty Just Nothing

empty_config :: IO Config
empty_config = getConfig []

rvTest :: (Config -> State () -> Bindings -> RewriteRule -> IO ()) ->
          String -> [String] -> IO ()
rvTest check src rule_names = do
  proj <- guessProj src
  config <- empty_config
  (init_state, bindings) <- initialStateNoStartFunc [proj] [src] libs
                            (TranslationConfig {simpl = True, load_rewrite_rules = True})
                            config
  let rules = map (findRule $ rewrite_rules bindings) rule_names
  mapM_ (check config init_state bindings) rules
  return ()

rewriteVerifyTestsGood :: TestTree
rewriteVerifyTestsGood =
  testCase "RewriteRuleVerifyGood" $ rvTest acceptRule good_src good_names

rewriteVerifyTestsBad :: TestTree
rewriteVerifyTestsBad =
  testCase "RewriteRuleVerifyBad" $ rvTest rejectRule bad_src bad_names

coinductionTestsGood :: TestTree
coinductionTestsGood =
  testCase "CoinductionGood" $ rvTest acceptRule coinduction_good_src coinduction_good_names

coinductionTestsBad :: TestTree
coinductionTestsBad =
  testCase "CoinductionBad" $ rvTest rejectRule coinduction_bad_src coinduction_bad_names
