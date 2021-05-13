module RewriteVerify.RewriteVerifyTest
    ( rewriteVerifyTestsGood
    , rewriteVerifyTestsBad
    ) where

import System.Environment

import qualified Data.Map as M
import Data.Maybe
import qualified Data.Text as T

import G2.Config
import G2.Interface
import G2.Language
import G2.Translation

import G2.Equiv.InitRewrite
import G2.Equiv.Verifier

import Data.List

import qualified G2.Solver as S

import Test.Tasty
import Test.Tasty.HUnit

{-
mainTest :: IO ()
mainTest = do
  let src_good = "tests/RewriteVerify/Correct/SimpleCorrect.hs"
      src_bad = "tests/RewriteVerify/Incorrect/SimpleIncorrect.hs"
  let m_mapsrc = mkMapSrc []
  -- TODO how much of the old structure do I preserve?
  proj_good <- guessProj src_good
  proj_bad <- guessProj sr_bad
  config <- getConfig []
  let libs = maybeToList m_mapsrc
  (init_state, bindings) <- initialStateNoStartFunc [proj] [src] libs
                            (TranslationConfig {simpl = True, load_rewrite_rules = True}) config

  (init_state_good, bindings_good) <- initialStateNoStartFunc
                                      [proj_good] [src_good] libs
                                      (TranslationConfig {simpl = True, load_rewrite_rules = True})
                                      config
  (init_state_bad, bindings_bad) <- initialStateNoStartFunc
                                    [proj_bad] [src_bad] libs
                                    (TranslationConfig {simpl = True, load_rewrite_rules = True})
                                    config

  -- TODO scrape the rules directly from the files instead
  let good_names = [ "addOneCommutative"
                   , "doubleNegative"
                   , "maybeForceZero"
                   , "maxWithSelf"
                   , "addOneJust"
                   , "justJust" ]
  let bad_names = [ "badMaybeForce"
                  , "badNegation"
                  , "badMax"
                  , "badMaxLeft" ]
  let good_rules = map (findRule $ rewrite_rules bindings) good_names
      bad_rules = map (findRule $ rewrite_rules bindings) bad_names

  mapM_ (checkRule config init_state bindings True) good_rules
  mapM_ (checkRule config init_state bindings False) bad_rules
  return ()
-}

findRule :: [RewriteRule] -> String -> RewriteRule
findRule rule_list rule_name =
  let tentry = T.pack rule_name
      rule = find (\r -> tentry == ru_name r) rule_list
  in case rule of
      Just r -> r
      Nothing -> error "not found"

-- TODO don't use good-bad distinction in helper function?
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
             , "addOneJust"
             , "justJust" ]

good_src :: String
good_src = "tests/RewriteVerify/Correct/SimpleCorrect.hs"

bad_names :: [String]
bad_names = [ "badMaybeForce"
            , "badNegation"
            , "badMax"
            , "badMaxLeft" ]

bad_src :: String
bad_src = "tests/RewriteVerify/Incorrect/SimpleIncorrect.hs"

-- TODO generalize the good and bad suites with a function
rvTest :: (Config -> State () -> Bindings -> RewriteRule -> IO ()) ->
          String -> [String] -> IO ()
rvTest check src rule_names = do
  -- TODO perhaps this can be a fixed constant
  let libs = maybeToList $ mkMapSrc []
  proj <- guessProj src
  -- TODO same goes here
  config <- getConfig []
  (init_state, bindings) <- initialStateNoStartFunc [proj] [src] libs
                            (TranslationConfig {simpl = True, load_rewrite_rules = True})
                            config
  let rules = map (findRule $ rewrite_rules bindings) rule_names
  mapM_ (check config init_state bindings) rules
  return ()

-- TODO copied from Main.hs
mkMapSrc :: [String] -> Maybe String
mkMapSrc a = strArg "mapsrc" a M.empty Just Nothing

-- TODO for the test suite
--rewriteVerifyTests :: TestTree
--rewriteVerifyTests = testCase "RewriteRuleVerify" mainTest

rewriteVerifyTestsGood :: TestTree
rewriteVerifyTestsGood =
  testCase "RewriteRuleVerifyGood" $ rvTest acceptRule good_src good_names

rewriteVerifyTestsBad :: TestTree
rewriteVerifyTestsBad =
  testCase "RewriteRuleVerifyBad" $ rvTest rejectRule bad_src bad_names
