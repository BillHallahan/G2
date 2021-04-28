module RewriteVerify.RewriteVerifyTest (rewriteVerifyTests) where

-- TODO imports, also include in cabal file
-- actually cabal inclusion might not matter
-- TODO not all of these imports may be necessary

import DynFlags

import System.Environment
import System.FilePath

import qualified Data.Map as M
import Data.Maybe
import qualified Data.Text as T

import G2.Lib.Printers

import G2.Config
import G2.Interface
import G2.Language
import G2.Translation

import G2.Liquid.Interface
import G2.Equiv.InitRewrite
import G2.Equiv.EquivADT
import G2.Equiv.Verifier

import Control.Exception

import Data.List

import qualified G2.Solver as S

-- TODO trying to make this into a TestTree
import Test.Tasty
import Test.Tasty.HUnit

mainTest :: IO ()
mainTest = do
  as <- getArgs
  let (src:entry:tail_args) = as
  let m_mapsrc = mkMapSrc tail_args
  -- TODO how much of the old structure do I preserve?
  proj <- guessProj src
  -- let tentry = T.pack entry
  config <- getConfig as
  let libs = maybeToList m_mapsrc
  (init_state, bindings) <- initialStateNoStartFunc [proj] [src] libs
                            (TranslationConfig {simpl = True, load_rewrite_rules = True}) config

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

  mapM_ (checkRule config init_state bindings) good_rules
  mapM_ (checkRule config init_state bindings) bad_rules
  return ()

findRule :: [RewriteRule] -> String -> RewriteRule
findRule rule_list rule_name =
  let tentry = T.pack rule_name
      rule = find (\r -> tentry == ru_name r) rule_list
  in case rule of
      Just r -> r
      Nothing -> error "not found"

checkRule :: Config -> State t -> Bindings -> RewriteRule -> IO ()
checkRule config init_state bindings rule = do
  let (rewrite_state_l, bindings_l) = initWithLHS init_state bindings $ rule
      (rewrite_state_r, bindings_r) = initWithRHS init_state bindings $ rule
      pairs_l = symbolic_ids rewrite_state_l
      pairs_r = symbolic_ids rewrite_state_r

  S.SomeSolver solver <- initSolver config
  -- TODO convert from State t to State ()
  res <- verifyLoop solver (zip pairs_l pairs_r)
         [(rewrite_state_l {track = ()}, rewrite_state_r {track = ()})]
         bindings_l bindings_r config
  print res
  return ()

-- TODO copied from Main.hs
mkMapSrc :: [String] -> Maybe String
mkMapSrc a = strArg "mapsrc" a M.empty Just Nothing

-- TODO for the test suite
rewriteVerifyTests :: TestTree
rewriteVerifyTests = testCase "RewriteRuleVerify" mainTest
