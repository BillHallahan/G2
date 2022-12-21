module ZenoSuite (suite) where

import DynFlags

import System.Environment
import System.FilePath

import qualified Data.Map as M
import Data.Maybe
import qualified Data.Text as T
import qualified G2.Solver as S

import G2.Lib.Printers

import G2.Config
import G2.Interface
import G2.Language
import G2.Translation

import G2.Liquid.Interface
import G2.Equiv.InitRewrite
import G2.Equiv.EquivADT
import G2.Equiv.Summary
import G2.Equiv.Types
import G2.Equiv.Verifier

import Control.Exception

import Data.List

rule_names1 :: [String]
rule_names1 = [
      "p01"
    , "p02"
    --, "p03"
    , "p04"
    , "p06"
    , "p07"
    , "p08"
    , "p09"
    , "p10"
    , "p11"
    , "p12"
    , "p13"
    , "p14"
    , "p15"
    , "p17"
    , "p19"
    ]

rule_names2 :: [String]
rule_names2 = [
      "p20"
    , "p22"
    , "p23"
    , "p24"
    , "p25"
    , "p31"
    , "p32"
    , "p33"
    , "p34"
    , "p35"
    , "p36"
    , "p38"
    , "p39"
    , "p40"
    , "p41"
    ]

rule_names3 :: [String]
rule_names3 = [
      "p42"
    , "p43"
    , "p44"
    , "p45"
    , "p46"
    , "p47"
    , "p49"
    , "p50"
    , "p51"
    , "p52"
    , "p53"
    , "p54"
    , "p55"
    , "p56"
    , "p57"
    ]

rule_names4 :: [String]
rule_names4 = [
      "p58"
    , "p61"
    , "p64"
    , "p67"
    , "p72"
    , "p73"
    , "p74"
    , "p75"
    , "p79"
    , "p80"
    , "p81"
    , "p82"
    , "p83"
    , "p84"
    ]

rule_names5 :: [String]
rule_names5 = [
      "p44"
    , "p45"
    , "p46"
    , "p47"
    , "p50"
    --, "p55"
    , "p80"
    , "p82"
    ]

all_empty :: [[String]]
all_empty = []:all_empty

regression1 :: [(String, [String])]
regression1 = [
    ("p01", ["n"])
  , ("p06fin", [])
  , ("p07fin", [])
  , ("p08fin", [])
  , ("p09", [])
  , ("p10fin", [])
  , ("p11", [])
  , ("p12", [])
  , ("p13", [])
  --, ("p14", [])
  , ("p17", [])
  , ("p18fin", [])
  , ("p19", ["n"])
  , ("p21fin", [])
  ]

regression2 :: [(String, [String])]
regression2 = [
    ("p22", [])
  , ("p23", [])
  , ("p31", [])
  , ("p32", ["a", "b"])
  , ("p33", [])
  , ("p34", ["a"])
  , ("p35", [])
  , ("p36", [])
  , ("p40", [])
  , ("p41", [])
  , ("p42", [])
  --, ("p43", ["p", "xs"])
  , ("p44", [])
  , ("p45", [])
  ]

regression3 :: [(String, [String])]
regression3 = [
    ("p46", [])
  , ("p47", [])
  , ("p49", ["xs", "ys"])
  , ("p50", [])
  --, ("p51", ["xs"])
  , ("p64fin", [])
  , ("p67", [])
  --, ("p73", ["p", "xs"])
  , ("p79", ["n"])
  , ("p80", [])
  , ("p82", [])
  , ("p83", ["ys"])
  , ("p84", ["ys"])
  ]

rule_inputs :: [[(String, [String])]]
rule_inputs = [regression1, regression2, regression3]

rule_names :: [[String]]
rule_names = [
      rule_names1
    , rule_names2
    , rule_names3
    , rule_names4
    , rule_names5
    ]

suite :: Int -> IO ()
suite n = do
  let src = "tests/RewriteVerify/Correct/Zeno.hs"
      ri = rule_inputs !! (n - 1)
      texts = map (T.pack . fst) ri
      totals = map (\(_, v) -> map T.pack v) ri
  proj <- guessProj src
  config <- getConfig
  (init_state, bindings) <- initialStateNoStartFunc [proj] [src]
                            (TranslationConfig {simpl = True, load_rewrite_rules = True}) config
  let rule_maybes = map (\t -> find (\r -> t == ru_name r) (rewrite_rules bindings)) texts
      rules = map fromJust rule_maybes
  res <- mapM (\(r, t) -> checkRule config UseLabeledErrors False init_state bindings t [] NoSummary 10 r) (zip rules totals)
  print $ zip ri res
  return ()
