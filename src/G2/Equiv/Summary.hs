{-# LANGUAGE OverloadedStrings #-}

module G2.Equiv.Summary (summarize, summarizeAct) where

-- TODO may not need all imports

import G2.Language

import G2.Config

import G2.Interface

import Data.List
import Data.Maybe

import G2.Equiv.InitRewrite
import G2.Equiv.EquivADT
import G2.Equiv.G2Calls
import G2.Equiv.Tactics

import G2.Execution.Memory

import Debug.Trace

import G2.Execution.NormalForms
import Control.Monad

import Data.Time

import G2.Execution.Reducer
import G2.Lib.Printers

sideName :: Side -> String
sideName ILeft = "Left"
sideName IRight = "Right"

printPG :: PrettyGuide -> StateET -> String
printPG pg s = printHaskellPG pg s $ exprExtract s

-- TODO print the name differently?
summarizeInduction :: PrettyGuide -> IndMarker -> String
summarizeInduction pg im@(IndMarker {
                        ind_real_present = (s1, s2)
                      , ind_used_present = (q1, q2)
                      , ind_past = (p1, p2)
                      , ind_result = (s1', s2')
                      , ind_present_scrutinees = (e1, e2)
                      , ind_past_scrutinees = (r1, r2)
                      }) =
  "Induction:\n" ++
  "Real Present: " ++
  (folder_name $ track s1) ++ "," ++
  (folder_name $ track s2) ++ "\n" ++
  (printPG pg s1) ++ "\n" ++
  (printPG pg s2) ++ "\n" ++
  "Used Present: " ++
  (folder_name $ track q1) ++ "," ++
  (folder_name $ track q2) ++ "\n" ++
  (printPG pg q1) ++ "\n" ++
  (printPG pg q2) ++ "\n" ++
  "Past: " ++
  (folder_name $ track p1) ++ "," ++
  (folder_name $ track p2) ++ "\n" ++
  (printPG pg p1) ++ "\n" ++
  (printPG pg p2) ++ "\n" ++
  "Side: " ++ (sideName $ ind_side im) ++ "\n" ++
  "Result:\n" ++
  (printPG pg s1') ++ "\n" ++
  (printPG pg s2') ++ "\n" ++
  "Present Sub-Expressions Used for Induction:\n" ++
  (printHaskellPG pg q1 e1) ++ "\n" ++
  (printHaskellPG pg q2 e2) ++ "\n" ++
  "Past Sub-Expressions Used for Induction:\n" ++
  (printPG pg r1) ++ "\n" ++
  (printPG pg r2) ++ "\n" ++
  "New Variable Name: " ++ (show $ ind_fresh_name im)

summarizeCoinduction :: PrettyGuide -> CoMarker -> String
summarizeCoinduction pg (CoMarker {
                          co_real_present = (s1, s2)
                        , co_used_present = (q1, q2)
                        , co_past = (p1, p2)
                        }) =
  "Coinduction:\n" ++
  "Real Present: " ++
  (folder_name $ track s1) ++ "," ++
  (folder_name $ track s2) ++ "\n" ++
  (printPG pg s1) ++ "\n" ++
  (printPG pg s2) ++ "\n" ++
  "Used Present: " ++
  (folder_name $ track q1) ++ "," ++
  (folder_name $ track q2) ++ "\n" ++
  (printPG pg q1) ++ "\n" ++
  (printPG pg q2) ++ "\n" ++
  "Past: " ++
  (folder_name $ track p1) ++ "," ++
  (folder_name $ track p2) ++ "\n" ++
  (printPG pg p1) ++ "\n" ++
  (printPG pg p2)

-- TODO pretty guide type in Printers
-- variables:  find all names used in here
-- look them up, find a fixed point
-- print all relevant vars beside the expressions
-- maybe don't include definitions from the initial state
summarizeEquality :: PrettyGuide -> EqualMarker -> String
summarizeEquality pg (EqualMarker {
                       eq_real_present = (s1, s2)
                     , eq_used_present = (q1, q2)
                     }) =
  "Equivalent Expressions:\n" ++
  "Real Present: " ++
  (folder_name $ track s1) ++ ", " ++
  (folder_name $ track s2) ++ "\n" ++
  (printPG pg s1) ++ "\n" ++
  (printPG pg s2) ++ "\n" ++
  "Used States: " ++
  (folder_name $ track q1) ++ ", " ++
  (folder_name $ track q2) ++ "\n" ++
  (printPG pg q1) ++ "\n" ++
  (printPG pg q2)

summarizeNoObligations :: PrettyGuide -> (StateET, StateET) -> String
summarizeNoObligations pg (s1, s2) =
  "No Obligations Produced:\n" ++
  (folder_name $ track s1) ++ ", " ++
  (folder_name $ track s2) ++ "\n" ++
  (printPG pg s1) ++ "\n" ++
  (printPG pg s2)

summarizeNotEquivalent :: PrettyGuide -> (StateET, StateET) -> String
summarizeNotEquivalent pg (s1, s2) =
  "NOT EQUIVALENT:\n" ++
  (folder_name $ track s1) ++ ", " ++
  (folder_name $ track s2) ++ "\n" ++
  (printPG pg s1) ++ "\n" ++
  (printPG pg s2)

summarizeSolverFail :: PrettyGuide -> (StateET, StateET) -> String
summarizeSolverFail pg (s1, s2) =
  "SOLVER FAIL:\n" ++
  (folder_name $ track s1) ++ ", " ++
  (folder_name $ track s2) ++ "\n" ++
  (printPG pg s1) ++ "\n" ++
  (printPG pg s2)

summarizeAct :: PrettyGuide -> ActMarker -> String
summarizeAct pg m = case m of
  Induction im -> summarizeInduction pg im
  Coinduction cm -> summarizeCoinduction pg cm
  Equality em -> summarizeEquality pg em
  NoObligations s_pair -> summarizeNoObligations pg s_pair
  NotEquivalent s_pair -> summarizeNotEquivalent pg s_pair
  SolverFail s_pair -> summarizeSolverFail pg s_pair

tabsAfterNewLines :: String -> String
tabsAfterNewLines [] = []
tabsAfterNewLines ('\n':t) = '\n':'\t':(tabsAfterNewLines t)
tabsAfterNewLines (c:t) = c:(tabsAfterNewLines t)

-- generate the guide for the whole summary externally
summarize :: PrettyGuide -> Marker -> String
summarize pg (Marker (sh1, sh2) m) =
  "***\nLeft Path: " ++
  (foldr (\s acc -> acc ++ " -> " ++ s) "Start" $ map (folder_name . track) $ (latest sh1):history sh1) ++
  "\nRight Path: " ++
  (foldr (\s acc -> acc ++ " -> " ++ s) "Start" $ map (folder_name . track) $ (latest sh2):history sh2) ++ "\n" ++
  (tabsAfterNewLines $ summarizeAct pg m)
