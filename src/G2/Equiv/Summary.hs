{-# LANGUAGE OverloadedStrings #-}

module G2.Equiv.Summary (summarize, summarizeAct) where

-- TODO may not need all imports
-- TODO add flag to disable summary printing

import G2.Language

import G2.Config

import G2.Interface

import qualified Control.Monad.State.Lazy as CM

import qualified G2.Language.ExprEnv as E
import qualified G2.Language.Typing as T
import qualified G2.Language.CallGraph as G

import Data.List
import Data.Maybe
import qualified Data.Text as DT

import qualified Data.HashSet as HS
import qualified G2.Solver as S

import qualified G2.Language.PathConds as P

import G2.Equiv.InitRewrite
import G2.Equiv.EquivADT
import G2.Equiv.G2Calls
import G2.Equiv.Tactics

import qualified Data.HashMap.Lazy as HM
import qualified Data.Map as M
import G2.Execution.Memory
import Data.Monoid (Any (..))

import Debug.Trace

import G2.Execution.NormalForms
import qualified G2.Language.Stack as Stck
import Control.Monad

import Data.Time

import G2.Execution.Reducer
import G2.Lib.Printers

import qualified Control.Monad.Writer.Lazy as W

sideName :: Side -> String
sideName ILeft = "Left"
sideName IRight = "Right"

-- TODO functions for summarizing proofs
summarizeInduction :: IndMarker -> String
summarizeInduction im =
  let (s1, s2) = ind_real_present im
      (q1, q2) = ind_used_present im
      (p1, p2) = ind_past im
  in "Induction:\n" ++
  "Real Present: " ++
  (folder_name $ track s1) ++ "," ++
  (folder_name $ track s2) ++ "\n" ++
  "Used Present: " ++
  (folder_name $ track q1) ++ "," ++
  (folder_name $ track q2) ++ "\n" ++
  "Past: " ++
  (folder_name $ track p1) ++ "," ++
  (folder_name $ track p2) ++ "\n" ++
  "Side: " ++ (sideName $ ind_side im)

summarizeCoinduction :: CoMarker -> String
summarizeCoinduction cm =
  let (s1, s2) = co_real_present cm
      (q1, q2) = co_used_present cm
      (p1, p2) = co_past cm
  in "Coinduction:\n" ++
  "Real Present: " ++
  (folder_name $ track s1) ++ "," ++
  (folder_name $ track s2) ++ "\n" ++
  "Used Present: " ++
  (folder_name $ track q1) ++ "," ++
  (folder_name $ track q2) ++ "\n" ++
  "Past: " ++
  (folder_name $ track p1) ++ "," ++
  (folder_name $ track p2)

-- TODO pretty guide type in Printers
-- TODO Named instances for Marker and other types, including EquivTracker
-- make one PrettyGuide on the whole list of markers
-- printHaskellPG
-- also print expressions for everything
-- variables:  find all names used in here
-- look them up, find a fixed point
-- print all relevant vars beside the expressions
-- maybe don't include definitions from the initial state
summarizeEquality :: EqualMarker -> String
summarizeEquality em =
  let (s1, s2) = eq_real_present em
      (q1, q2) = eq_used_present em
  in "Equivalent Expressions:\n" ++
  "Real Present: " ++
  (folder_name $ track s1) ++ ", " ++
  (folder_name $ track s2) ++ "\n" ++
  (printHaskellDirty $ exprExtract s1) ++ "\n" ++
  (printHaskellDirty $ exprExtract s2) ++ "\n" ++
  "Used States: " ++
  (folder_name $ track q1) ++ ", " ++
  (folder_name $ track q2) ++ "\n" ++
  (printHaskellDirty $ exprExtract q1) ++ "\n" ++
  (printHaskellDirty $ exprExtract q2)

summarizeNoObligations :: (StateET, StateET) -> String
summarizeNoObligations (s1, s2) =
  "No Obligations Produced:\n" ++
  (folder_name $ track s1) ++ ", " ++
  (folder_name $ track s2) ++ "\n" ++
  (printHaskellDirty $ exprExtract s1) ++ "\n" ++
  (printHaskellDirty $ exprExtract s2)

summarizeNotEquivalent :: (StateET, StateET) -> String
summarizeNotEquivalent (s1, s2) =
  "NOT EQUIVALENT:\n" ++
  (folder_name $ track s1) ++ ", " ++
  (folder_name $ track s2) ++ "\n" ++
  (printHaskellDirty $ exprExtract s1) ++ "\n" ++
  (printHaskellDirty $ exprExtract s2)

summarizeSolverFail :: (StateET, StateET) -> String
summarizeSolverFail (s1, s2) =
  "SOLVER FAIL:\n" ++
  (folder_name $ track s1) ++ ", " ++
  (folder_name $ track s2) ++ "\n" ++
  (printHaskellDirty $ exprExtract s1) ++ "\n" ++
  (printHaskellDirty $ exprExtract s2)

summarizeAct :: ActMarker -> String
summarizeAct m = case m of
  Induction im -> summarizeInduction im
  Coinduction cm -> summarizeCoinduction cm
  Equality em -> summarizeEquality em
  NoObligations s_pair -> summarizeNoObligations s_pair
  NotEquivalent s_pair -> summarizeNotEquivalent s_pair
  SolverFail s_pair -> summarizeSolverFail s_pair

tabsAfterNewLines :: String -> String
tabsAfterNewLines [] = []
tabsAfterNewLines ('\n':t) = '\n':'\t':(tabsAfterNewLines t)
tabsAfterNewLines (c:t) = c:(tabsAfterNewLines t)

summarize :: Marker -> String
summarize (Marker (sh1, sh2) m) =
  "***\nLeft Path: " ++
  (foldr (\s acc -> acc ++ " -> " ++ s) "Start" $ map (folder_name . track) $ history sh1) ++
  "\nRight Path: " ++
  (foldr (\s acc -> acc ++ " -> " ++ s) "Start" $ map (folder_name . track) $ history sh2) ++ "\n" ++
  (tabsAfterNewLines $ summarizeAct m)
