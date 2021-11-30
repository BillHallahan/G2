{-# LANGUAGE OverloadedStrings #-}

module G2.Equiv.Summary (summarize) where

-- TODO may not need all imports

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
  let (s1, s2) = co_present cm
      (p1, p2) = co_past cm
  in "Coinduction:\n" ++
  (folder_name $ track s1) ++ " matches " ++
  (folder_name $ track p1) ++ "\n" ++
  (folder_name $ track s2) ++ " matches " ++
  (folder_name $ track p2)

-- TODO equivalence may not be between the two real present states
-- would need to record more information beforehand
summarizeEquivalence :: (StateET, StateET) -> String
summarizeEquivalence (s1, s2) =
  "Equivalent Expressions:\n" ++
  (folder_name $ track s1) ++ ", " ++
  (folder_name $ track s2) ++ "\n" ++
  (printHaskellDirty $ exprExtract s1) ++ "\n" ++
  (printHaskellDirty $ exprExtract s2)

summarizeNoObligations :: (StateET, StateET) -> String
summarizeNoObligations (s1, s2) =
  "No Obligations Produced:\n" ++
  (folder_name $ track s1) ++ ", " ++
  (folder_name $ track s2) ++ "\n" ++
  (printHaskellDirty $ exprExtract s1) ++ "\n" ++
  (printHaskellDirty $ exprExtract s2)

summarize :: Marker -> String
summarize m = case m of
  Induction im -> summarizeInduction im
  Coinduction cm -> summarizeCoinduction cm
  Equivalence s_pair -> summarizeEquivalence s_pair
  NoObligations s_pair -> summarizeNoObligations s_pair
  NotEquivalent _ -> "NOT EQUIVALENT"
  SolverFail _ -> "SOLVER FAIL"
