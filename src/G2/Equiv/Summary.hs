{-# LANGUAGE OverloadedStrings #-}

module G2.Equiv.Summary (summarize, summarizeAct) where

-- TODO may not need all imports

import G2.Language

import G2.Config

import G2.Interface

import qualified G2.Language.ExprEnv as E

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

printPG :: PrettyGuide -> [Name] -> StateET -> String
printPG pg ns s =
  let h = expr_env s
  in
  (printHaskellPG pg s $ exprExtract s) ++
  "\nVariables:" ++
  (printVars pg ns s)

data ChainEnd = Symbolic
              | Cycle Id
              | Terminal Expr
              | Unmapped

-- don't include ns names in the result here
varsInExpr :: [Name] -> Expr -> [Id]
varsInExpr ns e =
  let ids = evalASTs (\e_ -> case e_ of
                               Var i -> [i]
                               _ -> []) e
  in filter (\i -> not ((idName i) `elem` ns)) ids

-- TODO some names could have cycles
-- TODO right additions to inlined list?
-- TODO need to take new bindings into account; don't display those
-- TODO i is same as i' for symbolic
varChain :: ExprEnv -> [Name] -> [Id] -> Id -> ([Id], ChainEnd)
varChain h ns inlined i =
  if i `elem` inlined then (reverse inlined, Cycle i)
  else if (idName i) `elem` ns then (reverse inlined, Terminal $ Var i)
  else case E.lookupConcOrSym (idName i) h of
    Nothing -> ([], Unmapped)
    Just (E.Sym i') -> (reverse (i':inlined), Symbolic)
    Just (E.Conc e) -> exprChain h ns (i:inlined) e

exprChain :: ExprEnv -> [Name] -> [Id] -> Expr -> ([Id], ChainEnd)
exprChain h ns inlined e = case e of
  Tick _ e' -> exprChain h ns inlined e'
  Var i -> varChain h ns inlined i
  _ -> (reverse inlined, Terminal e)

-- TODO nothing for printing Names directly in Printers
-- TODO stop inlining when something in ns reached
-- TODO not the best case setup
printVar :: PrettyGuide -> [Name] -> StateET -> Id -> String
printVar pg ns s@(State{ expr_env = h }) i =
  let (chain, c_end) = varChain h ns [] i
      chain_strs = map (\i_ -> printHaskellPG pg s $ Var i_) chain
      end_str = case c_end of
        Symbolic -> "Symbolic"
        Cycle i' -> "Cycle " ++ printHaskellPG pg s (Var i')
        Terminal e -> printHaskellPG pg s e
        Unmapped -> ""
  in case c_end of
    Unmapped -> ""
    _ -> foldr (\s acc -> s ++ " -> " ++ acc) "" (chain_strs ++ [end_str])

printVars :: PrettyGuide -> [Name] -> StateET -> String
printVars pg ns s =
  let vars = varsInExpr ns $ exprExtract s
      var_strs = map (printVar pg ns s) vars
      non_empty_strs = filter (not . null) var_strs
  in foldr (\s acc -> acc ++ "\n" ++ s) "" $ non_empty_strs

-- TODO print the name differently?
summarizeInduction :: PrettyGuide -> [Name] -> IndMarker -> String
summarizeInduction pg ns im@(IndMarker {
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
  (printPG pg ns s1) ++ "\n" ++
  (printPG pg ns s2) ++ "\n" ++
  "Used Present: " ++
  (folder_name $ track q1) ++ "," ++
  (folder_name $ track q2) ++ "\n" ++
  (printPG pg ns q1) ++ "\n" ++
  (printPG pg ns q2) ++ "\n" ++
  "Past: " ++
  (folder_name $ track p1) ++ "," ++
  (folder_name $ track p2) ++ "\n" ++
  (printPG pg ns p1) ++ "\n" ++
  (printPG pg ns p2) ++ "\n" ++
  "Side: " ++ (sideName $ ind_side im) ++ "\n" ++
  "Result:\n" ++
  (printPG pg ns s1') ++ "\n" ++
  (printPG pg ns s2') ++ "\n" ++
  "Present Sub-Expressions Used for Induction:\n" ++
  (printHaskellPG pg q1 e1) ++ "\n" ++
  (printHaskellPG pg q2 e2) ++ "\n" ++
  "Past Sub-Expressions Used for Induction:\n" ++
  (printPG pg ns r1) ++ "\n" ++
  (printPG pg ns r2) ++ "\n" ++
  "New Variable Name: " ++ (show $ ind_fresh_name im)

summarizeCoinduction :: PrettyGuide -> [Name] -> CoMarker -> String
summarizeCoinduction pg ns (CoMarker {
                             co_real_present = (s1, s2)
                           , co_used_present = (q1, q2)
                           , co_past = (p1, p2)
                           }) =
  "Coinduction:\n" ++
  "Real Present: " ++
  (folder_name $ track s1) ++ "," ++
  (folder_name $ track s2) ++ "\n" ++
  (printPG pg ns s1) ++ "\n" ++
  (printPG pg ns s2) ++ "\n" ++
  "Used Present: " ++
  (folder_name $ track q1) ++ "," ++
  (folder_name $ track q2) ++ "\n" ++
  (printPG pg ns q1) ++ "\n" ++
  (printPG pg ns q2) ++ "\n" ++
  "Past: " ++
  (folder_name $ track p1) ++ "," ++
  (folder_name $ track p2) ++ "\n" ++
  (printPG pg ns p1) ++ "\n" ++
  (printPG pg ns p2)

-- TODO pretty guide type in Printers
-- variables:  find all names used in here
-- look them up, find a fixed point
-- print all relevant vars beside the expressions
-- maybe don't include definitions from the initial state
-- TODO fixed point of inlining; don't include things in ns
summarizeEquality :: PrettyGuide -> [Name] -> EqualMarker -> String
summarizeEquality pg ns (EqualMarker {
                          eq_real_present = (s1, s2)
                        , eq_used_present = (q1, q2)
                        }) =
  "Equivalent Expressions:\n" ++
  "Real Present: " ++
  (folder_name $ track s1) ++ ", " ++
  (folder_name $ track s2) ++ "\n" ++
  (printPG pg ns s1) ++ "\n" ++
  (printPG pg ns s2) ++ "\n" ++
  "Used States: " ++
  (folder_name $ track q1) ++ ", " ++
  (folder_name $ track q2) ++ "\n" ++
  (printPG pg ns q1) ++ "\n" ++
  (printPG pg ns q2)

summarizeNoObligations :: PrettyGuide -> [Name] -> (StateET, StateET) -> String
summarizeNoObligations pg ns (s1, s2) =
  "No Obligations Produced:\n" ++
  (folder_name $ track s1) ++ ", " ++
  (folder_name $ track s2) ++ "\n" ++
  (printPG pg ns s1) ++ "\n" ++
  (printPG pg ns s2)

summarizeNotEquivalent :: PrettyGuide -> [Name] -> (StateET, StateET) -> String
summarizeNotEquivalent pg ns (s1, s2) =
  "NOT EQUIVALENT:\n" ++
  (folder_name $ track s1) ++ ", " ++
  (folder_name $ track s2) ++ "\n" ++
  (printPG pg ns s1) ++ "\n" ++
  (printPG pg ns s2)

summarizeSolverFail :: PrettyGuide -> [Name] -> (StateET, StateET) -> String
summarizeSolverFail pg ns (s1, s2) =
  "SOLVER FAIL:\n" ++
  (folder_name $ track s1) ++ ", " ++
  (folder_name $ track s2) ++ "\n" ++
  (printPG pg ns s1) ++ "\n" ++
  (printPG pg ns s2)

summarizeAct :: PrettyGuide -> [Name] -> ActMarker -> String
summarizeAct pg ns m = case m of
  Induction im -> summarizeInduction pg ns im
  Coinduction cm -> summarizeCoinduction pg ns cm
  Equality em -> summarizeEquality pg ns em
  NoObligations s_pair -> summarizeNoObligations pg ns s_pair
  NotEquivalent s_pair -> summarizeNotEquivalent pg ns s_pair
  SolverFail s_pair -> summarizeSolverFail pg ns s_pair

tabsAfterNewLines :: String -> String
tabsAfterNewLines [] = []
tabsAfterNewLines ('\n':t) = '\n':'\t':(tabsAfterNewLines t)
tabsAfterNewLines (c:t) = c:(tabsAfterNewLines t)

-- generate the guide for the whole summary externally
summarize :: PrettyGuide -> [Name] -> Marker -> String
summarize pg ns (Marker (sh1, sh2) m) =
  "***\nLeft Path: " ++
  (foldr (\s acc -> acc ++ " -> " ++ s) "Start" $ map (folder_name . track) $ (latest sh1):history sh1) ++
  "\nRight Path: " ++
  (foldr (\s acc -> acc ++ " -> " ++ s) "Start" $ map (folder_name . track) $ (latest sh2):history sh2) ++ "\n" ++
  (tabsAfterNewLines $ summarizeAct pg ns m)
