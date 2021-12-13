{-# LANGUAGE OverloadedStrings #-}

module G2.Equiv.Summary (summarize, summarizeAct) where

-- TODO may not need all imports

import G2.Language

import G2.Config

import G2.Interface

import qualified G2.Language.ExprEnv as E
import qualified G2.Language.Expr as X

import Data.List
import Data.Maybe
import qualified Data.Text as DT

import qualified Data.HashSet as HS

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

trackName :: StateET -> String
trackName s =
  let str = folder_name $ track s
      substrs = DT.splitOn (DT.pack "/") $ DT.pack str
      --substrs = DS.strSplitAll "/" str
      final_sub = case reverse substrs of
        [] -> error "No Substring"
        fs:_ -> DT.unpack fs
  in case final_sub of
    "" -> "Start"
    _ -> final_sub

printPG :: PrettyGuide -> [Name] -> [Id] -> StateET -> String
printPG pg ns sym_ids s =
  let h = expr_env s
      e_str = printHaskellPG pg s $ exprExtract s
      sym_str = printVarsList pg ns sym_ids s
      -- TODO don't print the symbolic variables over again?
      var_str = printVars pg ns s
  in case var_str of
    "" -> e_str ++ "\nSymbolic Variables:\n" ++ sym_str ++ "\n---"
    _ -> e_str ++ "\nSymbolic Variables:\n" ++ sym_str ++
         "\nOther Variables:\n" ++ var_str ++ "\n---"

data ChainEnd = Symbolic Id
              | Cycle Id
              | Terminal Expr [Id]
              | Unmapped

-- don't include ns names in the result here
-- this does not remove duplicates
varsInExpr :: [Name] -> Expr -> [Id]
varsInExpr ns e = filter (\i -> not ((idName i) `elem` ns)) $ X.vars e

extraVars :: ChainEnd -> [Id]
extraVars (Terminal _ ids) = ids
extraVars _ = []

-- new function for getting all of the variables right away
-- some of the computations here are redundant with what happens later
-- need to prune out repeats
-- should things count as repeats if they appear in the chain?
-- no need to remove duplicates if HashSet used internally
varsFull :: ExprEnv -> [Name] -> Expr -> [Id]
varsFull h ns e =
  let ids = varsInExpr ns e
  in HS.toList $ varsFullRec ns h (HS.fromList ids) ids

varsFullList :: ExprEnv -> [Name] -> [Id] -> [Id]
varsFullList h ns ids = HS.toList $ varsFullRec ns h (HS.fromList ids) ids

varsFullRec :: [Name] -> ExprEnv -> HS.HashSet Id -> [Id] -> HS.HashSet Id
varsFullRec ns h seen search
  | null search = seen
  | otherwise =
    let all_exprs = mapMaybe (flip E.lookup h) $ map idName search
        all_vars = vars all_exprs
        all_new = filter
                  (\i -> not (((idName i) `elem` ns) || HS.member i seen))
                  all_vars
        new_seen = HS.union (HS.fromList all_new) seen
    in varsFullRec ns h new_seen all_new

-- the terminal expression can have variables of its own that we should cover
varChain :: ExprEnv -> [Name] -> [Id] -> Id -> ([Id], ChainEnd)
varChain h ns inlined i =
  if i `elem` inlined then (reverse inlined, Cycle i)
  else if (idName i) `elem` ns then (reverse inlined, Terminal (Var i) [])
  else case E.lookupConcOrSym (idName i) h of
    Nothing -> ([], Unmapped)
    Just (E.Sym i') -> (reverse (i:inlined), Symbolic i')
    Just (E.Conc e) -> exprChain h ns (i:inlined) e

exprChain :: ExprEnv -> [Name] -> [Id] -> Expr -> ([Id], ChainEnd)
exprChain h ns inlined e = case e of
  Tick _ e' -> exprChain h ns inlined e'
  Var i -> varChain h ns inlined i
  _ -> (reverse inlined, Terminal e $ varsInExpr ns e)

-- stop inlining when something in ns reached
printVar :: PrettyGuide -> [Name] -> StateET -> Id -> String
printVar pg ns s@(State{ expr_env = h }) i =
  let (chain, c_end) = varChain h ns [] i
      chain_strs = map (\i_ -> printHaskellPG pg s $ Var i_) chain
      end_str = case c_end of
        Symbolic (Id _ t) -> "Symbolic " ++ mkTypeHaskellPG pg t
        Cycle i' -> "Cycle " ++ printHaskellPG pg s (Var i')
        Terminal e _ -> printHaskellPG pg s e
        Unmapped -> ""
  in case c_end of
    Unmapped -> ""
    _ -> (foldr (\str acc -> str ++ " -> " ++ acc) "" chain_strs) ++ end_str

-- TODO use markAndSweepPreserving plus an extra filter
printVars :: PrettyGuide -> [Name] -> StateET -> String
printVars pg ns s =
  let vars = varsFull (expr_env s) ns (exprExtract s)
      var_strs = map (printVar pg ns s) vars
      non_empty_strs = filter (not . null) var_strs
  in intercalate "\n" non_empty_strs

-- TODO only need the expression environment from the state
-- TODO redundant code
printVarsList :: PrettyGuide -> [Name] -> [Id] -> StateET -> String
printVarsList pg ns ids s =
  let vars = varsFullList (expr_env s) ns ids
      var_strs = map (printVar pg ns s) vars
      non_empty_strs = filter (not . null) var_strs
  in intercalate "\n" non_empty_strs

-- no new line at end
summarizeStatePairTrack :: String ->
                           PrettyGuide ->
                           [Name] ->
                           [Id] ->
                           StateET ->
                           StateET ->
                           String
summarizeStatePairTrack str pg ns sym_ids s1 s2 =
  str ++ ": " ++
  (trackName s1) ++ ", " ++
  (trackName s2) ++ "\n" ++
  (printPG pg ns sym_ids s1) ++ "\n" ++
  (printPG pg ns sym_ids s2)

summarizeInduction :: PrettyGuide -> [Name] -> [Id] -> IndMarker -> String
summarizeInduction pg ns sym_ids im@(IndMarker {
                           ind_real_present = (s1, s2)
                         , ind_used_present = (q1, q2)
                         , ind_past = (p1, p2)
                         , ind_result = (s1', s2')
                         , ind_present_scrutinees = (e1, e2)
                         , ind_past_scrutinees = (r1, r2)
                         }) =
  "Induction:\n" ++
  --(summarizeStatePairTrack "Real Present" pg ns sym_ids s1 s2) ++ "\n" ++
  (summarizeStatePairTrack "Used Present" pg ns sym_ids q1 q2) ++ "\n" ++
  (summarizeStatePairTrack "Past" pg ns sym_ids p1 p2) ++ "\n" ++
  "Side: " ++ (sideName $ ind_side im) ++ "\n" ++
  "Result:\n" ++
  (printPG pg ns sym_ids s1') ++ "\n" ++
  (printPG pg ns sym_ids s2') ++ "\n" ++
  "Present Sub-Expressions Used for Induction:\n" ++
  (printHaskellPG pg q1 e1) ++ "\n" ++
  (printHaskellPG pg q2 e2) ++ "\n" ++
  "Past Sub-Expressions Used for Induction:\n" ++
  (printPG pg ns sym_ids r1) ++ "\n" ++
  (printPG pg ns sym_ids r2) ++ "\n" ++
  "New Variable Name: " ++
  (printHaskellPG pg s1' $ Var $ Id (ind_fresh_name im) $ typeOf $ exprExtract s1')

summarizeCoinduction :: PrettyGuide -> [Name] -> [Id] -> CoMarker -> String
summarizeCoinduction pg ns sym_ids (CoMarker {
                             co_real_present = (s1, s2)
                           , co_used_present = (q1, q2)
                           , co_past = (p1, p2)
                           }) =
  "Coinduction:\n" ++
  --(summarizeStatePairTrack "Real Present" pg ns sym_ids s1 s2) ++ "\n" ++
  (summarizeStatePairTrack "Used Present" pg ns sym_ids q1 q2) ++ "\n" ++
  (summarizeStatePairTrack "Past" pg ns sym_ids p1 p2)

-- variables:  find all names used in here
-- look them up, find a fixed point
-- print all relevant vars beside the expressions
-- don't include definitions from the initial state (i.e. things in ns)
summarizeEquality :: PrettyGuide -> [Name] -> [Id] -> EqualMarker -> String
summarizeEquality pg ns sym_ids (EqualMarker {
                          eq_real_present = (s1, s2)
                        , eq_used_present = (q1, q2)
                        }) =
  "Equivalent Expressions:\n" ++
  --(summarizeStatePairTrack "Real Present" pg ns sym_ids s1 s2) ++ "\n" ++
  (summarizeStatePairTrack "Used States" pg ns sym_ids q1 q2)

summarizeNoObligations :: PrettyGuide ->
                          [Name] ->
                          [Id] ->
                          (StateET, StateET) ->
                          String
summarizeNoObligations = summarizeStatePair "No Obligations Produced"

summarizeNotEquivalent :: PrettyGuide ->
                          [Name] ->
                          [Id] ->
                          (StateET, StateET) ->
                          String
summarizeNotEquivalent = summarizeStatePair "NOT EQUIVALENT"

summarizeSolverFail :: PrettyGuide ->
                       [Name] ->
                       [Id] ->
                       (StateET, StateET) ->
                       String
summarizeSolverFail = summarizeStatePair "SOLVER FAIL"

summarizeUnresolved :: PrettyGuide ->
                       [Name] ->
                       [Id] ->
                       (StateET, StateET) ->
                       String
summarizeUnresolved = summarizeStatePair "Unresolved"

summarizeStatePair :: String ->
                      PrettyGuide ->
                      [Name] ->
                      [Id] ->
                      (StateET, StateET) ->
                      String
summarizeStatePair str pg ns sym_ids (s1, s2) =
  str ++ ":\n" ++
  (trackName s1) ++ ", " ++
  (trackName s2) ++ "\n" ++
  (printPG pg ns sym_ids s1) ++ "\n" ++
  (printPG pg ns sym_ids s2)

summarizeAct :: PrettyGuide -> [Name] -> [Id] -> ActMarker -> String
summarizeAct pg ns sym_ids m = case m of
  Induction im -> summarizeInduction pg ns sym_ids im
  Coinduction cm -> summarizeCoinduction pg ns sym_ids cm
  Equality em -> summarizeEquality pg ns sym_ids em
  NoObligations s_pair -> summarizeNoObligations pg ns sym_ids s_pair
  NotEquivalent s_pair -> summarizeNotEquivalent pg ns sym_ids s_pair
  SolverFail s_pair -> summarizeSolverFail pg ns sym_ids s_pair
  Unresolved s_pair -> summarizeUnresolved pg ns sym_ids s_pair

tabsAfterNewLines :: String -> String
tabsAfterNewLines [] = []
tabsAfterNewLines ('\n':t) = '\n':'\t':(tabsAfterNewLines t)
tabsAfterNewLines (c:t) = c:(tabsAfterNewLines t)

-- generate the guide for the whole summary externally
summarize :: PrettyGuide -> [Name] -> [Id] -> Marker -> String
summarize pg ns sym_ids (Marker (sh1, sh2) m) =
  let names1 = map trackName $ (latest sh1):history sh1
      names2 = map trackName $ (latest sh2):history sh2
  in
  "***\nLeft Path: " ++
  (intercalate " -> " $ (reverse names1)) ++
  "\nRight Path: " ++
  (intercalate " -> " $ (reverse names2)) ++ "\n" ++
  (tabsAfterNewLines $ summarizeAct pg ns sym_ids m)
