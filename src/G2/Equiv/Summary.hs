{-# LANGUAGE OverloadedStrings #-}

module G2.Equiv.Summary (SummaryMode (..), summarize, summarizeAct, printPG) where

-- TODO may not need all imports

import G2.Language

import G2.Config

import G2.Interface

import qualified G2.Language.ExprEnv as E
import qualified G2.Language.Typing as T
import qualified G2.Language.Expr as X

import Data.List
import Data.Maybe
import qualified Data.Text as DT

import qualified Data.HashSet as HS
import qualified Data.HashMap.Lazy as HM

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

data SummaryMode = NoHistory | WithHistory | NoSummary deriving Eq

sideName :: Side -> String
sideName ILeft = "Left"
sideName IRight = "Right"

trackName :: StateET -> String
trackName s =
  let str = folder_name $ track s
      substrs = DT.splitOn (DT.pack "/") $ DT.pack str
      final_sub = case reverse substrs of
        [] -> error "No Substring"
        fs:_ -> DT.unpack fs
  in case final_sub of
    "" -> "Start"
    _ -> final_sub

printPG :: PrettyGuide -> HS.HashSet Name -> [Id] -> StateET -> String
printPG pg ns sym_ids s =
  let label_str = trackName s
      h = expr_env s
      e = inlineVars ns h $ exprExtract s
      e_str = printHaskellDirtyPG pg e
      -- sym exec keeps higher_order in sync but not concretizations
      -- this means that the ids in func_ids are not always mapped
      -- if they are unmapped, they will not be printed for a state
      func_ids = map snd $ HM.toList $ higher_order $ track s
      sym_vars = varsFullList h ns $ sym_ids ++ func_ids
      sym_str = printVars pg ns s sym_vars
      sym_print = case sym_str of
        "" -> ""
        _ -> "\nMain Symbolic Variables:\n" ++ sym_str
      other_vars = varsFull h ns e \\ sym_vars
      var_str = printVars pg ns s other_vars
      var_print = case var_str of
        "" -> ""
        _ -> "\nOther Variables:\n" ++ var_str
      map_str = printMappings pg s
      map_print = case map_str of
        "" -> ""
        _ -> "\nSymbolic Function Mappings:\n" ++ map_str
  in label_str ++ "\n" ++ e_str ++ sym_print ++ var_print ++ map_print ++ "\n---"

inlineVars :: HS.HashSet Name -> ExprEnv -> Expr -> Expr
inlineVars ns eenv = inlineVars' HS.empty ns eenv

inlineVars' :: HS.HashSet Name -> HS.HashSet Name -> ExprEnv -> Expr -> Expr
inlineVars' seen ns eenv v@(Var (Id n _))
    | n `elem` ns = v
    | n `HS.member` seen = v
    | Just (E.Conc e) <- E.lookupConcOrSym n eenv = inlineVars' (HS.insert n seen) ns eenv e
inlineVars' seen ns eenv e = modifyChildren (inlineVars' seen ns eenv) e

data ChainEnd = Symbolic Id
              | Cycle Id
              | Terminal Expr [Id]
              | Unmapped

-- don't include ns names in the result here
-- this does not remove duplicates
varsInExpr :: HS.HashSet Name -> Expr -> [Id]
varsInExpr ns e = filter (\i -> not ((idName i) `elem` ns)) $ X.vars e

extraVars :: ChainEnd -> [Id]
extraVars (Terminal _ ids) = ids
extraVars _ = []

-- new function for getting all of the variables right away
-- some of the computations here are redundant with what happens later
-- need to prune out repeats
-- should things count as repeats if they appear in the chain?
-- no need to remove duplicates if HashSet used internally
varsFull :: ExprEnv -> HS.HashSet Name -> Expr -> [Id]
varsFull h ns e =
  let ids = varsInExpr ns e
  in HS.toList $ varsFullRec ns h (HS.fromList ids) ids

varsFullList :: ExprEnv -> HS.HashSet Name -> [Id] -> [Id]
varsFullList h ns ids = HS.toList $ varsFullRec ns h (HS.fromList ids) ids

varsFullRec :: HS.HashSet Name -> ExprEnv -> HS.HashSet Id -> [Id] -> HS.HashSet Id
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
varChain :: ExprEnv -> HS.HashSet Name -> [Id] -> Id -> ([Id], ChainEnd)
varChain h ns inlined i =
  if i `elem` inlined then (reverse inlined, Cycle i)
  else if (idName i) `elem` ns then (reverse inlined, Terminal (Var i) [])
  else case E.lookupConcOrSym (idName i) h of
    Nothing -> ([], Unmapped)
    Just (E.Sym i') -> (reverse (i:inlined), Symbolic i')
    Just (E.Conc e) -> exprChain h ns (i:inlined) e

exprChain :: ExprEnv -> HS.HashSet Name -> [Id] -> Expr -> ([Id], ChainEnd)
exprChain h ns inlined e = case e of
  Tick _ e' -> exprChain h ns inlined e'
  Var i -> varChain h ns inlined i
  _ -> (reverse inlined, Terminal e $ varsInExpr ns e)

-- stop inlining when something in ns reached
printVar :: PrettyGuide -> HS.HashSet Name -> StateET -> Id -> String
printVar pg ns s@(State{ expr_env = h }) i =
  let (chain, c_end) = varChain h ns [] i
      chain_strs = map (\i_ -> printHaskellDirtyPG pg $ Var i_) chain
      end_str = case c_end of
        Symbolic (Id _ t) -> "Symbolic " ++ mkTypeHaskellPG pg t
        Cycle i' -> "Cycle " ++ printHaskellDirtyPG pg (Var i')
        Terminal e _ -> printHaskellDirtyPG pg e
        Unmapped -> ""
  in case c_end of
    Unmapped -> ""
    _ -> (foldr (\str acc -> str ++ " = " ++ acc) "" chain_strs) ++ end_str

printVars :: PrettyGuide -> HS.HashSet Name -> StateET -> [Id] -> String
printVars pg ns s vars =
  let var_strs = map (printVar pg ns s) vars
      non_empty_strs = filter (not . null) var_strs
  in intercalate "\n" non_empty_strs

-- TODO print symbolic function mappings too
printMapping :: PrettyGuide -> (Expr, Id) -> String
printMapping pg (e, i) =
  let e_str = printHaskellDirtyPG pg e
      i_str = printHaskellDirtyPG pg (Var i)
  in e_str ++ " --> " ++ i_str

printMappings :: PrettyGuide -> StateET -> String
printMappings pg s =
  let mapping_list = HM.toList $ higher_order $ track s
  in intercalate "\n" $ map (printMapping pg) mapping_list

-- TODO may need some adjustment
-- TODO would be better to use trackName with all of these
printLemma :: PrettyGuide -> HS.HashSet Name -> [Id] -> Lemma -> String
printLemma pg ns sym_ids (Lemma{
                   lemma_name = n
                 , lemma_lhs = s1
                 , lemma_rhs = s2
                 , lemma_lhs_origin = n1
                 , lemma_rhs_origin = n2
                 }) =
  n ++ ": from " ++
  n1 ++ ", " ++ n2 ++ "\n" ++
  (summarizeStatePairTrack "States" pg ns sym_ids s1 s2)

-- no new line at end
summarizeStatePairTrack :: String ->
                           PrettyGuide ->
                           HS.HashSet Name ->
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

summarizeInduction :: PrettyGuide -> HS.HashSet Name -> [Id] -> IndMarker -> String
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
  (printHaskellDirtyPG pg e1) ++ "\n" ++
  (printHaskellDirtyPG pg e2) ++ "\n" ++
  "Past Sub-Expressions Used for Induction:\n" ++
  (printPG pg ns sym_ids r1) ++ "\n" ++
  (printPG pg ns sym_ids r2) ++ "\n" ++
  "New Variable Name: " ++
  (printHaskellDirtyPG pg $ Var $ Id (ind_fresh_name im) $ typeOf $ exprExtract s1')

summarizeCoinduction :: PrettyGuide -> HS.HashSet Name -> [Id] -> CoMarker -> String
summarizeCoinduction pg ns sym_ids (CoMarker {
                             co_real_present = (s1, s2)
                           , co_used_present = (q1, q2)
                           , co_past = (p1, p2)
                           , lemma_used_left = lemma_l
                           , lemma_used_right = lemma_r
                           }) =
  "Coinduction:\n" ++
  --(summarizeStatePairTrack "Real Present" pg ns sym_ids s1 s2) ++ "\n" ++
  (summarizeStatePairTrack "Used Present" pg ns sym_ids q1 q2) ++ "\n" ++
  (summarizeStatePairTrack "Past" pg ns sym_ids p1 p2) ++
  (case lemma_l of
    Nothing -> ""
    Just (s1', lem_l) ->
      "\nLeft Lemma:\n" ++ printLemma pg ns sym_ids lem_l ++
      "\nLeft Before Lemma Usage:\n" ++ printPG pg ns sym_ids s1') ++
  (case lemma_r of
    Nothing -> ""
    Just (s2', lem_r) ->
      "\nRight Lemma:\n" ++ printLemma pg ns sym_ids lem_r ++
      "\nRight Before Lemma Usage:\n" ++ printPG pg ns sym_ids s2')

-- variables:  find all names used in here
-- look them up, find a fixed point
-- print all relevant vars beside the expressions
-- don't include definitions from the initial state (i.e. things in ns)
summarizeEquality :: PrettyGuide -> HS.HashSet Name -> [Id] -> EqualMarker -> String
summarizeEquality pg ns sym_ids (EqualMarker {
                          eq_real_present = (s1, s2)
                        , eq_used_present = (q1, q2)
                        }) =
  "Equivalent Expressions:\n" ++
  --(summarizeStatePairTrack "Real Present" pg ns sym_ids s1 s2) ++ "\n" ++
  (summarizeStatePairTrack "Used States" pg ns sym_ids q1 q2)

summarizeNoObligations :: PrettyGuide ->
                          HS.HashSet Name ->
                          [Id] ->
                          (StateET, StateET) ->
                          String
summarizeNoObligations = summarizeStatePair "No Obligations Produced"

summarizeNotEquivalent :: PrettyGuide ->
                          HS.HashSet Name ->
                          [Id] ->
                          (StateET, StateET) ->
                          String
summarizeNotEquivalent = summarizeStatePair "NOT EQUIVALENT"

summarizeSolverFail :: PrettyGuide ->
                       HS.HashSet Name ->
                       [Id] ->
                       (StateET, StateET) ->
                       String
summarizeSolverFail = summarizeStatePair "SOLVER FAIL"

summarizeUnresolved :: PrettyGuide ->
                       HS.HashSet Name ->
                       [Id] ->
                       (StateET, StateET) ->
                       String
summarizeUnresolved = summarizeStatePair "Unresolved"

summarizeStatePair :: String ->
                      PrettyGuide ->
                      HS.HashSet Name ->
                      [Id] ->
                      (StateET, StateET) ->
                      String
summarizeStatePair str pg ns sym_ids (s1, s2) =
  str ++ ":\n" ++
  (trackName s1) ++ ", " ++
  (trackName s2) ++ "\n" ++
  (printPG pg ns sym_ids s1) ++ "\n" ++
  (printPG pg ns sym_ids s2)

summarizeAct :: PrettyGuide -> HS.HashSet Name -> [Id] -> ActMarker -> String
summarizeAct pg ns sym_ids m = case m of
  Induction im -> summarizeInduction pg ns sym_ids im
  Coinduction cm -> summarizeCoinduction pg ns sym_ids cm
  Equality em -> summarizeEquality pg ns sym_ids em
  NoObligations s_pair -> summarizeNoObligations pg ns sym_ids s_pair
  NotEquivalent s_pair -> summarizeNotEquivalent pg ns sym_ids s_pair
  SolverFail s_pair -> summarizeSolverFail pg ns sym_ids s_pair
  Unresolved s_pair -> summarizeUnresolved pg ns sym_ids s_pair

summarizeHistory :: PrettyGuide -> HS.HashSet Name -> [Id] -> StateH -> String
summarizeHistory pg ns sym_ids =
  intercalate "\n" . map (printPG pg ns sym_ids) . reverse . history

tabsAfterNewLines :: String -> String
tabsAfterNewLines [] = []
tabsAfterNewLines ('\n':t) = '\n':'\t':(tabsAfterNewLines t)
tabsAfterNewLines (c:t) = c:(tabsAfterNewLines t)

-- generate the guide for the whole summary externally
summarize :: SummaryMode -> PrettyGuide -> HS.HashSet Name -> [Id] -> Marker -> String
summarize mode pg ns sym_ids (Marker (sh1, sh2) m) =
  let names1 = map trackName $ (latest sh1):history sh1
      names2 = map trackName $ (latest sh2):history sh2
  in
  "***\nLeft Path: " ++
  (intercalate " -> " $ (reverse names1)) ++
  "\nRight Path: " ++
  (intercalate " -> " $ (reverse names2)) ++ "\n" ++
  (if mode == WithHistory
      then "Left:\n\t" ++ tabsAfterNewLines (summarizeHistory pg ns sym_ids sh1)
            ++ "\nRight:\n\t" ++ tabsAfterNewLines (summarizeHistory pg ns sym_ids sh2) ++ "\n"
      else "")
  ++
  (tabsAfterNewLines $ summarizeAct pg ns sym_ids m)

-- TODO different set of functions for CSV
csvHeader :: String
csvHeader = "Name,LHS,RHS,Total,Outcome,Time"

-- TODO does not remove duplicate total vars or ones that are irrelevant
-- TODO what if there are line breaks in an expression string?
csvRowStart :: [DT.Text] -> RewriteRule -> String
csvRowStart total r =
  let i = Id (ru_head r) TyUnknown
      v = Var i
      app = X.mkApp (v:ru_args r)
  in (DT.unpack $ ru_name r) ++ "," ++
  (printHaskellDirty app) ++ "," ++
  (printHaskellDirty $ ru_rhs r) ++ "," ++
  (intercalate " " $ map DT.unpack total) ++ ","

-- TODO how to get the time string?
-- the time isn't calculated within the Haskell program
-- I should do this inside the Python code instead
csvRowEnd :: String -> String -> String
csvRowEnd outcome time = outcome ++ "," ++ time
