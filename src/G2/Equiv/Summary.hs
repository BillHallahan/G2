{-# LANGUAGE OverloadedStrings #-}

module G2.Equiv.Summary
  ( SummaryMode (..)
  , summarize
  , summarizeAct
  , printPG
  , showCX
  , showCycle
  , stateMaxDepth
  , stateSumDepths
  , minMaxDepth
  , minSumDepth
  )
  where

import G2.Language

import qualified G2.Language.ExprEnv as E
import qualified G2.Language.Expr as X

import Data.List
import Data.Maybe
import Data.Tuple
import qualified Data.Text as DT

import qualified Data.HashSet as HS
import qualified Data.HashMap.Lazy as HM

import G2.Equiv.Config
import G2.Equiv.EquivADT
import G2.Equiv.G2Calls
import G2.Equiv.Tactics

import G2.Lib.Printers

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
      depth_str1 = "\nMax Depth:  " ++ (show $ maxArgDepth ns sym_ids s)
      depth_str2 = "\nSum Depth:  " ++ (show $ sumArgDepths ns sym_ids s)
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
      dc_print = "\nPath Length:  " ++ (show $ length $ dc_path $ track s)
  in label_str ++ "\n" ++ e_str ++ depth_str1 ++ depth_str2 ++
     sym_print ++ var_print ++ map_print ++ dc_print ++ "\n---"

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
              | Terminal Expr
              | Unmapped

-- don't include ns names in the result here
-- this does not remove duplicates
varsInExpr :: HS.HashSet Name -> Expr -> [Id]
varsInExpr ns e = filter (\i -> not ((idName i) `elem` ns)) $ X.vars e

-- new function for getting all of the variables right away
-- some of the computations here are redundant with what happens later
-- need to prune out repeats
-- should things count as repeats if they appear in the chain?
-- no need to remove duplicates if HashSet used internally
varsFull :: ExprEnv -> HS.HashSet Name -> Expr -> [Id]
varsFull h ns e =
  let v_ids = varsInExpr ns e
  in HS.toList $ varsFullRec ns h (HS.fromList v_ids) v_ids

varsFullList :: ExprEnv -> HS.HashSet Name -> [Id] -> [Id]
varsFullList h ns v_ids =
  HS.toList $ varsFullRec ns h (HS.fromList v_ids) v_ids

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

-- the terminal expression can have variables of its own
-- seemingly, they're not needed for anything
varChain :: ExprEnv -> HS.HashSet Name -> [Id] -> Id -> ([Id], ChainEnd)
varChain h ns inlined i =
  if i `elem` inlined then (reverse inlined, Cycle i)
  else if (idName i) `elem` ns then (reverse inlined, Terminal (Var i))
  else case E.lookupConcOrSym (idName i) h of
    Nothing -> ([], Unmapped)
    Just (E.Sym i') -> (reverse (i:inlined), Symbolic i')
    Just (E.Conc e) -> exprChain h ns (i:inlined) e

exprChain :: ExprEnv -> HS.HashSet Name -> [Id] -> Expr -> ([Id], ChainEnd)
exprChain h ns inlined e = case e of
  Tick _ (Prim Error _) -> (reverse inlined, Terminal e)
  Tick _ e' -> exprChain h ns inlined e'
  Var i -> varChain h ns inlined i
  _ -> (reverse inlined, Terminal e)

-- stop inlining when something in ns reached
printVar :: PrettyGuide -> HS.HashSet Name -> StateET -> Id -> String
printVar pg ns (State{ expr_env = h }) i =
  let (chain, c_end) = varChain h ns [] i
      chain_strs = map (\i_ -> printHaskellDirtyPG pg $ Var i_) chain
      end_str = case c_end of
        Symbolic (Id _ t) -> "Symbolic " ++ mkTypeHaskellPG pg t
        Cycle i' -> "Cycle " ++ printHaskellDirtyPG pg (Var i')
        Terminal e -> printHaskellDirtyPG pg e
        Unmapped -> ""
  in case c_end of
    Unmapped -> ""
    _ -> (foldr (\str acc -> str ++ " = " ++ acc) "" chain_strs) ++ end_str

printVars :: PrettyGuide -> HS.HashSet Name -> StateET -> [Id] -> String
printVars pg ns s v_ids =
  let var_strs = map (printVar pg ns s) v_ids
      non_empty_strs = filter (not . null) var_strs
  in intercalate "\n" non_empty_strs

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
                           ind_used_present = (q1, q2)
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
                             co_used_present = (q1, q2)
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
summarizeEquality pg ns sym_ids (EqualMarker { eq_used_present = (q1, q2) }) =
  "Equivalent Expressions:\n" ++
  --(summarizeStatePairTrack "Real Present" pg ns sym_ids s1 s2) ++ "\n" ++
  (summarizeStatePairTrack "Used States" pg ns sym_ids q1 q2)

summarizeCycleFound :: PrettyGuide ->
                       HS.HashSet Name ->
                       [Id] ->
                       CycleMarker ->
                       String
summarizeCycleFound pg ns sym_ids (CycleMarker (s1, s2) p _ sd) =
  "CYCLE FOUND:\n" ++
  (summarizeStatePairTrack "Real Present" pg ns sym_ids s1 s2) ++
  "\nPast State:\n" ++ (printPG pg ns sym_ids p) ++
  "\nSide: " ++ (sideName sd)

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
  CycleFound cm -> summarizeCycleFound pg ns sym_ids cm
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
summarize s_mode pg ns sym_ids (Marker (sh1, sh2) m) =
  let names1 = map trackName $ (latest sh1):history sh1
      names2 = map trackName $ (latest sh2):history sh2
  in
  "***\nLeft Path: " ++
  (intercalate " -> " $ (reverse names1)) ++
  "\nRight Path: " ++
  (intercalate " -> " $ (reverse names2)) ++ "\n" ++
  (if s_mode == WithHistory
      then "Left:\n\t" ++ tabsAfterNewLines (summarizeHistory pg ns sym_ids sh1)
            ++ "\nRight:\n\t" ++ tabsAfterNewLines (summarizeHistory pg ns sym_ids sh2) ++ "\n"
      else "")
  ++
  (tabsAfterNewLines $ summarizeAct pg ns sym_ids m)

printDC :: PrettyGuide -> [BlockInfo] -> String -> String
printDC _ [] str = str
printDC pg ((BlockDC d i n):ds) str =
  let d_str = printHaskellDirtyPG pg $ Data d
      str' = "(" ++ (printDC pg ds str) ++ ")"
      pre_blanks = replicate i "_"
      post_blanks = replicate (n - (i + 1)) "_"
  in intercalate " " $ d_str:(pre_blanks ++ (str':post_blanks))
printDC pg (_:ds) str = printDC pg ds str

-- instead of interleaving DCs and lambdas, we handle them separately
-- for lambdas, we wrap applications around the starting exprs
-- earlier list entries represent applications that are farther in
printLams :: PrettyGuide ->
             HS.HashSet Name ->
             ExprEnv ->
             [BlockInfo] ->
             String ->
             String
printLams _ _ _ [] str = str
printLams pg ns h ((BlockLam i):ds) str =
  let arg = inlineVars ns h $ Var i
      arg_str = printHaskellDirtyPG pg arg
      str' = "(" ++ str ++ ") " ++ arg_str
  in printLams pg ns h ds str'
printLams pg ns h (_:ds) str = printLams pg ns h ds str

-- for both cycles and regular counterexamples
printCX :: PrettyGuide ->
           HS.HashSet Name ->
           [Id] ->
           (StateH, StateH) ->
           (State t, State t) ->
           (StateET, StateET) ->
           String ->
           String ->
           String
printCX pg ns sym_ids (sh1, sh2) (s1, s2) (q1', q2') end1_str end2_str =
  let h = expr_env q2'
      names1 = map trackName $ (latest sh1):history sh1
      names2 = map trackName $ (latest sh2):history sh2
      e1 = inlineVars ns (expr_env q1') $ exprExtract s1
      e1_str = printHaskellPG pg q1' e1
      e1_str' = printLams pg ns (expr_env q1') (dc_path $ track q1') e1_str
      e2 = inlineVars ns h $ exprExtract s2
      e2_str = printHaskellPG pg q2' e2
      e2_str' = printLams pg ns (expr_env q2') (dc_path $ track q2') e2_str
      cx_str = e1_str' ++ " = " ++ end1_str ++ " but " ++
               e2_str' ++ " = " ++ end2_str
      func_ids = map snd $ HM.toList $ higher_order $ track q2'
      sym_vars = varsFullList h ns $ sym_ids ++ func_ids
      sym_str = printVars pg ns q2' sym_vars
      sym_print = case sym_str of
        "" -> ""
        _ -> "\nMain Symbolic Variables:\n" ++ sym_str
      other_vars = varsFull h ns (App (exprExtract q1') (exprExtract q2')) \\ sym_vars
      var_str = printVars pg ns q2' other_vars
      var_print = case var_str of
        "" -> ""
        _ -> "\nOther Variables:\n" ++ var_str
      map_str = printMappings pg q2'
      map_print = case map_str of
        "" -> ""
        _ -> "\nSymbolic Function Mappings:\n" ++ map_str
  in
  "Left Path: " ++
  (intercalate " -> " $ (reverse names1)) ++
  "\nRight Path: " ++
  (intercalate " -> " $ (reverse names2)) ++ "\n" ++
  intercalate "" [cx_str, sym_print, var_print, map_print]

-- counterexample printing
-- first state pair is initial states, second is from counterexample
showCX :: PrettyGuide ->
          HS.HashSet Name ->
          [Id] ->
          (StateH, StateH) ->
          (State t, State t) ->
          (StateET, StateET) ->
          String
showCX pg ns sym_ids sh_pair s_pair (q1, q2) =
  -- main part showing contradiction
  let (q1', q2') = syncEnvs q1 q2
      end1 = inlineVars ns (expr_env q1') $ exprExtract q1'
      end1_str = printDC pg (dc_path $ track q1') $ printHaskellPG pg q1' end1
      end2 = inlineVars ns (expr_env q2') $ exprExtract q2'
      end2_str = printDC pg (dc_path $ track q2') $ printHaskellPG pg q2' end2
  in printCX pg ns sym_ids sh_pair s_pair (q1', q2') end1_str end2_str

showCycle :: PrettyGuide ->
             HS.HashSet Name ->
             [Id] ->
             (StateH, StateH) ->
             (State t, State t) ->
             CycleMarker ->
             String
showCycle pg ns sym_ids sh_pair s_pair cm =
  let (q1, q2) = cycle_real_present cm
      (q1', q2') = syncEnvs q1 q2
      end1 = inlineVars ns (expr_env q1') $ exprExtract q1'
      end1_str = case cycle_side cm of
        ILeft -> "{HAS NON-TERMINATING PATH}"
        IRight -> printDC pg (dc_path $ track q1') $ printHaskellPG pg q1' end1
      end2 = inlineVars ns (expr_env q2') $ exprExtract q2'
      end2_str = case cycle_side cm of
        ILeft -> printDC pg (dc_path $ track q2') $ printHaskellPG pg q2' end2
        IRight -> "{HAS NON-TERMINATING PATH}"
      mappings = map swap $ HM.toList $ cycle_mapping cm
      mapping_str = intercalate "\n" $ map (printMapping pg) mappings
      mapping_print = "\nMapping for Cycle:\n" ++ mapping_str
  in
  (printCX pg ns sym_ids sh_pair s_pair (q1', q2') end1_str end2_str) ++ mapping_print

-- most Expr constructors will never appear in a concretization of an argument
-- TODO don't need to care about ns or cycles if only applied to initial args?
-- type arguments do not contribute to the depth of an expression
-- TODO this needs to take the opposite side into account
exprDepth :: ExprEnv -> ExprEnv -> HS.HashSet Name -> [Name] -> Expr -> Int
exprDepth h h' ns n e = case e of
  Tick _ e' -> exprDepth h h' ns n e'
  Var i | isSymbolicBoth (idName i) h h' -> 0
        | m <- idName i
        , not $ m `elem` ns
        , Just e' <- lookupBoth m h h' -> exprDepth h h' ns (m:n) e'
        | not $ (idName i) `elem` ns -> error "unmapped variable"
  _ | d@(Data (DataCon _ _)):l <- unAppNoTicks e
    , not $ null (anonArgumentTypes d) ->
      1 + (maximum $ 0:(map (exprDepth h h' ns n) l))
    | otherwise -> 0

getDepth :: StateET -> HS.HashSet Name -> Id -> Int
getDepth s ns i = exprDepth (expr_env s) (opp_env $ track s) ns [] (Var i)

maxArgDepth :: HS.HashSet Name -> [Id] -> StateET -> Int
maxArgDepth ns sym_ids s = case sym_ids of
  [] -> 0
  _ -> maximum $ map (getDepth s ns) sym_ids

sumArgDepths :: HS.HashSet Name -> [Id] -> StateET -> Int
sumArgDepths ns sym_ids s = foldr (+) 0 $ map (getDepth s ns) sym_ids

minDepthMetric :: (HS.HashSet Name -> [Id] -> StateET -> Int) ->
                  HS.HashSet Name ->
                  [Id] ->
                  [(StateH, StateH)] ->
                  Int
minDepthMetric m ns sym_ids states =
  let lefts = map (\(sh1, _) -> latest sh1) states
      rights = map (\(_, sh2) -> latest sh2) states
      (lefts', rights') = unzip $ map (uncurry syncSymbolic) (zip lefts rights)
      depths = map (m ns sym_ids) $ lefts' ++ rights'
  in case states of
    [] -> 0
    _ -> minimum depths

stateDepthMetric :: (HS.HashSet Name -> [Id] -> StateET -> Int) ->
                    HS.HashSet Name ->
                    [Id] ->
                    (StateH, StateH) ->
                    Int
stateDepthMetric m ns sym_ids (sh1, sh2) =
  let (s1, s2) = syncSymbolic (latest sh1) (latest sh2)
  in min (m ns sym_ids s1) (m ns sym_ids s2)

stateMaxDepth :: HS.HashSet Name -> [Id] -> (StateH, StateH) -> Int
stateMaxDepth = stateDepthMetric maxArgDepth

stateSumDepths :: HS.HashSet Name -> [Id] -> (StateH, StateH) -> Int
stateSumDepths = stateDepthMetric sumArgDepths

minMaxDepth :: HS.HashSet Name -> [Id] -> [(StateH, StateH)] -> Int
minMaxDepth = minDepthMetric maxArgDepth

-- correct to sync beforehand for all these
minSumDepth :: HS.HashSet Name -> [Id] -> [(StateH, StateH)] -> Int
minSumDepth = minDepthMetric sumArgDepths
