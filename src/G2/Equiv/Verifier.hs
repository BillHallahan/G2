{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Equiv.Verifier
    ( verifyLoop
    , checkRule
    ) where

import G2.Language

import G2.Config

import G2.Interface

import qualified Control.Monad.State.Lazy as CM

import qualified G2.Language.ExprEnv as E
import qualified G2.Language.CallGraph as G

import Data.Maybe
import Data.List
import qualified Data.Text as DT

import qualified Data.HashSet as HS
import qualified G2.Solver as S

import qualified G2.Language.PathConds as P

import G2.Equiv.InitRewrite
import G2.Equiv.EquivADT
import G2.Equiv.G2Calls
import G2.Equiv.Tactics
import G2.Equiv.Generalize
import G2.Equiv.Summary

import qualified Data.Map as M
import G2.Execution.Memory
import Data.Monoid (Any (..))

import qualified G2.Language.Stack as Stck
import Control.Monad

import G2.Lib.Printers

-- reader / writer monad source consulted
-- https://mmhaskell.com/monads/reader-writer

import qualified Control.Monad.Writer.Lazy as W

import System.IO

statePairReadyForSolver :: (State t, State t) -> Bool
statePairReadyForSolver (s1, s2) =
  let h1 = expr_env s1
      h2 = expr_env s2
      CurrExpr _ e1 = curr_expr s1
      CurrExpr _ e2 = curr_expr s2
  in
  exprReadyForSolver h1 e1 && exprReadyForSolver h2 e2

-- don't log when the base folder name is empty
logStatesFolder :: String -> LogMode -> LogMode
logStatesFolder pre (Log method n) = Log method $ n ++ "/" ++ pre
logStatesFolder _ NoLog = NoLog

logStatesET :: String -> LogMode -> String
logStatesET pre (Log _ n) = n ++ "/" ++ pre
logStatesET pre NoLog = "/" ++ pre

runSymExec :: S.Solver solver =>
              solver ->
              Config ->
              NebulaConfig ->
              HS.HashSet Name ->
              StateET ->
              StateET ->
              CM.StateT (Bindings, Int) IO [(StateET, StateET)]
runSymExec solver config nc@(NC { sync = sy }) ns s1 s2 = do
  (bindings, k) <- CM.get
  let nc' = nc { log_states = logStatesFolder ("a" ++ show k) (log_states nc) }
      t1 = (track s1) { folder_name = logStatesET ("a" ++ show k) (log_states nc) }
      CurrExpr r1 e1 = curr_expr s1
      e1' = addStackTickIfNeeded ns (expr_env s1) e1
      s1' = s1 { track = t1, curr_expr = CurrExpr r1 e1' }
  --CM.liftIO $ putStrLn $ (folder_name $ track s1) ++ " becomes " ++ (folder_name t1)
  (er1, bindings') <- CM.lift $ runG2ForNebula solver s1' (expr_env s2) (track s2) config nc' bindings
  CM.put (bindings', k + 1)
  let final_s1 = map final_state er1
  pairs <- mapM (\s1_ -> do
                    (b_, k_) <- CM.get
                    let s2_ = transferInfo sy s1_ (snd $ syncSymbolic s1_ s2)
                    let nc'' = nc { log_states = logStatesFolder ("b" ++ show k_) (log_states nc) }
                        t2 = (track s2_) { folder_name = logStatesET ("b" ++ show k_) (log_states nc) }
                        CurrExpr r2 e2 = curr_expr s2_
                        e2' = addStackTickIfNeeded ns (expr_env s2) e2
                        s2' = s2_ { track = t2, curr_expr = CurrExpr r2 e2' }
                    --CM.liftIO $ putStrLn $ (folder_name $ track s2_) ++ " becomes " ++ (folder_name t2)
                    (er2, b_') <- CM.lift $ runG2ForNebula solver s2' (expr_env s1_) (track s1_) config nc'' b_
                    CM.put (b_', k_ + 1)
                    return $ map (\er2_ -> 
                                    let
                                        s2_' = final_state er2_
                                        s1_' = transferInfo sy s2_' (snd $ syncSymbolic s2_' s1_)
                                    in
                                    (addStamps k $ prepareState s1_', addStamps k_ $ prepareState s2_')
                                 ) er2) final_s1
  CM.liftIO $ filterM (pathCondsConsistent solver) (concat pairs)

pathCondsConsistent :: S.Solver solver =>
                       solver ->
                       (StateET, StateET) ->
                       IO Bool
pathCondsConsistent solver (s1, s2) = do
  res <- applySolver solver P.empty s1 s2
  case res of
    S.UNSAT () -> return False
    _ -> return True

-- info goes from left to right for expression environment too
transferInfo :: Bool -> StateET -> StateET -> StateET
transferInfo True s1 s2 =
  transferTrackerInfo s1 (s2 { expr_env = expr_env s1 })
transferInfo False s1 s2 = transferTrackerInfo s1 s2

-- Don't share expr env and path constraints between sides
-- info goes from left to right
transferTrackerInfo :: StateET -> StateET -> StateET
transferTrackerInfo s1 s2 =
  let t1 = track s1
      t2 = track s2
      t2' = t2 {
        higher_order = higher_order t1
      , total_vars = total_vars t1
      --, opp_env = expr_env s1
      }
  in s2 { track = t2' }

frameWrap :: Frame -> Expr -> Expr
frameWrap (CaseFrame i t alts) e = Case e i t alts
frameWrap (ApplyFrame e') e = App e e'
frameWrap (UpdateFrame _) e = e
frameWrap (CastFrame co) e = Cast e co
frameWrap _ _ = error "unsupported frame"

stackWrap :: Stck.Stack Frame -> Expr -> Expr
stackWrap sk e =
  case Stck.pop sk of
    Nothing -> e
    Just (fr, sk') -> stackWrap sk' $ frameWrap fr e

loc_name :: Name
loc_name = Name (DT.pack "STACK") Nothing 0 Nothing

rec_name :: Name
rec_name = Name (DT.pack "REC") Nothing 0 Nothing

wrapRecursiveCall :: Name -> Expr -> Expr
-- This first case prevents recursive calls from being wrapped twice
wrapRecursiveCall n e@(Tick (NamedLoc n'@(Name t _ _ _)) e') =
  if t == DT.pack "REC"
  then e
  else Tick (NamedLoc n') $ wrapRecursiveCall n e'
wrapRecursiveCall n e@(Var (Id n' _)) =
  if n == n'
  then Tick (NamedLoc rec_name) e
  else wrcHelper n e
wrapRecursiveCall n e = wrcHelper n e

wrcHelper :: Name -> Expr -> Expr
wrcHelper n e = case e of
  Tick (NamedLoc (Name t _ _ _)) _ | t == DT.pack "REC" -> e
  _ -> modifyChildren (wrapRecursiveCall n) e

-- Creating a new expression environment lets us use the existing reachability
-- functions.
-- look inside the bindings and inside the body for recursion
wrapLetRec :: ExprEnv -> Expr -> Expr
wrapLetRec h (Let binds e) =
  let binds1 = map (\(i, e_) -> (idName i, e_)) binds
      fresh_name = Name (DT.pack "FRESH") Nothing 0 Nothing
      h' = foldr (\(n_, e_) h_ -> E.insert n_ e_ h_) h ((fresh_name, e):binds1)
      wrap_cg = wrapAllRecursion (G.getCallGraph h') h'
      binds2 = map (\(n_, e_) -> (n_, wrap_cg n_ e_)) binds1
      e' = foldr (wrapIfCorecursive (G.getCallGraph h') h' fresh_name) e (map fst binds1)
      e'' = wrapLetRec h' $ modifyChildren (wrapLetRec h') e'
      binds3 = map ((wrapLetRec h') . modifyChildren (wrapLetRec h')) (map snd binds2)
      binds4 = zip (map fst binds) binds3
  in
  -- REC tick getting inserted in binds but not in body
  -- it's only needed where the recursion actually happens
  -- need to apply wrap_cg over it with the new names?
  -- wrap_cg with fresh_name won't help because nothing can reach fresh_name
  Let binds4 e''
wrapLetRec h e = modifyChildren (wrapLetRec h) e

-- first Name is the one that maps to the Expr in the environment
-- second Name is the one that might be wrapped
-- do not allow wrapping for symbolic variables
-- modifyChildren can't see a REC tick that was just inserted above it
wrapIfCorecursive :: G.CallGraph -> ExprEnv -> Name -> Name -> Expr -> Expr
wrapIfCorecursive cg h n m e =
  let n_list = G.reachable n cg
      m_list = G.reachable m cg
  in
  if (n `elem` m_list) && (m `elem` n_list)
  then
    if E.isSymbolic m h
    then e
    else wrcHelper m (wrapRecursiveCall m e)
  else e

-- the call graph must be based on the given environment
-- the Name must map to the Expr in the environment
wrapAllRecursion :: G.CallGraph -> ExprEnv -> Name -> Expr -> Expr
wrapAllRecursion cg h n e =
  let n_list = G.reachable n cg
  in
  if (not $ E.isSymbolic n h) && (n `elem` n_list)
  then foldr (wrapIfCorecursive cg h n) e n_list
  else e

-- stack tick not added here anymore
prepareState :: StateET -> StateET
prepareState s =
  let e = exprExtract s
  in s {
    curr_expr = CurrExpr Evaluate $ stackWrap (exec_stack s) $ e
  , num_steps = 0
  , rules = []
  , exec_stack = Stck.empty
  }

-- "stamps" for Case statements enforce induction validity
stampName :: Int -> Int -> Name
stampName x k =
  Name (DT.pack $ (show x) ++ "STAMP:" ++ (show k)) Nothing 0 Nothing

-- leave existing stamp ticks unaffected; don't cover them with more layers
-- only stamp strings should contain a colon
insertStamps :: Int -> Int -> Expr -> Expr
insertStamps x k (Tick nl e) = Tick nl (insertStamps x k e)
insertStamps x k (Case e i t a) =
  case a of
    (Alt am1 a1):as -> case a1 of
        Tick (NamedLoc (Name n _ _ _)) _ | str <- DT.unpack n
                                         , ':' `elem` str ->
          Case (insertStamps (x + 1) k e) i t a
        _ -> let sn = stampName x k
                 a1' = Alt am1 (Tick (NamedLoc sn) a1)
             in Case (insertStamps (x + 1) k e) i t (a1':as)
    _ -> error "Empty Alt List"
insertStamps _ _ e = e

addStamps :: Int -> StateET -> StateET
addStamps k s =
  let CurrExpr c e = curr_expr s
      e' = insertStamps 0 k e
  in s { curr_expr = CurrExpr c e' }

getLatest :: (StateH, StateH) -> (StateET, StateET)
getLatest (StateH { latest = s1 }, StateH { latest = s2 }) = (s1, s2)

type NewLemmaTactic solver = String -> String -> Tactic solver

-- discharge only has a meaningful value when execution is done for a branch
appendH :: StateH -> StateET -> StateH
appendH sh s =
  StateH {
    latest = s
  , history = (latest sh):(history sh)
  , discharge = discharge sh
  }

replaceH :: StateH -> StateET -> StateH
replaceH sh s = sh { latest = s }

allTactics :: S.Solver s => [Tactic s]
allTactics = [
    tryEquality
  , tryCoinduction
  , generalizeFull
  , trySolver
  , checkCycle
  ]

allNewLemmaTactics :: S.Solver s => [NewLemmaTactic s]
allNewLemmaTactics = map applyTacticToLabeledStates [tryEquality, tryCoinduction]

-- negative loop iteration count means there's no limit
-- The (null states) check ensures that we return UNSAT rather than
-- Unknown when states is empty and n = 0.
verifyLoop :: S.Solver solver =>
              solver ->
              Int ->
              HS.HashSet Name ->
              Lemmas ->
              [(StateH, StateH)] ->
              Bindings ->
              Config ->
              NebulaConfig ->
              [Id] ->
              Int ->
              Int ->
              W.WriterT [Marker] IO (S.Result () () ())
verifyLoop solver num_lems ns lemmas states b config nc sym_ids k n | (n /= 0) || (null states) = do
  W.liftIO $ putStrLn "<Loop Iteration>"
  W.liftIO $ putStrLn $ show n
  -- this printing allows our Python script to report depth stats
  let min_max_depth = minMaxDepth ns sym_ids states
      min_sum_depth = minSumDepth ns sym_ids states
  case states of
    [] -> return ()
    _ -> do
      W.liftIO $ putStrLn $ "<<Min Max Depth>> " ++ show min_max_depth
      W.liftIO $ putStrLn $ "<<Min Sum Depth>> " ++ show min_sum_depth
  W.liftIO $ hFlush stdout
  (b', k', proven, lemmas') <- verifyLoopPropLemmas solver allTactics num_lems ns lemmas b config nc k

  -- W.liftIO $ putStrLn $ "proposed_lemmas: " ++ show (length $ proposed_lemmas lemmas')
  -- W.liftIO $ putStrLn $ "proven_lemmas: " ++ show (length $ proven_lemmas lemmas')
  -- W.liftIO $ putStrLn $ "continued_lemmas: " ++ show (length continued_lemmas)
  -- W.liftIO $ putStrLn $ "disproven_lemmas: " ++ show (length $ disproven_lemmas lemmas')

  (b'', k'', proven', lemmas'') <- verifyLemmasWithNewProvenLemmas solver allNewLemmaTactics num_lems ns proven lemmas' b' config nc k'
  (pl_sr, b''') <- verifyWithNewProvenLemmas solver allNewLemmaTactics num_lems ns proven' lemmas'' b'' states

  case pl_sr of
      CounterexampleFound -> return $ S.SAT ()
      Proven -> return $ S.UNSAT ()
      ContinueWith _ pl_lemmas -> do
          (sr, b'''', k''') <- verifyLoopWithSymEx solver allTactics num_lems ns lemmas'' b''' config nc k'' states
          case sr of
              ContinueWith new_obligations new_lemmas -> do
                  let n' = if n > 0 then n - 1 else n
                  --W.liftIO $ putStrLn $ show $ length new_obligations
                  --W.liftIO $ putStrLn $ "length new_lemmas = " ++ show (length $ pl_lemmas ++ new_lemmas)

                  final_lemmas <- foldM (flip (insertProposedLemma solver ns))
                                        lemmas''
                                        (pl_lemmas ++ new_lemmas)

                  -- mapM (\l@(le1, le2) -> do
                  --               let pg = mkPrettyGuide l
                  --               W.liftIO $ putStrLn "----"
                  --               W.liftIO $ putStrLn $ printPG pg ns (E.symbolicIds $ expr_env le1) le1
                  --               W.liftIO $ putStrLn $ printPG pg ns (E.symbolicIds $ expr_env le2) le2) $ HS.toList new_lemmas
                  verifyLoop solver num_lems ns final_lemmas new_obligations b'''' config nc sym_ids k''' n'
              CounterexampleFound -> return $ S.SAT ()
              Proven -> do
                  W.liftIO $ putStrLn $ "proposed = " ++ show (length $ proposedLemmas lemmas)
                  -- mapM (\l@(Lemma le1 le2 _) -> do
                  --               let pg = mkPrettyGuide l
                  --               W.liftIO $ putStrLn "----"
                  --               W.liftIO $ putStrLn $ printPG pg ns (E.symbolicIds $ expr_env le1) le1
                  --               W.liftIO $ putStrLn $ printPG pg ns (E.symbolicIds $ expr_env le2) le2) $ proposedLemmas lemmas
                  W.liftIO $ putStrLn $ "proven = " ++ show (length $ provenLemmas lemmas) 
                  W.liftIO $ putStrLn $ "disproven = " ++ show (length $ disprovenLemmas lemmas) 
                  return $ S.UNSAT ()
  | otherwise = do
    W.liftIO $ putStrLn $ "proposed = " ++ show (length $ proposedLemmas lemmas)
    W.liftIO $ putStrLn $ "proven = " ++ show (length $ provenLemmas lemmas) 
    W.liftIO $ putStrLn $ "disproven = " ++ show (length $ disprovenLemmas lemmas)
    {-
    mapM (\l@(Lemma { lemma_lhs = le1, lemma_rhs = le2}) -> do
                  let pg = mkPrettyGuide l
                  W.liftIO $ putStrLn "---- Proven ----"
                  W.liftIO $ putStrLn $ lemma_name l
                  W.liftIO $ putStrLn $ printPG pg ns (E.symbolicIds $ expr_env le1) le1
                  W.liftIO $ putStrLn $ printPG pg ns (E.symbolicIds $ expr_env le2) le2) (provenLemmas lemmas)
    mapM (\l@(Lemma { lemma_lhs = le1, lemma_rhs = le2}) -> do
                  let pg = mkPrettyGuide l
                  W.liftIO $ putStrLn "---- Disproven ----"
                  W.liftIO $ putStrLn $ lemma_name l
                  W.liftIO $ putStrLn $ printPG pg ns (E.symbolicIds $ expr_env le1) le1
                  W.liftIO $ putStrLn $ printPG pg ns (E.symbolicIds $ expr_env le2) le2) (disprovenLemmas lemmas)
    mapM (\l@(Lemma { lemma_lhs = le1, lemma_rhs = le2}) -> do
                  let pg = mkPrettyGuide l
                  W.liftIO $ putStrLn "---- Proposed ----"
                  W.liftIO $ putStrLn $ lemma_name l
                  W.liftIO $ putStrLn $ printPG pg ns (E.symbolicIds $ expr_env le1) le1
                  W.liftIO $ putStrLn $ printPG pg ns (E.symbolicIds $ expr_env le2) le2) (proposedLemmas lemmas)
    -}
    -- TODO one option is to insert every lemma marker at the end
    -- not sure if it would be better to mix them with everything else
    -- TODO need a StateH for every lemma?
    W.liftIO $ putStrLn $ "Unresolved Obligations: " ++ show (length states)
    let ob (sh1, sh2) = Marker (sh1, sh2) $ Unresolved (latest sh1, latest sh2)
        pr l = LMarker $ LemmaProposed l
        pv l = LMarker $ LemmaProven l
        rj l = LMarker $ LemmaRejected l
        un l = LMarker $ LemmaUnresolved l
        un_lemmas = (proposedLemmas lemmas \\ provenLemmas lemmas) \\ disprovenLemmas lemmas
    W.tell $ map ob states
    W.tell $ map pr $ proposedLemmas lemmas
    W.tell $ map pv $ provenLemmas lemmas
    W.tell $ map rj $ disprovenLemmas lemmas
    W.tell $ map un un_lemmas
    return $ S.Unknown "Loop Iterations Exhausted" ()

data StepRes = CounterexampleFound
             | ContinueWith [(StateH, StateH)] [Lemma]
             | Proven

verifyLoopPropLemmas :: S.Solver solver =>
                        solver
                     -> [Tactic solver]
                     -> Int
                     -> HS.HashSet Name
                     -> Lemmas
                     -> Bindings
                     -> Config
                     -> NebulaConfig
                     -> Int
                     -> (W.WriterT [Marker] IO) (Bindings, Int, [ProvenLemma], Lemmas)
verifyLoopPropLemmas solver tactics num_lems ns lemmas b config nc k = do
    let prop_lemmas = proposedLemmas lemmas
        verify_lemma = verifyLoopPropLemmas' solver tactics num_lems ns lemmas config nc
    (prop_lemmas', (b', k')) <- CM.runStateT (mapM verify_lemma prop_lemmas) (b, k)

    let (proven, continued_lemmas, disproven, new_lemmas) = partitionLemmas ([], [], [], []) prop_lemmas'
        lemmas' = replaceProposedLemmas continued_lemmas lemmas
    lemmas'' <- foldM (insertProvenLemma solver ns) lemmas' proven
    lemmas''' <- foldM (insertDisprovenLemma solver ns) lemmas'' disproven

    lemmas'''' <- foldM (flip (insertProposedLemma solver ns))
                          lemmas'''
                          new_lemmas

    return (b', k', proven, lemmas'''')
    where
      partitionLemmas (p, c, d, n) ((CounterexampleFound, lem):xs) = partitionLemmas (p, c, lem:d, n) xs
      partitionLemmas (p, c, d, n) ((ContinueWith _ new_lem, lem):xs) = partitionLemmas (p, lem:c, d, new_lem ++ n) xs
      partitionLemmas (p, c, d, n) ((Proven, lem):xs) = partitionLemmas (lem:p, c, d, n) xs
      partitionLemmas r [] = r

verifyLoopPropLemmas' :: S.Solver solver =>
                         solver
                      -> [Tactic solver]
                      -> Int
                      -> HS.HashSet Name
                      -> Lemmas
                      -> Config
                      -> NebulaConfig
                      -> ProposedLemma
                      -> CM.StateT (Bindings, Int)  (W.WriterT [Marker] IO) (StepRes, Lemma)
verifyLoopPropLemmas' solver tactics num_lems ns lemmas config nc
                     l@(Lemma { lemma_to_be_proven = states }) = do
    (b, k) <- CM.get
    --W.liftIO $ putStrLn $ "k = " ++ show k
    --W.liftIO $ putStrLn $ lemma_name l
    (sr, b', k') <- W.lift (verifyLoopWithSymEx solver tactics num_lems ns lemmas b config nc k states)
    CM.put (b', k')
    lem <- case sr of
                  CounterexampleFound -> {-trace "COUNTEREXAMPLE verifyLemma"-} return $ l { lemma_to_be_proven = [] }
                  ContinueWith states' _ -> return $ l { lemma_to_be_proven = states' }
                  Proven -> return $ l { lemma_to_be_proven = [] }
    return (sr, lem)

verifyLoopWithSymEx :: S.Solver solver =>
                       solver
                    -> [Tactic solver]
                    -> Int
                    -> HS.HashSet Name
                    -> Lemmas
                    -> Bindings
                    -> Config
                    -> NebulaConfig
                    -> Int
                    -> [(StateH, StateH)]
                    -> W.WriterT [Marker] IO (StepRes, Bindings, Int)
verifyLoopWithSymEx solver tactics num_lems ns lemmas b config nc k states = do
    let current_states = map getLatest states
    (paired_states, (b', k')) <- W.liftIO $ CM.runStateT (mapM (uncurry (runSymExec solver config nc ns)) current_states) (b, k)

    --W.liftIO $ putStrLn "verifyLoopWithSymEx"
    -- for every internal list, map with its corresponding original state
    let app_pair (sh1, sh2) (s1, s2) = (appendH sh1 s1, appendH sh2 s2)
        updated_hists = map (\(s, ps) -> map (app_pair s) ps) $ zip states paired_states
    --W.liftIO $ putStrLn $ show $ length $ concat updated_hists

    (res, b'') <- verifyLoop' solver tactics num_lems ns lemmas b' (concat updated_hists)
    return (res, b'', k')

verifyWithNewProvenLemmas :: S.Solver solver =>
                             solver
                          -> [NewLemmaTactic solver]
                          -> Int
                          -> HS.HashSet Name
                          -> [ProvenLemma]
                          -> Lemmas
                          -> Bindings
                          -> [(StateH, StateH)]
                          -> W.WriterT [Marker] IO (StepRes, Bindings)
verifyWithNewProvenLemmas solver nl_tactics num_lems ns proven lemmas b states = do
    let rel_states = map (\pl -> (lemma_lhs_origin pl, lemma_rhs_origin pl)) proven
        tactics = concatMap (\t -> map (uncurry t) rel_states) nl_tactics
    verifyLoop' solver tactics num_lems ns lemmas b states

verifyLemmasWithNewProvenLemmas :: S.Solver solver =>
                                   solver
                                -> [NewLemmaTactic solver]
                                -> Int
                                -> HS.HashSet Name
                                -> [ProvenLemma]
                                -> Lemmas
                                -> Bindings
                                -> Config
                                -> NebulaConfig
                                -> Int
                                -> W.WriterT [Marker] IO (Bindings, Int, [ProvenLemma], Lemmas)
verifyLemmasWithNewProvenLemmas solver nl_tactics num_lems ns proven lemmas b config nc k = do
    let rel_states = map (\pl -> (lemma_lhs_origin pl, lemma_rhs_origin pl)) proven
        tactics = concatMap (\t -> map (uncurry t) rel_states) nl_tactics

    --W.liftIO $ putStrLn "verifyLemmasWithNewProvenLemmas"
    (b', k', new_proven, lemmas') <-
          verifyLoopPropLemmas solver tactics num_lems ns lemmas b config nc k
    case null new_proven of
        True -> return (b', k', proven, lemmas')
        False ->
            let
                proven' = new_proven ++ proven
            in
            verifyLemmasWithNewProvenLemmas solver nl_tactics num_lems ns proven' lemmas' b' config nc k'

verifyLoop' :: S.Solver solver =>
               solver
            -> [Tactic solver]
            -> Int
            -> HS.HashSet Name
            -> Lemmas
            -> Bindings
            -> [(StateH, StateH)]
            -> W.WriterT [Marker] IO (StepRes, Bindings)
verifyLoop' solver tactics num_lems ns lemmas b states = do
    --W.liftIO $ putStrLn "verifyLoop'"
    let (fn1, ng') = freshName (name_gen b)
        (fn2, ng'') = freshName ng'
        b' = b { name_gen = ng'' }
 
        td (sh1, sh2) = tryDischarge solver tactics num_lems ns lemmas [fn1, fn2] sh1 sh2

    proof_lemma_list <- mapM td states

    let new_obligations = concatMap fst $ catMaybes proof_lemma_list
        new_lemmas = concatMap snd $ catMaybes proof_lemma_list

    let res = if | null proof_lemma_list -> Proven
                 | all isJust proof_lemma_list -> ContinueWith new_obligations new_lemmas
                 | otherwise -> CounterexampleFound
    return (res, b')

applyTacticToLabeledStates :: Tactic solver -> String -> String -> Tactic solver
applyTacticToLabeledStates tactic lbl1 lbl2 solver num_lems ns lemmas fresh_names (sh1, sh2) (s1, s2)
    | Just sh1' <- digInStateH lbl1 $ appendH sh1 s1 =
        tactic solver num_lems ns lemmas fresh_names (sh1', sh2) (latest sh1', latest sh2)
    | Just sh2' <- digInStateH lbl2 $ appendH sh2 s2 =
        tactic solver num_lems ns lemmas fresh_names (sh1, sh2') (latest sh1, latest sh2')
    | otherwise = return . NoProof $ []

digInStateH :: String -> StateH -> Maybe StateH
digInStateH lbl sh
    | (folder_name . track $ latest sh) == lbl = Just sh
    | Just sh' <- backtrackOne sh = digInStateH lbl sh'
    | otherwise = Nothing

updateDC :: EquivTracker -> [BlockInfo] -> EquivTracker
updateDC et ds = et { dc_path = dc_path et ++ ds }

-- It is not a problem that this function uses the type variable from only
-- the first lambda.  If the two StateET inputs come from corresponding
-- points in symbolic execution, the type variables from the two lambdas
-- must align with each other.
stateWrap :: Name -> StateET -> StateET -> Obligation -> (StateET, StateET)
stateWrap fresh_name s1 s2 (Ob ds e1 e2) =
  let ds' = map (\(d, i, n) -> BlockDC d i n) ds
  in case (e1, e2) of
    (Lam _ (Id _ t) _, Lam _ _ _) ->
      let fresh_id = Id fresh_name t
          fresh_var = Var fresh_id
          s1' = s1 {
            curr_expr = CurrExpr Evaluate $ App e1 fresh_var
          , track = updateDC (track s1) $ ds' ++ [BlockLam fresh_id]
          , expr_env = E.insertSymbolic fresh_id $ expr_env s1
          }
          s2' = s2 {
            curr_expr = CurrExpr Evaluate $ App e2 fresh_var
          , track = updateDC (track s2) $ ds' ++ [BlockLam fresh_id]
          , expr_env = E.insertSymbolic fresh_id $ expr_env s2
          }
      in (s1', s2')
    _ -> ( s1 { curr_expr = CurrExpr Evaluate e1, track = updateDC (track s1) ds' }
         , s2 { curr_expr = CurrExpr Evaluate e2, track = updateDC (track s2) ds' } )

-- the Bool value for EFail is True if a cycle has been found
data TacticEnd = EFail Bool
               | EDischarge
               | EContinue [Lemma] (StateH, StateH)

getRemaining :: TacticEnd -> [(StateH, StateH)] -> [(StateH, StateH)]
getRemaining (EContinue _ sh_pair) acc = sh_pair:acc
getRemaining _ acc = acc

getLemmas :: TacticEnd -> [Lemma]
getLemmas (EContinue lemmas _) = lemmas
getLemmas _ = []

hasFail :: [TacticEnd] -> Bool
hasFail [] = False
hasFail ((EFail _):_) = True
hasFail (_:es) = hasFail es

hasSolverFail :: [TacticEnd] -> Bool
hasSolverFail [] = False
hasSolverFail ((EFail False):_) = True
hasSolverFail (_:es) = hasSolverFail es

-- covers all of the solver obligations at once
trySolver :: S.Solver s => Tactic s
trySolver solver _ _ _ _ _ (s1, s2) | statePairReadyForSolver (s1, s2) = do
  let e1 = exprExtract s1
      e2 = exprExtract s2
  res <- W.liftIO $ checkObligations solver s1 s2 (HS.fromList [(e1, e2)])
  case res of
    S.UNSAT () -> return Success
    _ -> return $ Failure False
trySolver _ _ _ _ _ _ _ = return $ NoProof []

-- apply all tactics sequentially in a single run
-- make StateH adjustments between each application, if necessary
-- if Success ever appears, it's done
applyTactics :: S.Solver solver =>
                solver ->
                [Tactic solver] ->
                Int ->
                HS.HashSet Name ->
                Lemmas ->
                [Lemma] ->
                [Name] ->
                (StateH, StateH) ->
                (StateET, StateET) ->
                W.WriterT [Marker] IO TacticEnd
applyTactics solver (tac:tacs) num_lems ns lemmas gen_lemmas fresh_names (sh1, sh2) (s1, s2) = do
  tr <- tac solver num_lems ns lemmas fresh_names (sh1, sh2) (s1, s2)
  case tr of
    Failure b -> return $ EFail b
    NoProof new_lemmas -> applyTactics solver tacs num_lems ns lemmas (new_lemmas ++ gen_lemmas) fresh_names (sh1, sh2) (s1, s2)
    Success -> return EDischarge
applyTactics _ _ _ _ _ gen_lemmas _ (sh1, sh2) (s1, s2) =
    return $ EContinue gen_lemmas (replaceH sh1 s1, replaceH sh2 s2)

-- Nothing output means failure
-- fresh_names must have at least two elements
-- the first name is for stateWrap, the second is for the tactics
-- the only tactic left that uses fresh names is generalizeFull
-- still, there may be new tactics in the future that use fresh names
tryDischarge :: S.Solver solver =>
                solver ->
                [Tactic solver] ->
                Int ->
                HS.HashSet Name ->
                Lemmas ->
                [Name] ->
                StateH ->
                StateH ->
                W.WriterT [Marker] IO (Maybe ([(StateH, StateH)], [Lemma]))
tryDischarge solver tactics num_lems ns lemmas (fn:fresh_names) sh1 sh2 =
  let s1 = latest sh1
      s2 = latest sh2
  in case getObligations ns s1 s2 of
    Nothing -> do
      W.tell [Marker (sh1, sh2) $ NotEquivalent (s1, s2)]
      return Nothing
    Just obs -> do
      case obs of
        [] -> W.tell [Marker (sh1, sh2) $ NoObligations (s1, s2)]
        _ -> return ()
      -- just like with tactics, we only need one fresh name here
      let states = map (stateWrap fn s1 s2) obs
      res <- mapM (applyTactics solver tactics num_lems ns lemmas [] fresh_names (sh1, sh2)) states
      -- list of remaining obligations in StateH form
      let res' = foldr getRemaining [] res
          new_lemmas = concatMap getLemmas res
      if hasFail res then do
        if hasSolverFail res
          then W.tell [Marker (sh1, sh2) $ SolverFail (s1, s2)]
          else return ()
        return Nothing
      else do
        return $ Just (res', new_lemmas)
tryDischarge _ _ _ _ _ _ _ _ = error "Need more fresh names"

getObligations :: HS.HashSet Name ->
                  State t ->
                  State t ->
                  Maybe [Obligation]
getObligations ns s1 s2 =
  case proofObligations ns s1 s2 (exprExtract s1) (exprExtract s2) of
    Nothing -> Nothing
    Just obs -> Just $ HS.toList obs

addStackTickIfNeeded :: HS.HashSet Name -> ExprEnv -> Expr -> Expr
addStackTickIfNeeded ns h e' =
  let has_tick = getAny . evalASTs (\e -> case e of
                                          Tick (NamedLoc l) _
                                            | l == loc_name -> Any True
                                          _ -> Any False) $ e'
  in if has_tick then e' else tickWrap ns h e'

tickWrap :: HS.HashSet Name -> ExprEnv -> Expr -> Expr
tickWrap ns h (Var (Id n _))
    | not (n `HS.member` ns)
    , Just (E.Conc e) <- E.lookupConcOrSym n h = tickWrap ns h e 
tickWrap ns h (Case e i t a) = Case (tickWrap ns h e) i t a
tickWrap ns h (App e1 e2) = App (tickWrap ns h e1) e2
tickWrap ns h te@(Tick nl e) | not (isLabeledError te) = Tick nl (tickWrap ns h e)
tickWrap _ _ e = Tick (NamedLoc loc_name) e

includedName :: [DT.Text] -> Name -> Bool
includedName texts (Name t _ _ _) = t `elem` texts

-- stack tick should appear inside rec tick
startingState :: EquivTracker -> HS.HashSet Name -> State t -> StateH
startingState et ns s =
  let h = expr_env s
      -- Tick wrapping for recursive and corecursive functions
      wrap_cg = wrapAllRecursion (G.getCallGraph h) h
      h' = E.map (wrapLetRec h) $ E.mapWithKey wrap_cg h
      all_names = E.keys h
      s' = s {
      track = et
    , curr_expr = CurrExpr Evaluate $ tickWrap ns h $ foldr wrap_cg (exprExtract s) all_names
    , expr_env = h'
    }
  in newStateH s'

cleanState :: State t -> Bindings -> (State t, Bindings)
cleanState state bindings =
  let sym_config = addSearchNames (input_names bindings)
                   $ addSearchNames (M.keys $ deepseq_walkers bindings) emptyMemConfig
  in markAndSweepPreserving sym_config state bindings

-- If the Marker list is reversed from how it was when it was fetched, then
-- we're guaranteed to get something that came from the main proof rather than
-- a lemma.  Lemma examination happens first within iterations.
writeCX :: [Marker] ->
           PrettyGuide ->
           HS.HashSet Name ->
           [Id] ->
           (State t, State t) ->
           String
writeCX [] _ _ _ _ = error "No Counterexample"
writeCX ((Marker hist m):ms) pg ns sym_ids init_pair = case m of
  NotEquivalent s_pair -> showCX pg ns sym_ids hist init_pair s_pair
  SolverFail s_pair -> showCX pg ns sym_ids hist init_pair s_pair
  CycleFound cm -> showCycle pg ns sym_ids hist init_pair cm
  _ -> writeCX ms pg ns sym_ids init_pair
writeCX (_:ms) pg ns sym_ids init_pair =
  writeCX ms pg ns sym_ids init_pair

-- This function relies on the assumption that, if symbolic execution for
-- the main expression pair hits a counterexample, that counterexample
-- will be the final counterexample in the Marker list (alternatively, the
-- first counterexample in the reversed list that this takes as input).
-- Lemma  counterexamples appear in the same list and are not distinguished
-- in any special way, but, in each loop iteration, lemma execution happens
-- before execution on the main expression pair.  If the main execution
-- hits a counterexample, the iteration when it happens will be the final
-- loop iteration, so we have an indirect guarantee that the counterexample
-- covered here will not be one from a lemma.
reducedGuide :: [Marker] -> PrettyGuide
reducedGuide [] = error "No Counterexample"
reducedGuide ((Marker _ m):ms) = case m of
  NotEquivalent _ -> mkPrettyGuide m
  SolverFail _ -> mkPrettyGuide m
  CycleFound _ -> mkPrettyGuide m
  _ -> reducedGuide ms
reducedGuide (_:ms) = reducedGuide ms

checkRule :: Config
          -> NebulaConfig
          -> State t
          -> Bindings
          -> [DT.Text] -- ^ names of forall'd variables required to be total
          -> RewriteRule
          -> IO (S.Result () () ())
checkRule config nc init_state bindings total rule = do
  let (rewrite_state_l, bindings') = initWithLHS init_state bindings $ rule
      (rewrite_state_r, bindings'') = initWithRHS init_state bindings' $ rule
      sym_ids = ru_bndrs rule
      total_names = filter (includedName total) (map idName sym_ids)
      total_hs = foldr HS.insert HS.empty total_names
      EquivTracker et m _ _ _ _ = emptyEquivTracker
      start_equiv_tracker = EquivTracker et m total_hs [] E.empty ""
      -- the keys are the same between the old and new environments
      ns_l = HS.fromList $ E.keys $ expr_env rewrite_state_l
      ns_r = HS.fromList $ E.keys $ expr_env rewrite_state_r
      -- no need for two separate name sets
      ns = HS.filter (\n -> not (E.isSymbolic n $ expr_env rewrite_state_l)) $ HS.union ns_l ns_r
      e_l = exprExtract rewrite_state_l
      (rewrite_state_l',_) = cleanState (rewrite_state_l { curr_expr = CurrExpr Evaluate e_l }) bindings
      e_r = exprExtract rewrite_state_r
      (rewrite_state_r',_) = cleanState (rewrite_state_r { curr_expr = CurrExpr Evaluate e_r }) bindings
      
      rewrite_state_l'' = startingState start_equiv_tracker ns rewrite_state_l'
      rewrite_state_r'' = startingState start_equiv_tracker ns rewrite_state_r'

  S.SomeSolver solver <- initSolver config
  putStrLn $ "***\n" ++ (show $ ru_name rule) ++ "\n***"
  putStrLn $ printHaskellDirty e_l
  putStrLn $ printHaskellDirty e_r
  putStrLn $ printHaskellDirty $ exprExtract $ latest rewrite_state_l''
  putStrLn $ printHaskellDirty $ exprExtract $ latest rewrite_state_r''
  (res, w) <- W.runWriterT $ verifyLoop solver (num_lemmas nc) ns
             emptyLemmas
             [(rewrite_state_l'', rewrite_state_r'')]
             bindings'' config nc sym_ids 0 (limit nc)
  let pg = if have_summary $ print_summary nc
           then mkPrettyGuide w-- $ map (\(Marker _ am) -> am) w
           else reducedGuide (reverse w)
  if have_summary $ print_summary nc then do
    putStrLn "--- SUMMARY ---"
    _ <- mapM (putStrLn . (summarize (print_summary nc) pg ns sym_ids)) w
    putStrLn "--- END OF SUMMARY ---"
  else return ()
  case res of
    S.SAT () -> do
      putStrLn "--------------------"
      putStrLn "COUNTEREXAMPLE FOUND"
      putStrLn "--------------------"
      putStrLn $ writeCX (reverse w) pg ns sym_ids (rewrite_state_l, rewrite_state_r)
    _ -> return ()
  S.close solver
  return res
