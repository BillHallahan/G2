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
import G2.Equiv.Induction
import G2.Equiv.Summary

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

-- TODO reader / writer monad source consulted
-- https://mmhaskell.com/monads/reader-writer

import qualified Control.Monad.Writer.Lazy as W

-- 9/27 notes
-- TODO have a list of every single state, not just the stopping ones
-- At least be able to say what rules are being applied at every step
-- Applications of induction and coinduction for different branches
-- turn Case into Let for forcing, induction
-- split into multiple branches for Case-Let thing?
-- if the final value doesn't match what we expect, throw the branch out somehow
-- have some notion of finite variables still in place?
-- wrap finite things in force functions
-- The value of discharge should be the previously-encountered state pair that
-- was used to discharge this branch, if the branch has been discharged.
-- TODO requiring finiteness for forceIdempotent makes verifier get stuck
-- same goes for p10 in Zeno

-- TODO include history?
{-
data EquivMarker = EquivMarker {
    real_present :: (StateET, StateET)
  , used_present :: (StateET, StateET)
}
-}

-- TODO this should be the output from tryDischarge
-- unfinished is what tryDischarge gave as output before
-- finished is the proof obligations that were just discharged
data DischargeResult = DischargeResult {
    unfinished :: [(StateH, StateH)]
  , finished :: [(StateH, StateH)]
  , bad_states :: Maybe [(StateET, StateET)]
}

-- TODO starting Writer functions
-- TODO what should the second writer type be?
noteBasicDischarge :: String -> (StateET, StateET) -> W.WriterT String IO ()
noteBasicDischarge msg (s1, s2) = do
  let fn1 = folder_name $ track s1
      fn2 = folder_name $ track s2
      out_str = "(" ++ fn1 ++ "," ++ fn2 ++ ") " ++ msg ++ "\n"
  W.tell out_str
  return ()

{-
TODO
Information to provide for induction:
Real present states, their expressions
Fake present states, their expressions
Past states, their expressions
Present scrutinees used
Past scrutinees used
Fresh variable name
New generalized expressions for the present

Information to provide for coinduction:
Real present, fake present, past
-}

statePairReadyForSolver :: (State t, State t) -> Bool
statePairReadyForSolver (s1, s2) =
  let h1 = expr_env s1
      h2 = expr_env s2
      CurrExpr _ e1 = curr_expr s1
      CurrExpr _ e2 = curr_expr s2
  in
  exprReadyForSolver h1 e1 && exprReadyForSolver h2 e2

-- don't log when the base folder name is empty
logStatesFolder :: String -> String -> LogMode
logStatesFolder _ "" = NoLog
logStatesFolder pre fr = Log Pretty $ fr ++ "/" ++ pre

logStatesET :: String -> String -> String
logStatesET pre fr = fr ++ "/" ++ pre

runSymExec :: S.Solver solver =>
              solver ->
              Config ->
              String ->
              StateET ->
              StateET ->
              CM.StateT (Bindings, Int) IO [(StateET, StateET)]
runSymExec solver config folder_root s1 s2 = do
  CM.liftIO $ putStrLn "runSymExec"
  ct1 <- CM.liftIO $ getCurrentTime
  (bindings, k) <- CM.get
  let config' = config { logStates = logStatesFolder ("a" ++ show k) folder_root }
      t1 = (track s1) { folder_name = logStatesET ("a" ++ show k) folder_root }
      -- TODO always Evaluate here?
      CurrExpr r1 e1 = curr_expr s1
      e1' = addStackTickIfNeeded e1
      s1' = s1 { track = t1, curr_expr = CurrExpr r1 e1' }
  CM.liftIO $ putStrLn $ (show $ folder_name $ track s1) ++ " becomes " ++ (show $ folder_name t1)
  (er1, bindings') <- CM.lift $ runG2ForRewriteV s1' (expr_env s2) (track s2) config' bindings
  CM.put (bindings', k + 1)
  let final_s1 = map final_state er1
  pairs <- mapM (\s1_ -> do
                    (b_, k_) <- CM.get
                    let s2_ = transferTrackerInfo s1_ s2
                    ct2 <- CM.liftIO $ getCurrentTime
                    let config'' = config { logStates = logStatesFolder ("b" ++ show k_) folder_root }
                        t2 = (track s2_) { folder_name = logStatesET ("b" ++ show k_) folder_root }
                        CurrExpr r2 e2 = curr_expr s2_
                        e2' = addStackTickIfNeeded e2
                        s2' = s2_ { track = t2, curr_expr = CurrExpr r2 e2' }
                    CM.liftIO $ putStrLn $ (show $ folder_name $ track s2_) ++ " becomes " ++ (show $ folder_name t2)
                    (er2, b_') <- CM.lift $ runG2ForRewriteV s2' (expr_env s1_) (track s1_) config'' b_
                    CM.put (b_', k_ + 1)
                    return $ map (\er2_ -> 
                                    let
                                        s2_' = final_state er2_
                                        s1_' = transferTrackerInfo s2_' s1_
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

-- Don't share expr env and path constraints between sides
-- info goes from left to right
-- TODO union instead?
transferTrackerInfo :: StateET -> StateET -> StateET
transferTrackerInfo s1 s2 =
  let t1 = track s1
      t2 = track s2
      t2' = t2 {
        higher_order = higher_order t1
      , total = total t1-- HS.union (total t1) (total t2)
      , finite = finite t1-- HS.union (finite t1) (finite t2)
      }
  in s2 { track = t2' }

frameWrap :: Frame -> Expr -> Expr
frameWrap (CaseFrame i alts) e = Case e i alts
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

-- TODO also modify the expression itself directly?
wrcHelper :: Name -> Expr -> Expr
wrcHelper n = modifyChildren (wrapRecursiveCall n)

-- Creating a new expression environment lets us use the existing reachability
-- functions.
-- TODO does the expr env really need to keep track of Lets above this?
-- look inside the bindings and inside the body for recursion
-- TODO I should merge this process with the other wrapping?
-- TODO do I need an extra process for some other recursive structure?
wrapLetRec :: ExprEnv -> Expr -> Expr
wrapLetRec h (Let binds e) =
  let binds1 = map (\(i, e_) -> (idName i, e_)) binds
      -- TODO better name for this?
      fresh_name = Name (DT.pack "FRESH") Nothing 0 Nothing
      h' = foldr (\(n_, e_) h_ -> E.insert n_ e_ h_) h ((fresh_name, e):binds1)
      -- TODO this needs to be a 2D map?
      -- Leave it as 1D for now
      -- TODO this might be doing more work than is necessary
      wrap_cg = wrapAllRecursion (G.getCallGraph h') h'
      binds2 = map (\(n_, e_) -> (n_, wrap_cg n_ e_)) binds1
      -- TODO will Tick insertions accumulate?
      -- TODO doesn't work, again because nothing reaches fresh_name
      -- should I even need wrapping like this within the body?
      e' = foldr (wrapIfCorecursive (G.getCallGraph h') h' fresh_name) e (map fst binds1)
      -- TODO do I need to do this twice over like this?
      -- doesn't fix the problem of getting stuck
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
wrapIfCorecursive :: G.CallGraph -> ExprEnv -> Name -> Name -> Expr -> Expr
wrapIfCorecursive cg h n m e =
  let n_list = G.reachable n cg
      m_list = G.reachable m cg
  in
  if (n `elem` m_list) && (m `elem` n_list)
  then
    if E.isSymbolic m h
    then e
    else ((wrcHelper m) . (wrapRecursiveCall m)) (wrapRecursiveCall m e)
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

tickWrap :: Expr -> Expr
tickWrap (Case e i a) = Case (tickWrap e) i a
tickWrap (App e1 e2) = App (tickWrap e1) e2
tickWrap (Tick nl e) = Tick nl (tickWrap e)
tickWrap e = Tick (NamedLoc loc_name) e

-- TODO don't add stack tick here, just add the stack
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
insertStamps x k (Case e i a) =
  case a of
    (Alt am1 a1):as -> case a1 of
        Tick (NamedLoc (Name n _ _ _)) e' | str <- DT.unpack n
                                          , ':' `elem` str ->
          Case (insertStamps (x + 1) k e) i a
        _ -> let sn = stampName x k
                 a1' = Alt am1 (Tick (NamedLoc sn) a1)
             in Case (insertStamps (x + 1) k e) i (a1':as)
    _ -> error "Empty Alt List"
insertStamps _ _ e = e

addStamps :: Int -> StateET -> StateET
addStamps k s =
  let CurrExpr c e = curr_expr s
      e' = insertStamps 0 k e
  in s { curr_expr = CurrExpr c e' }

getLatest :: (StateH, StateH) -> (StateET, StateET)
getLatest (StateH { latest = s1 }, StateH { latest = s2 }) = (s1, s2)

newStateH :: StateET -> StateH
newStateH s = StateH {
    latest = s
  , history = []
  , inductions = []
  , discharge = Nothing
  }

-- discharge only has a meaningful value when execution is done for a branch
appendH :: StateH -> StateET -> StateH
appendH sh s =
  StateH {
    latest = s
  , history = (latest sh):(history sh)
  , inductions = inductions sh
  , discharge = discharge sh
  }

replaceH :: StateH -> StateET -> StateH
replaceH sh s = sh { latest = s }

-- TODO allow a negative loop iteration count for unlimited iterations
verifyLoop :: S.Solver solver =>
              solver ->
              HS.HashSet Name ->
              [(StateH, StateH)] ->
              [(StateH, StateH)] ->
              Bindings ->
              Config ->
              String ->
              Int ->
              Int ->
              W.WriterT [Marker] IO (S.Result () ())
verifyLoop solver ns states prev b config folder_root k n | not (null states)
                                                          , n /= 0 = do
  let current_states = map getLatest states
  (paired_states, (b', k')) <- W.liftIO $ CM.runStateT (mapM (uncurry (runSymExec solver config folder_root)) current_states) (b, k)
  let ng = name_gen b'
      (fresh_name, ng') = freshName ng
      b'' = b' { name_gen = ng' }
      simplify dr = do
        dr' <- dr
        case bad_states dr' of
          Nothing -> return $ Just $ unfinished dr'
          Just _ -> return Nothing
      -- TODO don't use a universal prev list; every exec path has its own
      vl (sh1, sh2) = simplify $ tryDischarge solver ns fresh_name sh1 sh2 (zip (history sh1) (history sh2))
  -- TODO printing
  W.liftIO $ putStrLn "<Loop Iteration>"
  W.liftIO $ putStrLn $ show n
  -- for every internal list, map with its corresponding original state
  let app_pair (sh1, sh2) (s1, s2) = (appendH sh1 s1, appendH sh2 s2)
      map_fns = map app_pair states
      updated_hists = map (uncurry map) (zip map_fns paired_states)
  W.liftIO $ putStrLn $ show $ length $ concat updated_hists
  proof_list <- mapM vl $ concat updated_hists
  let new_obligations = concat [l | Just l <- proof_list]
      prev' = new_obligations ++ prev
      n' = if n > 0 then n - 1 else n
  W.liftIO $ putStrLn $ show $ length new_obligations
  if all isJust proof_list then
    verifyLoop solver ns new_obligations prev' b'' config folder_root k' n'
  else
    return $ S.SAT ()
  | not (null states) = do
    return $ S.Unknown "Loop Iterations Exhausted"
  | otherwise = do
    return $ S.UNSAT ()

stateWrap :: StateET -> StateET -> Obligation -> (StateET, StateET)
stateWrap s1 s2 (Ob e1 e2) =
  ( s1 { curr_expr = CurrExpr Evaluate e1 }
  , s2 { curr_expr = CurrExpr Evaluate e2 } )

-- helper functions for induction
-- TODO can something other than Case be at the outermost level?
caseRecursion :: Expr -> Bool
caseRecursion (Tick _ e) = caseRecursion e
caseRecursion (Case e _ _) =
  (getAny . evalASTs (\e' -> Any $ caseRecHelper e')) e
caseRecursion _ = False

-- TODO this shouldn't need to look more deeply since it's used with evalASTs
caseRecHelper :: Expr -> Bool
caseRecHelper (Tick (NamedLoc (Name t _ _ _)) _) = t == DT.pack "REC"
caseRecHelper _ = False

-- We only apply induction to a pair of expressions if both expressions are
-- Case statements whose scrutinee includes a recursive function or variable
-- use.  Induction is sound as long as the two expressions are Case statements,
-- but, if no recursion is involved, ordinary coinduction is just as useful.
-- We prefer coinduction in that scenario because it is more efficient.
canUseInduction :: Obligation -> Bool
canUseInduction (Ob e1 e2) = caseRecursion e1 && caseRecursion e2

isNothingM :: Monad m => m (Maybe t) -> m Bool
isNothingM = liftM (not . isJust)

-- TODO debugging function
stateHistory :: StateH -> StateH -> [(StateET, StateET)]
stateHistory sh1 sh2 =
  let hist1 = (latest sh1):(history sh1)
      hist2 = (latest sh2):(history sh2)
  in reverse $ zip hist1 hist2

exprTrace :: StateH -> StateH -> [String]
exprTrace sh1 sh2 =
  let s_hist = stateHistory sh1 sh2
      s_pair (s1, s2) = [
          printHaskellDirty (exprExtract s1)
        , printHaskellDirty (exprExtract s2)
        , show (E.symbolicIds $ expr_env s1)
        , show (E.symbolicIds $ expr_env s2)
        , show (track s1)
        , show (track s2)
        , show (length $ inductions sh1)
        , show (length $ inductions sh2)
        --, show (exprExtract s1)
        --, show (exprExtract s2)
        , "------"
        ]
  in concat $ map s_pair s_hist

addDischarge :: StateET -> StateH -> StateH
addDischarge s sh = sh { discharge = Just s }

-- TODO don't use for now
{-
addInduction :: StateET -> StateH -> StateH
addInduction s sh =
  let im = IndMarker s s (latest sh)
  in sh { inductions = im:(inductions sh) }
-}

-- TODO a better setup would also indicate which side was used for induction
-- TODO just return (sh1, sh2) in failure event?
-- TODO I can add induction markers here; preserve the old states
-- q1 and q2 were the states used for the induction
-- TODO more reworking would be necessary to get the actual past states used
-- TODO could be losing valuable parts of history from this
makeIndStateH :: (StateH, StateH) ->
                 ((StateET, StateET), ((Int, Int), StateET, StateET)) ->
                 (StateH, StateH)
makeIndStateH (sh1, sh2) ((q1, q2), ((n1, n2), s1, s2)) | n1 >= 0, n2 >= 0 =
  let hist1 = drop n1 $ history sh1
      hist2 = drop n2 $ history sh2
      sh1' = sh1 { history = hist1, latest = s1 }
      sh2' = sh2 { history = hist2, latest = s2 }
      --im1 = IndMarker q2 q1 s1
      --im2 = IndMarker q1 q2 s2
  in (sh1', sh2')
  | otherwise = (sh1 { latest = s1 }, sh2 { latest = s2 })

-- TODO printing
-- TODO was the type signature wrong before?
-- TODO prev not used anymore
-- TODO have something other than a string as the Writer accumulator
tryDischarge :: S.Solver solver =>
                solver ->
                HS.HashSet Name ->
                Name ->
                StateH ->
                StateH ->
                [(StateET, StateET)] ->
                W.WriterT [Marker] IO DischargeResult
tryDischarge solver ns fresh_name sh1 sh2 prev =
  let s1 = latest sh1
      s2 = latest sh2
  in
  case getObligations ns s1 s2 of
    Nothing -> do
      W.tell [Marker (sh1, sh2) $ NotEquivalent (s1, s2)]
      -- obligation generation failed, so the expressions must not be equivalent
      W.liftIO $ putStrLn $ "N! " ++ (show $ folder_name $ track s1) ++ " " ++ (show $ folder_name $ track s2)
      W.liftIO $ putStrLn $ show $ exprExtract s1
      W.liftIO $ putStrLn $ show $ exprExtract s2
      W.liftIO $ mapM putStrLn $ exprTrace sh1 sh2
      -- TODO what to return here?
      -- all left unfinished, nothing resolved
      -- bad_states are the ones right here
      return $ DischargeResult [] [] (Just [(s1, s2)])
    Just obs -> do
      -- TODO Writer logging
      case obs of
        [] -> W.tell [Marker (sh1, sh2) $ NoObligations (s1, s2)]
        _ -> return ()
      W.liftIO $ putStrLn $ "J! " ++ (show $ folder_name $ track s1) ++ " " ++ (show $ folder_name $ track s2)
      W.liftIO $ putStrLn $ printHaskellDirty $ exprExtract s1
      W.liftIO $ putStrLn $ printHaskellDirty $ exprExtract s2
      --putStrLn $ show $ exprExtract s1
      --putStrLn $ show $ exprExtract s2

      -- TODO new prev'
      let -- prev' = prevFiltered (sh1, sh2)
          (obs_i, obs_c) = partition canUseInduction obs
          states_c = map (stateWrap s1 s2) obs_c
      -- TODO do I need more adjustments than what I have here?
      discharges_e <- mapM (tryEquality solver ns (sh1, sh2)) states_c
      discharges_c <- mapM (tryCoinduction solver ns (sh1, sh2)) states_c
      let either_maybe (Just x, _) = Just x
          either_maybe (Nothing, y) = y
          discharges = map either_maybe (zip discharges_e discharges_c)
      -- get the states and histories for the successful discharges
      -- will need to fill in the discharge field
      -- also need to pair them up with the original states?
      -- there's only one original state pair
      let discharges' = [(d, sp) | (Just (PrevMatch _ d _ _), sp) <- zip discharges states_c]
          matches1 = [(d1, s1_) | ((d1, _), (s1_, _)) <- discharges']
          matches1' = map (\(d1, s1_) -> addDischarge d1 $ replaceH sh1 s1_) matches1
          matches2 = [(d2, s2_) | ((_, d2), (_, s2_)) <- discharges']
          matches2' = map (\(d2, s2_) -> addDischarge d2 $ replaceH sh2 s2_) matches2
          matches = zip matches1' matches2'
      let discharges_ = map (not . isJust) discharges
          states_c' = map snd $ filter fst (zip discharges_ states_c)

      let states_i = map (stateWrap s1 s2) obs_i
      states_i1 <- filterM (isNothingM . (tryEquality solver ns (sh1, sh2))) states_i
      states_i2 <- filterM (isNothingM . (tryCoinduction solver ns (sh1, sh2))) states_i1
      -- TODO need a way to get the prev pair used for induction
      states_i' <- mapM (inductionFull solver ns fresh_name (sh1, sh2)) states_i2
      --states_i' <- filterM (notM . (induction solver ns fresh_name prev')) states_i

      -- TODO unnecessary to pass the induction states through this?
      let (ready, not_ready) = partition statePairReadyForSolver states_c'
          ready_exprs = HS.fromList $ map (\(r1, r2) -> (exprExtract r1, exprExtract r2)) ready
          not_ready_h1 = map (\(n1, n2) -> (replaceH sh1 n1, replaceH sh2 n2)) not_ready
          -- TODO crude solution:  induction states lose their history
          -- seems to cause some other problems
          not_ready_h2 = map (makeIndStateH (sh1, sh2)) (zip states_i states_i')
          not_ready_h = not_ready_h1 ++ not_ready_h2
          -- TODO what debug information do I give for these?
          -- let the "discharge" state be the current state itself?
          -- I think that's good enough for now
          ready_solved = map
                        (\(n1, n2) -> (addDischarge n1 $ replaceH sh1 n1, addDischarge n2 $ replaceH sh2 n2))
                        ready
      res <- W.liftIO $ checkObligations solver s1 s2 ready_exprs
      case res of
        S.UNSAT () -> W.liftIO $ putStrLn $ "V? " ++ show (length not_ready_h)
        _ -> do
          W.liftIO $ putStrLn "X?"
          W.tell [Marker (sh1, sh2) $ SolverFail (s1, s2)]
      case res of
        -- TODO discharged exprs should come from filter and solver
        S.UNSAT () -> return $ DischargeResult not_ready_h (matches ++ ready_solved) Nothing
        _ -> return $ DischargeResult not_ready_h (matches ++ ready_solved) (Just ready)

-- TODO (11/10) need to move total-finite info for induction
-- info from first tracker gets added to the second
-- TODO left takes precedence in union?
-- TODO unused
mergeTrackers :: EquivTracker -> EquivTracker -> EquivTracker
mergeTrackers t1 t2 = t2 {
    higher_order = HM.union (higher_order t1) (higher_order t2)
  , total = HS.union (total t1) (total t2)
  , finite = HS.union (finite t1) (finite t2)
}

-- combinations to try:
-- try current left state with all right scrutinees and all prior state pairs
-- try current right state with all left scrutinees and all prior state pairs
-- also need to do substitutions coming from moreRestrictivePair
-- those come later, on the combinations that work out
-- TODO (11/8) clear out some of past if old state used as "present"
-- substitution happens on the left here
{-
inductionL :: S.Solver solver =>
              solver ->
              HS.HashSet Name ->
              [(StateET, StateET)] ->
              (StateET, StateET) ->
              IO (Bool, StateET, StateET)
inductionL solver ns prev (s1, s2) = do
  let scr1 = innerScrutinees $ exprExtract s1
      scr2 = innerScrutinees $ exprExtract s2
      scr_pairs = [(sc1, sc2) | sc1 <- scr1, sc2 <- scr2]
      scr_states = [(s1 { curr_expr = CurrExpr Evaluate sc1 }, s2 { curr_expr = CurrExpr Evaluate sc2 }) | (sc1, sc2) <- scr_pairs]
  mr_pairs <- mapM (moreRestrictiveIndRight solver ns prev) scr_states
  let mr_zipped = zip scr_pairs mr_pairs
      working_info = [(sc1, sc2, pm) | ((sc1, sc2), Just pm) <- mr_zipped]
      working_info' = filter (\(_, _, PrevMatch _ (_, p2) _ pc2) -> validScrutinee s2 p2 pc2) working_info
  -- TODO make an arbitrary choice about which working combination to return
  -- need to make a substitution for it
  -- going with left substitution for now
  case working_info' of
    [] -> return (False, s1, s2)
    -- TODO use the "current" pair
    -- TODO some of this doesn't matter anymore
    h:_ -> let (sc1, sc2, PrevMatch (q1, q2) (p1, p2) (mapping, _) pc2) = h
               e2_old = exprExtract pc2
               hm_list = HM.toList mapping
               e2_old' = foldr (\(i, e) acc -> replaceASTs (Var i) e acc) e2_old hm_list
               e1_new = replaceScrutinee sc1 e2_old' $ exprExtract s1
               -- TODO use s2 or pc2 here?  Probably s2
               h1_new = E.union (expr_env s1) (expr_env pc2)
               si1_new = map (\(Var i) -> i) . E.elems $ E.filterToSymbolic h1_new
               s1' = s1 {
                 curr_expr = CurrExpr Evaluate e1_new
               , expr_env = h1_new
               , symbolic_ids = si1_new
               --, track = mergeTrackers (track pc2) (track s1)
               }
           in trace ("YL " ++ show (length working_info')) $
              trace (printHaskellDirty sc1) $
              trace (printHaskellDirty e2_old) $
              trace (printHaskellDirty e2_old') $
              trace (printHaskellDirty $ exprExtract s1) $
              trace (printHaskellDirty e1_new) $
              trace ("HM " ++ show hm_list) $
              trace (show (map (\(r1, r2) -> (folder_name $ track r1, folder_name $ track r2)) prev)) $
              trace ("YES IL! " ++ show (map (folder_name . track) [s1, s2, q1, q2, p1, p2])) $
              return (True, s1', s2)
-}

-- TODO reduce duplicated code?  Also make sure it's correct
-- substitution happens on the right here
{-
inductionR :: S.Solver solver =>
              solver ->
              HS.HashSet Name ->
              [(StateET, StateET)] ->
              (StateET, StateET) ->
              W.WriterT [Marker] IO (Bool, StateET, StateET)
inductionR solver ns prev (s1, s2) = do
  let scr1 = innerScrutinees $ exprExtract s1
      scr2 = innerScrutinees $ exprExtract s2
      scr_pairs = [(sc1, sc2) | sc1 <- scr1, sc2 <- scr2]
      scr_states = [(s1 { curr_expr = CurrExpr Evaluate sc1 }, s2 { curr_expr = CurrExpr Evaluate sc2 }) | (sc1, sc2) <- scr_pairs]
  mr_pairs <- mapM (moreRestrictiveIndLeft solver ns prev) scr_states
  let mr_zipped = zip scr_pairs mr_pairs
      working_info = [(sc1, sc2, pm) | ((sc1, sc2), Just pm) <- mr_zipped]
      working_info' = filter (\(_, _, PrevMatch _ (p1, _) _ pc1) -> validScrutinee s1 p1 pc1) working_info
  case working_info' of
    [] -> return (False, s1, s2)
    h:_ -> let (sc1, sc2, PrevMatch (q1, q2) (p1, p2) (mapping, _) pc1) = h
               e1_old = exprExtract pc1
               hm_list = HM.toList mapping
               e1_old' = foldr (\(i, e) acc -> replaceASTs (Var i) e acc) e1_old hm_list
               e2_new = replaceScrutinee sc2 e1_old' $ exprExtract s2
               -- TODO use s1 or pc1 here?
               -- the s1 version gets an error that pc1 doesn't
               h2_new = E.union (expr_env s2) (expr_env pc1)
               s2' = s2 {
                 curr_expr = CurrExpr Evaluate e2_new
               , expr_env = h2_new
               }
           in trace ("YR " ++ show (length working_info')) $
              trace (printHaskellDirty sc2) $
              trace (printHaskellDirty e1_old) $
              trace (printHaskellDirty e1_old') $
              trace (printHaskellDirty $ exprExtract s2) $
              trace (printHaskellDirty e2_new) $
              trace ("HM " ++ show hm_list) $
              trace (show (map (\(r1, r2) -> (folder_name $ track r1, folder_name $ track r2)) prev)) $
              trace ("YES IR! " ++ show (map (folder_name . track) [s1, s2, q1, q2, p1, p2])) $
              return (True, s1, s2')
-}

-- TODO (9/27) check path constraint implication?
-- TODO (9/30) alternate:  just substitute one scrutinee for the other
-- put a non-symbolic variable there?

getObligations :: HS.HashSet Name ->
                  State t ->
                  State t ->
                  Maybe [Obligation]
getObligations ns s1 s2 =
  case proofObligations ns s1 s2 (exprExtract s1) (exprExtract s2) of
    Nothing -> Nothing
    Just obs -> Just $ HS.toList obs

addStackTickIfNeeded :: Expr -> Expr
addStackTickIfNeeded e' =
  let has_tick = getAny . evalASTs (\e -> case e of
                                          Tick (NamedLoc l) _
                                            | l == loc_name -> Any True
                                          _ -> Any False) $ e'
  in if has_tick then e' else tickWrap e'

includedName :: [DT.Text] -> Name -> Bool
includedName texts (Name t _ _ _) = t `elem` texts

-- stack tick should appear inside rec tick
startingState :: EquivTracker -> State t -> StateH
startingState et s =
  let h = expr_env s
      -- Tick wrapping for recursive and corecursive functions
      wrap_cg = wrapAllRecursion (G.getCallGraph h) h
      h' = E.map (wrapLetRec h) $ E.mapWithKey wrap_cg h
      all_names = E.keys h
      s' = s {
      track = et
    , curr_expr = CurrExpr Evaluate $ tickWrap $ foldr wrap_cg (exprExtract s) all_names
    , expr_env = h'
    }
  in newStateH s'

unused_name :: Name
unused_name = Name (DT.pack "UNUSED") Nothing 0 Nothing

-- TODO get the actual symbolic vars that correspond to the finite names
-- at the very least, I need the Ids
-- Case statements force evaluation to SWHNF in G2
-- TODO what to use as the extra Id for the Case statement?
-- TODO the force function needs to match the type of the symbolic var
-- I don't know if this will work as it is now
-- TODO adding extra stack tick here doesn't help
forceFinite :: Walkers -> Id -> Expr -> Expr
forceFinite w i e =
  let e' = mkStrict w $ Var i
      i' = Id unused_name (typeOf $ Var i)
      a = Alt Default e
  in Case e' i' [a]

cleanState :: State t -> Bindings -> (State t, Bindings)
cleanState state bindings =
  let sym_config = addSearchNames (input_names bindings)
                   $ addSearchNames (M.keys $ deepseq_walkers bindings) emptyMemConfig
  in markAndSweepPreserving sym_config state bindings

checkRule :: Config ->
             State t ->
             Bindings ->
             [DT.Text] -> -- ^ names of forall'd variables required to be total
             [DT.Text] -> -- ^ names of forall'd variables required to be total and finite
             RewriteRule ->
             IO (S.Result () ())
checkRule config init_state bindings total finite rule = do
  let (rewrite_state_l, bindings') = initWithLHS init_state bindings $ rule
      (rewrite_state_r, bindings'') = initWithRHS init_state bindings' $ rule
      total_names = filter (includedName total) (map idName $ ru_bndrs rule)
      finite_names = filter (includedName finite) (map idName $ ru_bndrs rule)
      finite_hs = foldr HS.insert HS.empty finite_names
      -- always include the finite names in total
      total_hs = foldr HS.insert finite_hs total_names
      EquivTracker et m _ _ _ = emptyEquivTracker
      start_equiv_tracker = EquivTracker et m total_hs finite_hs ""
      -- the keys are the same between the old and new environments
      ns_l = HS.fromList $ E.keys $ expr_env rewrite_state_l
      ns_r = HS.fromList $ E.keys $ expr_env rewrite_state_r
      -- no need for two separate name sets
      ns = HS.filter (\n -> not (E.isSymbolic n $ expr_env rewrite_state_l)) $ HS.union ns_l ns_r
      -- TODO wrap both sides with forcings for finite vars
      -- get the finite vars first
      -- TODO a little redundant with the earlier stuff
      finite_ids = filter ((includedName finite) . idName) (ru_bndrs rule)
      walkers = deepseq_walkers bindings''
      e_l = exprExtract rewrite_state_l
      e_l' = foldr (forceFinite walkers) e_l finite_ids
      (rewrite_state_l',_) = cleanState (rewrite_state_l { curr_expr = CurrExpr Evaluate e_l' }) bindings
      e_r = exprExtract rewrite_state_r
      e_r' = foldr (forceFinite walkers) e_r finite_ids
      (rewrite_state_r',_) = cleanState (rewrite_state_r { curr_expr = CurrExpr Evaluate e_r' }) bindings
      
      rewrite_state_l'' = startingState start_equiv_tracker rewrite_state_l'
      rewrite_state_r'' = startingState start_equiv_tracker rewrite_state_r'
  S.SomeSolver solver <- initSolver config
  putStrLn $ "***\n" ++ (show $ ru_name rule) ++ "\n***"
  putStrLn $ printHaskellDirty e_l'
  putStrLn $ printHaskellDirty e_r'
  -- TODO prepareState putting in wrong place?
  -- TODO put REC ticks in the starting expression?
  putStrLn $ printHaskellDirty $ exprExtract $ latest rewrite_state_l''
  putStrLn $ printHaskellDirty $ exprExtract $ latest rewrite_state_r''
  -- TODO this may not be sound anymore with Nothing
  (res, w) <- W.runWriterT $ verifyLoop solver ns
             [(rewrite_state_l'', rewrite_state_r'')]
             [(rewrite_state_l'', rewrite_state_r'')]
             bindings'' config "" 0 10
  -- UNSAT for good, SAT for bad
  -- TODO how to display?
  putStrLn "--- SUMMARY ---"
  let pg = mkPrettyGuide w
  mapM (putStrLn . (summarize pg)) w
  putStrLn "--- END OF SUMMARY ---"
  return res

-- inner scrutinees on the left side
-- ultimately for a substitution that happens on the right
{-
moreRestrictiveIndLeft :: S.Solver solver =>
                          solver ->
                          HS.HashSet Name ->
                          [(StateET, StateET)] ->
                          (StateET, StateET) ->
                          W.WriterT [Marker] IO (Maybe (PrevMatch EquivTracker))
moreRestrictiveIndLeft solver ns prev (s1, s2) =
  let prev1 = map (\(p1, p2) -> (p1, innerScrutineeStates p1, p2)) prev
      prev2 = [(p1', p2, p1) | (p1, p1l, p2) <- prev1, p1' <- p1l]
  in moreRestrictivePairAux solver ns prev2 (s1, s2)
-}
