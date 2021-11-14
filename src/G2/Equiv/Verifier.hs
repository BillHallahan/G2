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

import qualified Data.HashMap.Lazy as HM
import Data.Monoid (Any (..))

import Debug.Trace

import G2.Execution.NormalForms
import qualified G2.Language.Stack as Stck
import Control.Monad

import Data.Time

import G2.Execution.Reducer
import G2.Lib.Printers

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
data StateH = StateH {
    latest :: StateET
  , history :: [StateET]
  , inductions :: [IndMarker]
  , discharge :: Maybe StateET
}

-- remember this is for only one side
data IndMarker = IndMarker {
    past_state :: StateET
  , present_state :: StateET
  , result_state :: StateET
}

-- TODO this should be the output from tryDischarge
-- unfinished is what tryDischarge gave as output before
-- finished is the proof obligations that were just discharged
data DischargeResult = DischargeResult {
    unfinished :: [(StateH, StateH)]
  , finished :: [(StateH, StateH)]
  , bad_states :: Maybe [(StateET, StateET)]
}

exprReadyForSolver :: ExprEnv -> Expr -> Bool
exprReadyForSolver h (Tick _ e) = exprReadyForSolver h e
exprReadyForSolver h (Var i) = E.isSymbolic (idName i) h && T.isPrimType (typeOf i)
exprReadyForSolver h (App f a) = exprReadyForSolver h f && exprReadyForSolver h a
exprReadyForSolver _ (Prim _ _) = True
exprReadyForSolver _ (Lit _) = True
exprReadyForSolver _ _ = False

statePairReadyForSolver :: (State t, State t) -> Bool
statePairReadyForSolver (s1, s2) =
  let h1 = expr_env s1
      h2 = expr_env s2
      CurrExpr _ e1 = curr_expr s1
      CurrExpr _ e2 = curr_expr s2
  in
  exprReadyForSolver h1 e1 && exprReadyForSolver h2 e2

logStatesFolder :: String -> Maybe String -> LogMode
logStatesFolder _ Nothing = NoLog
logStatesFolder pre (Just fr) = Log Pretty $ fr ++ "/" ++ pre

logStatesET :: String -> Maybe String -> Maybe String
logStatesET _ Nothing = Nothing
logStatesET pre (Just fr) = Just $ fr ++ "/" ++ pre

-- TODO keep track of the prefixes for debugging
runSymExec :: Config ->
              Maybe String ->
              StateET ->
              StateET ->
              CM.StateT (Bindings, Int) IO [(StateET, StateET)]
runSymExec config folder_root s1 s2 = do
  CM.liftIO $ putStrLn "runSymExec"
  ct1 <- CM.liftIO $ getCurrentTime
  (bindings, k) <- CM.get
  let config' = config { logStates = logStatesFolder ("a" ++ show k) folder_root }
      t1 = (track s1) { folder_name = logStatesET ("a" ++ show k) folder_root }
  CM.liftIO $ putStrLn $ (show $ folder_name $ track s1) ++ " becomes " ++ (show $ folder_name t1)
  (er1, bindings') <- CM.lift $ runG2ForRewriteV (s1 { track = t1 }) config' bindings
  CM.put (bindings', k + 1)
  let final_s1 = map final_state er1
  pairs <- mapM (\s1_ -> do
                    (b_, k_) <- CM.get
                    let s2_ = transferStateInfo s1_ s2
                    ct2 <- CM.liftIO $ getCurrentTime
                    let config'' = config { logStates = logStatesFolder ("b" ++ show k_) folder_root }
                        t2 = (track s2_) { folder_name = logStatesET ("b" ++ show k_) folder_root }
                    CM.liftIO $ putStrLn $ (show $ folder_name $ track s2_) ++ " becomes " ++ (show $ folder_name t2)
                    (er2, b_') <- CM.lift $ runG2ForRewriteV (s2_ { track = t2 }) config'' b_
                    CM.put (b_', k_ + 1)
                    return $ map (\er2_ -> 
                                    let
                                        s2_' = final_state er2_
                                        s1_' = transferStateInfo s2_' s1_
                                    in
                                    (prepareState s1_', prepareState s2_')
                                 ) er2) final_s1
  return $ concat pairs

-- After s1 has had its expr_env, path constraints, and tracker updated,
-- transfer these updates to s2.
transferStateInfo :: StateET -> StateET -> StateET
transferStateInfo s1 s2 =
    let
        n_eenv = E.union (expr_env s1) (expr_env s2)
    in
    s2 { expr_env = n_eenv
       , path_conds = foldr P.insert (path_conds s1) (P.toList (path_conds s2))
       , symbolic_ids = map (\(Var i) -> i) . E.elems $ E.filterToSymbolic n_eenv
       , track = (track s1) { folder_name = folder_name $ track s2 } }

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

-- do not allow wrapping for symbolic variables
recWrap :: ExprEnv -> Name -> Expr -> Expr
recWrap h n e =
  if E.isSymbolic n h
  then e
  else ((wrcHelper n) . (wrapRecursiveCall n)) (wrapRecursiveCall n e)

-- Creating a new expression environment lets us use the existing reachability
-- functions.
-- TODO does the expr env really need to keep track of Lets above this?
-- look inside the bindings and inside the body for recursion
-- TODO I should merge this process with the other wrapping?
-- TODO do I need an extra process for some other recursive structure?
-- TODO is this not tagging "let w = w in w" with a REC tick?
-- other possibility:  no case, no full app, so no termination condition
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
wrapIfCorecursive :: G.CallGraph -> ExprEnv -> Name -> Name -> Expr -> Expr
wrapIfCorecursive cg h n m e =
  let n_list = G.reachable n cg
      m_list = G.reachable m cg
  in
  if (n `elem` m_list) && (m `elem` n_list)
  then recWrap h m e
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

-- TODO also needs to go underneath Cases
tickWrap :: Expr -> Expr
tickWrap (Case e i a) = Case (tickWrap e) i a
tickWrap (App e1 e2) = App (tickWrap e1) e2
tickWrap (Tick nl e) = Tick nl (tickWrap e)
tickWrap e = Tick (NamedLoc loc_name) e

exprWrap :: Stck.Stack Frame -> Expr -> Expr
exprWrap sk e = stackWrap sk $ tickWrap e

-- A Var counts as being in EVF if it's symbolic or if it's unmapped.
isSWHNF :: State t -> Bool
isSWHNF (State { expr_env = h, curr_expr = CurrExpr _ e }) =
  let e' = stripTicks e
  in case e' of
    Var _ -> isPrimType (typeOf e') && isExprValueForm h e'
    _ -> isExprValueForm h e'

-- The conditions for expr-value form do not align exactly with SWHNF.
-- A symbolic variable is in SWHNF only if it is of primitive type.
eitherSWHNF :: (State t, State t) -> Bool
eitherSWHNF (s1, s2) =
  isSWHNF s1 || isSWHNF s2

prepareState :: StateET -> StateET
prepareState s =
  let e = exprExtract s
  in s {
    curr_expr = CurrExpr Evaluate $ exprWrap (exec_stack s) $ e
  , num_steps = 0
  , rules = []
  , exec_stack = Stck.empty
  }

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

prevFull :: (StateH, StateH) -> [(StateET, StateET)]
prevFull (sh1, sh2) = [(p1, p2) | p1 <- history sh1, p2 <- history sh2]

prevFiltered :: (StateH, StateH) -> [(StateET, StateET)]
prevFiltered = (filter (not . eitherSWHNF)) . prevFull

verifyLoop :: S.Solver solver =>
              solver ->
              HS.HashSet Name ->
              [(StateH, StateH)] ->
              [(StateH, StateH)] ->
              Bindings ->
              Config ->
              Maybe String ->
              Int ->
              IO (S.Result () ())
verifyLoop solver ns states prev b config folder_root k | not (null states) = do
  let current_states = map getLatest states
  (paired_states, (b', k')) <- CM.runStateT (mapM (uncurry (runSymExec config folder_root)) current_states) (b, k)
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
  putStrLn "<Loop Iteration>"
  -- for every internal list, map with its corresponding original state
  let app_pair (sh1, sh2) (s1, s2) = (appendH sh1 s1, appendH sh2 s2)
      map_fns = map app_pair states
      updated_hists = map (uncurry map) (zip map_fns paired_states)
  putStrLn $ show $ length $ concat updated_hists
  proof_list <- mapM vl $ concat updated_hists
  let new_obligations = concat [l | Just l <- proof_list]
      prev' = new_obligations ++ prev
  putStrLn $ show $ length new_obligations
  if all isJust proof_list then
    verifyLoop solver ns new_obligations prev' b'' config folder_root k'
  else
    return $ S.SAT ()
  | otherwise = do
    return $ S.UNSAT ()

exprExtract :: State t -> Expr
exprExtract (State { curr_expr = CurrExpr _ e }) = e

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

-- Checks the same conditions, but takes a state pair as input instead.
statePairInduction :: (State t, State t) -> Bool
statePairInduction (s1, s2) =
  (caseRecursion $ exprExtract s1) && (caseRecursion $ exprExtract s2)

concretize :: HM.HashMap Id Expr -> Expr -> Expr
concretize hm e =
  HM.foldrWithKey (\i -> replaceVar (idName i)) e hm

-- Copies bindings from the first expression environment into the second.
-- This inserts symbolic variables twice over, once along with all of the other
-- variables and then once on their own specifically marked as symbolic, but
-- only the second insertion should matter.
concretizeEnv :: ExprEnv -> ExprEnv -> ExprEnv
concretizeEnv h_new h_old =
  let ins_sym n = case h_new E.! n of
                    Var i -> E.insertSymbolic n i
                    _ -> error ("unmapped symbolic variable " ++ show n)
      all_bindings = map (\n -> (n, h_new E.! n)) $ E.keys h_new
      all_sym_names = filter (\n -> E.isSymbolic n h_new) $ E.keys h_new
  in
  foldr ins_sym (foldr (uncurry E.insert) h_old all_bindings) all_sym_names

concretizeStatePair :: (ExprEnv, ExprEnv) ->
                       HM.HashMap Id Expr ->
                       (State t, State t) ->
                       (State t, State t)
concretizeStatePair (h_new1, h_new2) hm (s1, s2) =
  let e1 = concretize hm $ exprExtract s1
      e2 = concretize hm $ exprExtract s2
      h1 = concretizeEnv h_new1 $ expr_env s1
      h2 = concretizeEnv h_new2 $ expr_env s2
  in
  ( s1 { curr_expr = CurrExpr Evaluate e1, expr_env = h1 }
  , s2 { curr_expr = CurrExpr Evaluate e2, expr_env = h2 } )

-- assumes that the initial input is from an induction-ready state
inductionExtract :: Expr -> Expr
inductionExtract (Case e _ _) =
  case e of
    Case _ _ _ -> inductionExtract e
    _ -> e
inductionExtract _ = error "Improper Format"

inductionState :: State t -> State t
inductionState s =
  s { curr_expr = CurrExpr Evaluate $ inductionExtract $ exprExtract s }

-- TODO keep going recursively though more nested Cases
getAlts :: State t -> [Alt]
getAlts s@(State { curr_expr = CurrExpr _ e }) =
  case e of
    Case e' _ a -> case e' of
      Case _ _ _ -> getAlts $ s { curr_expr = CurrExpr Evaluate e' }
      _ -> a
    _ -> error "Improper Format"

-- TODO can't just replace the first case I see
-- need to keep going down until I reach something that isn't a Case
-- didn't fix forceIdempotent, though
-- TODO the trace here is the last thing that gets printed before freeze
-- TODO is this messing with the EquivTracker somehow?
-- TODO removed error, but there's a soundness problem
-- I get UNSAT for forceIdempotent
newScrutinee :: Id -> Expr -> Expr
newScrutinee i (Case e i' a) = Case (newScrutinee i e) i' a
newScrutinee i (Tick nl e) = Tick nl $ newScrutinee i e
newScrutinee i _ = Var i

-- the first expression becomes the new scrutinee of the second
substScrutinee :: Expr -> Expr -> Expr
substScrutinee e (Case e' i a) = Case (substScrutinee e e') i a
substScrutinee e (Tick nl e') = Tick nl $ substScrutinee e e'
substScrutinee e _ = e

-- TODO new induction scheme
removeMatchingCases :: Expr -> Expr -> Expr
removeMatchingCases (Tick _ e1) e2 = removeMatchingCases e1 e2
removeMatchingCases e1 (Tick _ e2) = removeMatchingCases e1 e2
removeMatchingCases (Case e1 i1 a1) (Case e2 i2 a2) =
  if a1 == a2 then removeMatchingCases e1 e2 else e2
removeMatchingCases _ e2 = e2

rmcHelper :: Expr -> State t -> State t
rmcHelper e1 s@(State { curr_expr = CurrExpr _ e2 }) =
  s { curr_expr = CurrExpr Evaluate (removeMatchingCases e1 e2) }

-- TODO new version gets all of the layers, not just the innermost
innerScrutinees :: Expr -> [Expr]
innerScrutinees (Tick _ e) = innerScrutinees e
innerScrutinees e@(Case e' _ _) = e:(innerScrutinees e')
innerScrutinees e = [e]

replaceScrutinee :: Expr -> Expr -> Expr -> Expr
replaceScrutinee e1 e2 e | e1 == e = e2
replaceScrutinee e1 e2 (Case e i a) = Case (replaceScrutinee e1 e2 e) i a
replaceScrutinee _ _ e = e

{-
How to handle the extra evaluation of past scrutinees?
Just record more stuff beforehand?
Every time I have a Case statement beforehand, I can precompute
what the steps would be for the scrutinee
Eventually it'll reach SWHNF or a recursion tick
Either that or pause evaluation more often?
-}

-- TODO new rule:  removal of singleton Case statements
-- convert them into Let statements
-- TODO if there's only one constructor, that should count too
-- likewise, if there's only one literal value, that should work
-- that's a really uncommon case, though
-- TODO make it recursive?
isSingleton :: Expr -> Bool
isSingleton (Case _ _ [Alt Default _]) = True
isSingleton (Case e _ _) = isSingleton e
isSingleton (Tick _ e) = isSingleton e
--isSingleton (Case e _ [Alt (DataAlt _ _) _]) = error "TODO"
isSingleton _ = False

-- TODO not looping in here
elimSingleton :: Expr -> Expr
elimSingleton (Tick nl e) = Tick nl (elimSingleton e)
elimSingleton (Case e i [Alt Default e']) = Let [(i, e)] e'
elimSingleton (Case e i a) = Case (elimSingleton e) i a
elimSingleton _ = error "Improper Format"

elimSingletonPair :: (StateET, StateET) -> (StateET, StateET)
elimSingletonPair (s1, s2) =
  let e1 = exprExtract s1
      e1' = elimSingleton e1
      s1' = s1 { curr_expr = CurrExpr Evaluate e1' }
      e2 = exprExtract s2
      e2' = elimSingleton e2
      s2' = s2 { curr_expr = CurrExpr Evaluate e2' }
      s1_ = if isSingleton e1 then s1' else s1
      s2_ = if isSingleton e2 then s2' else s2
  in (s1_, s2_)

notM :: IO Bool -> IO Bool
notM b = do
  b' <- b
  return (not b')

andM :: IO Bool -> IO Bool -> IO Bool
andM b1 b2 = do
  b1' <- b1
  b2' <- b2
  return (b1' && b2')

isNothingM :: IO (Maybe t) -> IO Bool
isNothingM m = do
  m' <- m
  return $ not $ isJust m'

-- TODO debugging function
exprHistory :: StateH -> StateH -> [(Expr, Expr)]
exprHistory sh1 sh2 =
  let hist1 = map exprExtract $ (latest sh1):(history sh1)
      hist2 = map exprExtract $ (latest sh2):(history sh2)
  in reverse $ zip hist1 hist2

stateHistory :: StateH -> StateH -> [(StateET, StateET)]
stateHistory sh1 sh2 =
  let hist1 = (latest sh1):(history sh1)
      hist2 = (latest sh2):(history sh2)
  in reverse $ zip hist1 hist2

exprTrace :: StateH -> StateH -> [String]
exprTrace sh1 sh2 =
  let s_hist = stateHistory sh1 sh2
      s_pair (s1, s2) = [
          printHaskell s1 (exprExtract s1)
        , printHaskell s2 (exprExtract s2)
        , show (symbolic_ids s1)
        , show (symbolic_ids s2)
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
addInduction :: StateET -> StateH -> StateH
addInduction s sh =
  let im = IndMarker s s (latest sh)
  in sh { inductions = im:(inductions sh) }

-- TODO a better setup would also indicate which side was used for induction
-- TODO just return (sh1, sh2) in failure event?
-- TODO I can add induction markers here; preserve the old states
-- q1 and q2 were the states used for the induction
-- TODO more reworking would be necessary to get the actual past states used
makeIndStateH :: (StateH, StateH) ->
                 ((StateET, StateET), (Int, StateET, StateET)) ->
                 (StateH, StateH)
makeIndStateH (sh1, sh2) ((q1, q2), (n, s1, s2)) | n >= 0 =
  let hist1 = drop n $ history sh1
      hist2 = drop n $ history sh2
      sh1' = sh1 { history = hist1, latest = s1 }
      sh2' = sh2 { history = hist2, latest = s2 }
      im1 = IndMarker q2 q1 s1
      im2 = IndMarker q1 q2 s2
  in (sh1', sh2')
  | otherwise = (sh1 { latest = s1 }, sh2 { latest = s2 })

-- this covers discharging of equivalent present states
tryCoinduction :: S.Solver solver =>
                  solver ->
                  HS.HashSet Name ->
                  [(StateET, StateET)] ->
                  (StateET, StateET) ->
                  IO (Maybe (PrevMatch EquivTracker))
tryCoinduction solver ns prev (s1, s2) = do
  res1 <- moreRestrictiveEquiv solver ns s1 s2
  res2 <- moreRestrictivePair solver ns prev (s1, s2)
  case res1 of
    Just _ -> trace ("EQUIVALENT " ++ show (length prev)) $ return res1
    _ -> trace ("DISCHARGE " ++ show (length prev)) $ return res2

-- TODO printing
-- TODO was the type signature wrong before?
-- TODO prev not used anymore
tryDischarge :: S.Solver solver =>
                solver ->
                HS.HashSet Name ->
                Name ->
                StateH ->
                StateH ->
                [(StateET, StateET)] ->
                IO DischargeResult
tryDischarge solver ns fresh_name sh1 sh2 prev =
  let s1 = latest sh1
      s2 = latest sh2
  in
  case getObligations ns s1 s2 of
    Nothing -> do
      -- obligation generation failed, so the expressions must not be equivalent
      putStrLn "N!"
      putStrLn $ show $ exprExtract s1
      putStrLn $ show $ exprExtract s2
      mapM putStrLn $ exprTrace sh1 sh2
      -- TODO what to return here?
      -- all left unfinished, nothing resolved
      -- bad_states are the ones right here
      return $ DischargeResult [] [] (Just [(s1, s2)])
    Just obs -> do
      putStrLn $ "J! " ++ (show $ folder_name $ track s1) ++ " " ++ (show $ folder_name $ track s2)
      putStrLn $ printHaskell s1 $ exprExtract s1
      putStrLn $ printHaskell s2 $ exprExtract s2
      --putStrLn $ show $ exprExtract s1
      --putStrLn $ show $ exprExtract s2

      -- TODO new prev'
      let -- prev' = concat $ map prevFiltered prev
          prev' = prevFiltered (sh1, sh2)
          (obs_i, obs_c) = partition canUseInduction obs
          states_c = map (stateWrap s1 s2) obs_c
      -- TODO do I need more adjustments than what I have here?
      discharges <- mapM (tryCoinduction solver ns prev') states_c
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
      -- TODO need a way to get the prev pair used for induction
      states_i' <- mapM (inductionFull solver ns fresh_name (sh1, sh2)) states_i
      --states_i' <- filterM (notM . (induction solver ns fresh_name prev')) states_i

      -- TODO unnecessary to pass the induction states through this?
      let (ready, not_ready) = partition statePairReadyForSolver states_c'
          --not_ready' = not_ready ++ states_i'
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
      res <- checkObligations solver s1 s2 ready_exprs
      case res of
        S.UNSAT () -> putStrLn "V?"
        _ -> putStrLn "X?"
      case res of
        -- TODO discharged exprs should come from filter and solver
        S.UNSAT () -> return $ DischargeResult not_ready_h (matches ++ ready_solved) Nothing
        _ -> return $ DischargeResult not_ready_h (matches ++ ready_solved) (Just ready)

-- TODO (11/10) need to move total-finite info for induction
-- info from first tracker gets added to the second
-- TODO left takes precedence in union?
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
  -- TODO make an arbitrary choice about which working combination to return
  -- need to make a substitution for it
  -- going with left substitution for now
  case working_info of
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
           --in trace ("YES I! " ++ show (printHaskell q1 $ exprExtract q1, printHaskell q2 $ exprExtract q2) ++ " :: " ++ show (printHaskell p1 $ exprExtract p1, printHaskell p2 $ exprExtract p2) ++ " :: " ++ show (printHaskell q1 $ sc1, printHaskell q2 $ sc2) ++ " :: " ++ show (printHaskell s1 $ exprExtract s1, printHaskell s2 $ exprExtract s2)) $ return (True, q1{ curr_expr = CurrExpr Evaluate e1_new }, q2)
           --in trace ("YES I! " ++ show (track q1', track q2) ++ " :: " ++ show (track p1, track p2) ++ " :: " ++ show (sc1, sc2) ++ " :: " ++ show (track s1, track s2)) $ return (True, q1'{ curr_expr = CurrExpr Evaluate e1_new }, q2')
           in trace (show (sc1, e2_old', exprExtract s1)) $
              trace ("YL " ++ show (length working_info)) $
              trace ("HM " ++ show hm_list) $
              trace (show (map (\(r1, r2) -> (folder_name $ track r1, folder_name $ track r2)) prev)) $
              trace ("YES IL! " ++ show (map (folder_name . track) [s1, s2, q1, q2, p1, p2])) $
              return (True, s1 { curr_expr = CurrExpr Evaluate e1_new, expr_env = h1_new, symbolic_ids = si1_new }, s2)
           --in trace ("YES I! " ++ show (map (folder_name . track) [s1, s2, q1, q2, p1, p2])) $ return (False, s1, s2)
           --in trace ("YES I! " ++ show (length prev)) $ return (True, q1, q2'{ curr_expr = CurrExpr Evaluate e2_new })

-- TODO reduce duplicated code?  Also make sure it's correct
-- substitution happens on the right here
inductionR :: S.Solver solver =>
              solver ->
              HS.HashSet Name ->
              [(StateET, StateET)] ->
              (StateET, StateET) ->
              IO (Bool, StateET, StateET)
inductionR solver ns prev (s1, s2) = do
  let scr1 = innerScrutinees $ exprExtract s1
      scr2 = innerScrutinees $ exprExtract s2
      scr_pairs = [(sc1, sc2) | sc1 <- scr1, sc2 <- scr2]
      scr_states = [(s1 { curr_expr = CurrExpr Evaluate sc1 }, s2 { curr_expr = CurrExpr Evaluate sc2 }) | (sc1, sc2) <- scr_pairs]
  mr_pairs <- mapM (moreRestrictiveIndLeft solver ns prev) scr_states
  let mr_zipped = zip scr_pairs mr_pairs
      working_info = [(sc1, sc2, pm) | ((sc1, sc2), Just pm) <- mr_zipped]
  case working_info of
    [] -> return (False, s1, s2)
    h:_ -> let (sc1, sc2, PrevMatch (q1, q2) (p1, p2) (mapping, _) pc1) = h
               e1_old = exprExtract pc1
               hm_list = HM.toList mapping
               e1_old' = foldr (\(i, e) acc -> replaceASTs (Var i) e acc) e1_old hm_list
               e2_new = replaceScrutinee sc2 e1_old' $ exprExtract s2
               -- TODO use s1 or pc1 here?
               -- the s1 version gets an error that pc1 doesn't
               h2_new = E.union (expr_env s2) (expr_env pc1)
               si2_new = map (\(Var i) -> i) . E.elems $ E.filterToSymbolic h2_new
           in trace (show (sc2, e1_old', exprExtract s2)) $
              trace ("YR " ++ show (length working_info)) $
              trace ("HM " ++ show hm_list) $
              trace (show (map (\(r1, r2) -> (folder_name $ track r1, folder_name $ track r2)) prev)) $
              trace ("YES IR! " ++ show (map (folder_name . track) [s1, s2, q1, q2, p1, p2])) $
              return (True, s1, s2 { curr_expr = CurrExpr Evaluate e2_new, expr_env = h2_new, symbolic_ids = si2_new })

-- precedence goes to left-side substitution
-- right-side substitution only happens if left-side fails
induction :: S.Solver solver =>
             solver ->
             HS.HashSet Name ->
             [(StateET, StateET)] ->
             (StateET, StateET) ->
             IO (Bool, StateET, StateET)
induction solver ns prev (s1, s2) = do
  (bl, s1l, s2l) <- inductionL solver ns prev (s1, s2)
  (br, s1r, s2r) <- inductionR solver ns prev (s1, s2)
  if bl then return (bl, s1l, s2l)
  else return (br, s1r, s2r)

backtrackOne :: StateH -> StateH
backtrackOne sh =
  case history sh of
    [] -> error "No Backtrack Possible"
    h:t -> sh {
        latest = h
      , history = t
      }

-- left side stays constant
inductionFoldL :: S.Solver solver =>
                  solver ->
                  HS.HashSet Name ->
                  Name ->
                  (StateH, StateH) ->
                  (StateET, StateET) ->
                  IO (Int, StateET, StateET)
inductionFoldL solver ns fresh_name (sh1, sh2) (s1, s2) = do
  let prev = prevFiltered (sh1, sh2)
  (b, s1', s2') <- induction solver ns prev (s1, s2)
  if b then do
    (b', s1'', s2'') <- generalize solver ns fresh_name (s1', s2')
    if b' then trace ("EL " ++ show (map (folder_name . track) [s1, s2, s1', s2'])) $ return (length $ history sh2, s1', s2')
    else case history sh2 of
      [] -> return (-1, s1, s2)
      p2:_ -> inductionFoldL solver ns fresh_name (sh1, backtrackOne sh2) (s1, p2)
  else case history sh2 of
    [] -> return (-1, s1, s2)
    p2:_ -> inductionFoldL solver ns fresh_name (sh1, backtrackOne sh2) (s1, p2)

-- TODO this returns the length of prev at the time of return
inductionFoldR :: S.Solver solver =>
                  solver ->
                  HS.HashSet Name ->
                  Name ->
                  (StateH, StateH) ->
                  (StateET, StateET) ->
                  IO (Int, StateET, StateET)
inductionFoldR solver ns fresh_name (sh1, sh2) (s1, s2) = do
  let prev = prevFiltered (sh1, sh2)
  (b, s1', s2') <- induction solver ns prev (s1, s2)
  if b then do
    (b', s1'', s2'') <- generalize solver ns fresh_name (s1', s2')
    if b' then trace ("ER " ++ show (map (folder_name . track) [s1, s2, s1', s2'])) $ return (length $ history sh1, s1', s2')
    else case history sh1 of
      [] -> return (-1, s1, s2)
      p1:_ -> inductionFoldR solver ns fresh_name (backtrackOne sh1, sh2) (p1, s2)
  else case history sh1 of
    [] -> return (-1, s1, s2)
    p1:_ -> inductionFoldR solver ns fresh_name (backtrackOne sh1, sh2) (p1, s2)

-- TODO somewhat crude solution:  record how "far back" it needed to go
-- negative one means that it failed
-- TODO only use histories from sh1 and sh2
-- TODO no induction without substitution now
inductionFold :: S.Solver solver =>
                 solver ->
                 HS.HashSet Name ->
                 Name ->
                 (StateH, StateH) ->
                 (StateET, StateET) ->
                 IO (Int, StateET, StateET)
inductionFold solver ns fresh_name sh_pair@(sh1, sh2) (s1, s2) = do
  (nl, s1l, s2l) <- inductionFoldL solver ns fresh_name sh_pair (s1, s2)
  -- TODO this could cause excessive removals
  let min_length = min (length $ history sh1) (length $ history sh2)
  if nl >= 0 then trace ("IL " ++ show (map (folder_name . track) [s1, s2, s1l, s2l])) $ return (min_length - nl, s1l, s2l)
  else do
    (nr, s1r, s2r) <- inductionFoldR solver ns fresh_name sh_pair (s1, s2)
    if nr >= 0 then trace ("IR " ++ show (map (folder_name . track) [s1, s2, s1r, s2r])) $ return (min_length - nr, s1r, s2r)
    else return (-1, s1, s2)

generalizeAux :: S.Solver solver =>
                 solver ->
                 HS.HashSet Name ->
                 [StateET] ->
                 StateET ->
                 IO (Maybe (PrevMatch EquivTracker))
generalizeAux solver ns s1_list s2 = do
  --putStrLn "GAux"
  let check_equiv s1_ = moreRestrictiveEquiv solver ns s1_ s2
  res <- mapM check_equiv s1_list
  let res' = filter isJust res
  case res' of
    [] -> return Nothing
    h:_ -> return h

-- TODO replace the largest sub-expression possible with a fresh symbolic var
-- TODO this is never finishing, seemingly
generalize :: S.Solver solver =>
              solver ->
              HS.HashSet Name ->
              Name ->
              (StateET, StateET) ->
              IO (Bool, StateET, StateET)
generalize solver ns fresh_name (s1, s2) = do
  putStrLn $ "Starting G " ++ show fresh_name
  -- expressions are ordered from outer to inner
  -- the largest ones are on the outside
  -- take the earliest array entry that works
  -- for anything on one side, there can only be one match on the other side
  let e1 = exprExtract s1
      scr1 = innerScrutinees e1
      scr_states1 = map (\e -> s1 { curr_expr = CurrExpr Evaluate e }) scr1
      e2 = exprExtract s2
      scr2 = innerScrutinees e2
      scr_states2 = map (\e -> s2 { curr_expr = CurrExpr Evaluate e }) scr2
  res <- mapM (generalizeAux solver ns scr_states1) scr_states2
  putStrLn "Generalized"
  -- TODO expression environment adjustment?  Only for the fresh var
  -- TODO also may want to adjust the equivalence tracker
  let res' = filter isJust res
  case res' of
    (Just pm):_ -> let (s1', s2') = present pm
                       fresh_id = Id fresh_name (typeOf e1')
                       fresh_var = Var fresh_id
                       e1' = exprExtract s1'
                       e1'' = replaceScrutinee e1' fresh_var e1
                       h1 = expr_env s1
                       h1' = E.insertSymbolic fresh_name fresh_id h1
                       s1'' = s1 {
                         curr_expr = CurrExpr Evaluate e1''
                       , expr_env = h1'
                       , symbolic_ids = fresh_id:(symbolic_ids s1)
                       }
                       e2' = exprExtract s2'
                       e2'' = replaceScrutinee e2' fresh_var e2
                       h2 = expr_env s2
                       h2' = E.insertSymbolic fresh_name fresh_id h2
                       s2'' = s2 {
                         curr_expr = CurrExpr Evaluate e2''
                       , expr_env = h2'
                       , symbolic_ids = fresh_id:(symbolic_ids s2)
                       }
                   in trace ("G! " ++ show (e1'', e2'')) $
                      trace (show fresh_var) $
                      return (True, s1'', s2'')
    _ -> trace ("No G? " ++ show fresh_name) $
         -- TODO allowing failures for now
         return (False, s1, s2)

-- TODO does this throw off history logging?  I don't think so
-- TODO might not matter with s1 and s2 naming
inductionFull :: S.Solver solver =>
                 solver ->
                 HS.HashSet Name ->
                 Name ->
                 (StateH, StateH) ->
                 (StateET, StateET) ->
                 IO (Int, StateET, StateET)
inductionFull solver ns fresh_name sh_pair s_pair@(s1, s2) = do
  (n, s1', s2') <- inductionFold solver ns fresh_name sh_pair s_pair
  if n < 0 then trace ("NO INDUCTION " ++ show n) return (n, s1, s2)
  else return (n, s1', s2')
  {-
  else do
    (_, s1', s2') <- generalize solver ns fresh_name (s1, s2)
    return (n, s1', s2')
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
    Just obs -> Just $
                map (\(Ob e1 e2) -> Ob (addStackTickIfNeeded e1) (addStackTickIfNeeded e2)) $
                HS.toList obs

addStackTickIfNeeded :: Expr -> Expr
addStackTickIfNeeded e =
    if hasStackTick e then e else tickWrap e

hasStackTick :: Expr -> Bool
hasStackTick = getAny . evalASTs (\e -> case e of
                                          Tick (NamedLoc l) _
                                            | l == loc_name -> Any True
                                          _ -> Any False)

checkObligations :: S.Solver solver =>
                    solver ->
                    State t ->
                    State t ->
                    HS.HashSet (Expr, Expr) ->
                    IO (S.Result () ())
checkObligations solver s1 s2 obligation_set | not $ HS.null obligation_set =
    case obligationWrap $ modifyASTs stripTicks obligation_set of
        Nothing -> applySolver solver P.empty s1 s2
        Just allPO -> applySolver solver (P.insert allPO P.empty) s1 s2
  | otherwise = return $ S.UNSAT ()

stripTicks :: Expr -> Expr
stripTicks (Tick _ e) = e
stripTicks e = e

applySolver :: S.Solver solver =>
               solver ->
               PathConds ->
               State t ->
               State t ->
               IO (S.Result () ())
applySolver solver extraPC s1 s2 =
    let unionEnv = E.union (expr_env s1) (expr_env s2)
        rightPC = P.toList $ path_conds s2
        unionPC = foldr P.insert (path_conds s1) rightPC
        allPC = foldr P.insert unionPC (P.toList extraPC)
        -- TODO what if I use extraPC here instead of allPC?
        newState = s1 { expr_env = unionEnv, path_conds = extraPC }
    in S.check solver newState allPC

obligationWrap :: HS.HashSet (Expr, Expr) -> Maybe PathCond
obligationWrap obligations =
    let obligation_list = HS.toList obligations
        eq_list = map (\(e1, e2) -> App (App (Prim Eq TyUnknown) e1) e2) obligation_list
        conj = foldr1 (\o1 o2 -> App (App (Prim And TyUnknown) o1) o2) eq_list
    in
    if null eq_list
    then Nothing
    else Just $ ExtCond (App (Prim Not TyUnknown) conj) True

includedName :: [DT.Text] -> Name -> Bool
includedName texts (Name t _ _ _) = t `elem` texts

startingState :: EquivTracker -> State t -> StateH
startingState et s =
  let h = expr_env s
      -- Tick wrapping for recursive and corecursive functions
      wrap_cg = wrapAllRecursion (G.getCallGraph h) h
      h' = E.map (wrapLetRec h) $ E.mapWithKey wrap_cg h
      all_names = E.keys h
      s' = s {
      track = et
    , curr_expr = CurrExpr Evaluate $ foldr wrap_cg (tickWrap $ exprExtract s) all_names
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
      start_equiv_tracker = EquivTracker et m total_hs finite_hs Nothing
      -- the keys are the same between the old and new environments
      ns_l = HS.fromList $ E.keys $ expr_env rewrite_state_l
      ns_r = HS.fromList $ E.keys $ expr_env rewrite_state_r
      -- no need for two separate name sets
      ns = HS.union ns_l ns_r
      -- TODO wrap both sides with forcings for finite vars
      -- get the finite vars first
      -- TODO a little redundant with the earlier stuff
      finite_ids = filter ((includedName finite) . idName) (ru_bndrs rule)
      walkers = deepseq_walkers bindings''
      e_l = exprExtract rewrite_state_l
      e_l' = foldr (forceFinite walkers) e_l finite_ids
      -- TODO prepareState to avoid tick problem?
      rewrite_state_l' = rewrite_state_l { curr_expr = CurrExpr Evaluate e_l' }
      e_r = exprExtract rewrite_state_r
      e_r' = foldr (forceFinite walkers) e_r finite_ids
      rewrite_state_r' = rewrite_state_r { curr_expr = CurrExpr Evaluate e_r' }
      
      rewrite_state_l'' = startingState start_equiv_tracker rewrite_state_l'
      rewrite_state_r'' = startingState start_equiv_tracker rewrite_state_r'
  S.SomeSolver solver <- initSolver config
  putStrLn $ "***\n" ++ (show $ ru_name rule) ++ "\n***"
  putStrLn $ printHaskell rewrite_state_l' e_l'
  putStrLn $ printHaskell rewrite_state_r' e_r'
  -- TODO prepareState putting in wrong place?
  -- TODO put REC ticks in the starting expression?
  putStrLn $ printHaskell (latest rewrite_state_l'') $ exprExtract $ latest rewrite_state_l''
  putStrLn $ printHaskell (latest rewrite_state_r'') $ exprExtract $ latest rewrite_state_r''
  res <- verifyLoop solver ns
             [(rewrite_state_l'', rewrite_state_r'')]
             [(rewrite_state_l'', rewrite_state_r'')]
             bindings'' config (Just "testing") 0
  -- UNSAT for good, SAT for bad
  return res

-- s1 is the old state, s2 is the new state
-- If any recursively-defined functions or other expressions manage to slip
-- through the cracks with the other mechanisms in place for avoiding infinite
-- inlining loops, then we can handle them here by keeping track of all of the
-- variables that have been inlined previously.
-- Keeping track of inlinings by adding to ns only lets a variable be inlined
-- on one side.  We need to have two separate lists of variables that have been
-- inlined previously so that inlinings on one side do not block any inlinings
-- that need to happen on the other side.
-- Whenever a variable is inlined, we record the expression that was on the
-- opposite side at the time.  Under the original system, a variable could not
-- be inlined at all on one side in any sub-expressions that resulted from an
-- inlining of it, and that was too restrictive.  Under the current system,
-- repeated inlinings of a variable are allowed as long as the expression on
-- the opposite side is not the same as it was when a previous inlining of the
-- same variable happened.
-- TODO not looping in here
moreRestrictive :: State t ->
                   State t ->
                   HS.HashSet Name ->
                   (HM.HashMap Id Expr, HS.HashSet (Expr, Expr)) ->
                   [(Name, Expr)] -> -- ^ variables inlined previously on the LHS
                   [(Name, Expr)] -> -- ^ variables inlined previously on the RHS
                   Expr ->
                   Expr ->
                   Maybe (HM.HashMap Id Expr, HS.HashSet (Expr, Expr))
moreRestrictive s1@(State {expr_env = h1}) s2@(State {expr_env = h2}) ns hm n1 n2 e1 e2 =
  case (e1, e2) of
    -- ignore all Ticks
    (Tick _ e1', _) -> moreRestrictive s1 s2 ns hm n1 n2 e1' e2
    (_, Tick _ e2') -> moreRestrictive s1 s2 ns hm n1 n2 e1 e2'
    (Var i, _) | m <- idName i
               , not $ E.isSymbolic m h1
               , not $ HS.member m ns
               , not $ (m, e2) `elem` n1
               , Just e <- E.lookup m h1 ->
                 moreRestrictive s1 s2 ns hm ((m, e2):n1) n2 e e2
    (_, Var i) | m <- idName i
               , not $ E.isSymbolic m h2
               , not $ HS.member m ns
               , not $ (m, e1) `elem` n2
               , Just e <- E.lookup m h2 ->
                 moreRestrictive s1 s2 ns hm n1 ((m, e1):n2) e1 e
    (Var i1, Var i2) | HS.member (idName i1) ns
                     , idName i1 == idName i2 -> Just hm
                     | HS.member (idName i1) ns -> Nothing
                     | HS.member (idName i2) ns -> Nothing
    (Var i, _) | E.isSymbolic (idName i) h1
               , (hm', hs) <- hm
               , Nothing <- HM.lookup i hm' -> Just (HM.insert i (inlineEquiv [] h2 ns e2) hm', hs)
               | E.isSymbolic (idName i) h1
               , Just e <- HM.lookup i (fst hm)
               , e == inlineEquiv [] h2 ns e2 -> Just hm
               -- this last case means there's a mismatch
               | E.isSymbolic (idName i) h1 -> Nothing
               | not $ (idName i, e2) `elem` n1
               , not $ HS.member (idName i) ns -> error $ "unmapped variable " ++ (show i)
    (_, Var i) | E.isSymbolic (idName i) h2 -> Nothing -- sym replaces non-sym
               | not $ (idName i, e1) `elem` n2
               , not $ HS.member (idName i) ns -> error $ "unmapped variable " ++ (show i)
    (App f1 a1, App f2 a2) | Just hm_f <- moreRestrictive s1 s2 ns hm n1 n2 f1 f2
                           , Just hm_a <- moreRestrictive s1 s2 ns hm_f n1 n2 a1 a2 -> Just hm_a
    -- These two cases should come after the main App-App case.  If an
    -- expression pair fits both patterns, then discharging it in a way that
    -- does not add any extra proof obligations is preferable.
    (App _ _, _) | e1':_ <- unApp e1
                 , (Prim _ _) <- inlineTop [] h1 e1'
                 , T.isPrimType $ typeOf e1 ->
                                  let (hm', hs) = hm
                                  in Just (hm', HS.insert (inlineFull [] h1 e1, inlineFull [] h2 e2) hs)
    (_, App _ _) | e2':_ <- unApp e2
                 , (Prim _ _) <- inlineTop [] h1 e2'
                 , T.isPrimType $ typeOf e2 ->
                                  let (hm', hs) = hm
                                  in Just (hm', HS.insert (inlineFull [] h1 e1, inlineFull [] h2 e2) hs)
    -- We just compare the names of the DataCons, not the types of the DataCons.
    -- This is because (1) if two DataCons share the same name, they must share the
    -- same type, but (2) "the same type" may be represented in different syntactic
    -- ways, most significantly bound variable names may differ
    -- "forall a . a" is the same type as "forall b . b", but fails a syntactic check.
    (Data (DataCon d1 _), Data (DataCon d2 _))
                                  | d1 == d2 -> Just hm
                                  | otherwise -> Nothing
    -- We neglect to check type equality here for the same reason.
    (Prim p1 _, Prim p2 _) | p1 == p2 -> Just hm
                           | otherwise -> Nothing
    (Lit l1, Lit l2) | l1 == l2 -> Just hm
                     | otherwise -> Nothing
    (Lam lu1 i1 b1, Lam lu2 i2 b2)
                | lu1 == lu2
                , i1 == i2 ->
                  let ns' = HS.insert (idName i1) ns
                  -- no need to insert twice over because they're equal
                  in moreRestrictive s1 s2 ns' hm n1 n2 b1 b2
                | otherwise -> Nothing
    -- ignore types, like in exprPairing
    (Type _, Type _) -> Just hm
    -- new Let handling
    -- TODO does this not account for bindings properly?
    -- TODO only works properly if both binding lists are the same length
    -- I can just discard cases where they aren't for now
    (Let binds1 e1', Let binds2 e2') ->
                let pairs = (e1', e2'):(zip (map snd binds1) (map snd binds2))
                    ins (i_, e_) h_ = E.insert (idName i_) e_ h_
                    h1' = foldr ins h1 binds1
                    h2' = foldr ins h2 binds2
                    s1' = s1 { expr_env = h1' }
                    s2' = s2 { expr_env = h2' }
                    mf hm_ (e1_, e2_) = moreRestrictive s1' s2' ns hm_ n1 n2 e1_ e2_
                in
                if length binds1 == length binds2
                then foldM mf hm pairs
                else Nothing
    -- TODO if scrutinee is symbolic var, make Alt vars symbolic?
    -- TODO id equality never checked; does it matter?
    (Case e1' i1 a1, Case e2' i2 a2)
                | Just hm' <- moreRestrictive s1 s2 ns hm n1 n2 e1' e2' ->
                  -- add the matched-on exprs to the envs beforehand
                  let h1' = E.insert (idName i1) e1' h1
                      h2' = E.insert (idName i2) e2' h2
                      s1' = s1 { expr_env = h1' }
                      s2' = s2 { expr_env = h2' }
                      mf hm_ (e1_, e2_) = moreRestrictiveAlt s1' s2' ns hm_ n1 n2 e1_ e2_
                      l = zip a1 a2
                  in foldM mf hm' l
    _ -> Nothing

-- These helper functions have safeguards to avoid cyclic inlining.
inlineTop :: [Name] -> ExprEnv -> Expr -> Expr
inlineTop acc h v@(Var (Id n _))
    | n `elem` acc = v
    | E.isSymbolic n h = v
    | Just e <- E.lookup n h = inlineTop (n:acc) h e
inlineTop _ _ e = e

inlineFull :: [Name] -> ExprEnv -> Expr -> Expr
inlineFull acc h v@(Var (Id n _))
    | n `elem` acc = v
    | E.isSymbolic n h = v
    | Just e <- E.lookup n h = inlineFull (n:acc) h e
inlineFull acc h e = modifyChildren (inlineFull acc h) e

inlineEquiv :: [Name] -> ExprEnv -> HS.HashSet Name -> Expr -> Expr
inlineEquiv acc h ns v@(Var (Id n _))
    | n `elem` acc = v
    | E.isSymbolic n h = v
    | HS.member n ns = v
    | Just e <- E.lookup n h = inlineEquiv (n:acc) h ns e
inlineEquiv acc h ns e = modifyChildren (inlineEquiv acc h ns) e

-- check only the names for DataAlt
altEquiv :: AltMatch -> AltMatch -> Bool
altEquiv (DataAlt dc1 ids1) (DataAlt dc2 ids2) =
  let DataCon dn1 _ = dc1
      DataCon dn2 _ = dc2
      n1 = map idName ids1
      n2 = map idName ids2
  in
  dn1 == dn2 && n1 == n2
altEquiv (LitAlt l1) (LitAlt l2) = l1 == l2
altEquiv Default Default = True
altEquiv _ _ = False

-- ids are the same between both sides; no need to insert twice
moreRestrictiveAlt :: State t ->
                      State t ->
                      HS.HashSet Name ->
                      (HM.HashMap Id Expr, HS.HashSet (Expr, Expr)) ->
                      [(Name, Expr)] -> -- ^ variables inlined previously on the LHS
                      [(Name, Expr)] -> -- ^ variables inlined previously on the RHS
                      Alt ->
                      Alt ->
                      Maybe (HM.HashMap Id Expr, HS.HashSet (Expr, Expr))
moreRestrictiveAlt s1 s2 ns hm n1 n2 (Alt am1 e1) (Alt am2 e2) =
  if altEquiv am1 am2 then
  case am1 of
    DataAlt _ t1 -> let ns' = foldr HS.insert ns $ map (\(Id n _) -> n) t1
                    in moreRestrictive s1 s2 ns' hm n1 n2 e1 e2
    _ -> moreRestrictive s1 s2 ns hm n1 n2 e1 e2
  else Nothing

validMap :: State t -> State t -> HM.HashMap Id Expr -> Bool
validMap s1 s2 hm =
  let hm_list = HM.toList hm
      check (_, e) = (not $ isSWHNF $ s1 { curr_expr = CurrExpr Evaluate e })
                  || (not $ isSWHNF $ s2 { curr_expr = CurrExpr Evaluate e })
                  || isPrimType (typeOf e)
  in foldr (&&) True (map check hm_list)

restrictHelper :: State t ->
                  State t ->
                  HS.HashSet Name ->
                  Maybe (HM.HashMap Id Expr, HS.HashSet (Expr, Expr)) ->
                  Maybe (HM.HashMap Id Expr, HS.HashSet (Expr, Expr))
restrictHelper s1 s2 ns hm_hs = case restrictAux s1 s2 ns hm_hs of
  Nothing -> Nothing
  Just (hm, hs) -> if validMap s1 s2 hm then Just (hm, hs) else Nothing

restrictAux :: State t ->
               State t ->
               HS.HashSet Name ->
               Maybe (HM.HashMap Id Expr, HS.HashSet (Expr, Expr)) ->
               Maybe (HM.HashMap Id Expr, HS.HashSet (Expr, Expr))
restrictAux _ _ _ Nothing = Nothing
restrictAux s1 s2 ns (Just hm) =
  moreRestrictive s1 s2 ns hm [] [] (exprExtract s1) (exprExtract s2)

-- All the PathConds that this receives are generated by symbolic execution.
-- Consequently, non-primitive types are not an issue here.
extractCond :: PathCond -> Expr
extractCond (ExtCond e True) = e
extractCond (ExtCond e False) = App (Prim Not TyUnknown) e
extractCond (AltCond l e True) =
  App (App (Prim Eq TyUnknown) e) (Lit l)
extractCond (AltCond l e False) =
  App (App (Prim Neq TyUnknown) e) (Lit l)
extractCond _ = error "Not Supported"

-- s1 is old state, s2 is new state
-- only apply to old-new state pairs for which moreRestrictive works
moreRestrictivePC :: S.Solver solver =>
                     solver ->
                     State t ->
                     State t ->
                     HM.HashMap Id Expr ->
                     IO Bool
moreRestrictivePC solver s1 s2 hm = do
  let new_conds = map extractCond (P.toList $ path_conds s2)
      old_conds = map extractCond (P.toList $ path_conds s1)
      l = map (\(i, e) -> (Var i, e)) $ HM.toList hm
      -- this should only be used with primitive types
      -- no apparent problems come from using TyUnknown
      l' = map (\(e1, e2) ->
                  if (T.isPrimType $ typeOf e1) && (T.isPrimType $ typeOf e2)
                  then Just $ App (App (Prim Eq TyUnknown) e1) e2
                  else Nothing) l
      l'' = [c | Just c <- l']
      new_conds' = l'' ++ new_conds
      -- not safe to use unless the lists are non-empty
      conj_new = foldr1 (\o1 o2 -> App (App (Prim And TyUnknown) o1) o2) new_conds'
      conj_old = foldr1 (\o1 o2 -> App (App (Prim And TyUnknown) o1) o2) old_conds
      imp = App (App (Prim Implies TyUnknown) conj_new) conj_old
      neg_imp = ExtCond (App (Prim Not TyUnknown) imp) True
      neg_conj = ExtCond (App (Prim Not TyUnknown) conj_old) True
  res <- if null old_conds
         then return $ S.UNSAT ()
         else if null new_conds' -- old_conds not null
         -- TODO applySolver uses states' path constraints directly
         -- Are the conditions from this being satisfied trivially?
         then applySolver solver (P.insert neg_conj P.empty) s1 s2
         else applySolver solver (P.insert neg_imp P.empty) s1 s2
  case res of
    S.UNSAT () -> return True
    _ -> return False

rfs :: ExprEnv -> Expr -> Bool
rfs h e = (exprReadyForSolver h e) && (T.isPrimType $ typeOf e)

-- TODO container
data PrevMatch t = PrevMatch {
    present :: (State t, State t)
  , past :: (State t, State t)
  , conditions :: (HM.HashMap Id Expr, HS.HashSet (Expr, Expr))
  , container :: State t
}

-- extra filter on top of isJust for maybe_pairs
-- if restrictHelper end result is Just, try checking the corresponding PCs
-- for True output, there needs to be an entry for which that check succeeds
-- return the previous state pair that was used for the discharge
-- return Nothing if there was no discharge
-- if there are multiple, just return the first
-- TODO first pair is "current," second pair is the match from the past
-- TODO the third entry in a prev triple is the original for left or right
moreRestrictivePairAux :: S.Solver solver =>
                          solver ->
                          HS.HashSet Name ->
                          [(State t, State t, State t)] ->
                          (State t, State t) ->
                          IO (Maybe (PrevMatch t))
moreRestrictivePairAux solver ns prev (s1, s2) = do
  let mr (p1, p2, _) = restrictHelper p2 s2 ns $
                       restrictHelper p1 s1 ns (Just (HM.empty, HS.empty))
      getObs m = case m of
        Nothing -> HS.empty
        Just (_, hs) -> hs
      getMap m = case m of
        Nothing -> HM.empty
        Just (hm, _) -> hm
      maybe_pairs = map mr prev
      obs_sets = map getObs maybe_pairs
      h1 = expr_env s1
      h2 = expr_env s2
      obs_sets' = map (HS.filter (\(e1, e2) -> rfs h1 e1 && rfs h2 e2)) obs_sets
      no_loss = map (\(hs1, hs2) -> HS.size hs1 == HS.size hs2) (zip obs_sets obs_sets')
      mpc m = case m of
        (Just (hm, _), (s_old1, s_old2, _)) ->
          andM (moreRestrictivePC solver s_old1 s1 hm) (moreRestrictivePC solver s_old2 s2 hm)
        _ -> return False
      bools = map mpc (zip maybe_pairs prev)
  -- check obligations individually rather than as one big group
  res_list <- mapM (checkObligations solver s1 s2) obs_sets'
  bools' <- mapM id bools
  -- need res_list, no_loss, and bools all aligning at a point
  let all_three thr = case fst thr of
        ((S.UNSAT (), _), (True, True)) -> True
        _ -> False
  -- all four lists should be the same length
  case filter all_three $ zip (zip (zip res_list prev) $ zip no_loss bools') maybe_pairs of
    [] -> return Nothing
    (((_, (p1, p2, pc)), _), m):_ -> return $ Just $ PrevMatch (s1, s2) (p1, p2) (getMap m, getObs m) pc

-- the third entry in prev tuples is meaningless here
moreRestrictivePair :: S.Solver solver =>
                       solver ->
                       HS.HashSet Name ->
                       [(State t, State t)] ->
                       (State t, State t) ->
                       IO (Maybe (PrevMatch t))
moreRestrictivePair solver ns prev (s1, s2) =
  let prev' = map (\(p1, p2) -> (p1, p2, p2)) prev
  in moreRestrictivePairAux solver ns prev' (s1, s2)

innerScrutineeStates :: State t -> [State t]
innerScrutineeStates s@(State { curr_expr = CurrExpr _ e }) =
  map (\e' -> s { curr_expr = CurrExpr Evaluate e' }) (innerScrutinees e)

-- inner scrutinees on the left side
-- ultimately for a substitution that happens on the right
moreRestrictiveIndLeft :: S.Solver solver =>
                          solver ->
                          HS.HashSet Name ->
                          [(State t, State t)] ->
                          (State t, State t) ->
                          IO (Maybe (PrevMatch t))
moreRestrictiveIndLeft solver ns prev (s1, s2) =
  let prev1 = map (\(p1, p2) -> (p1, innerScrutineeStates p1, p2)) prev
      prev2 = [(p1', p2, p1) | (p1, p1l, p2) <- prev1, p1' <- p1l]
  in moreRestrictivePairAux solver ns prev2 (s1, s2)

-- TODO keep track of the whole expression that was used for the inner scrutinee
moreRestrictiveIndRight :: S.Solver solver =>
                           solver ->
                           HS.HashSet Name ->
                           [(State t, State t)] ->
                           (State t, State t) ->
                           IO (Maybe (PrevMatch t))
moreRestrictiveIndRight solver ns prev (s1, s2) =
  let prev1 = map (\(p1, p2) -> (p1, p2, innerScrutineeStates p2)) prev
      prev2 = [(p1, p2', p2) | (p1, p2, p2l) <- prev1, p2' <- p2l]
  in moreRestrictivePairAux solver ns prev2 (s1, s2)

isIdentity :: (Id, Expr) -> Bool
isIdentity (i1, (Var i2)) = i1 == i2
isIdentity _ = False

isIdentityMap :: HM.HashMap Id Expr -> Bool
isIdentityMap hm = foldr (&&) True (map isIdentity $ HM.toList hm)

-- approximation should be the identity map
-- needs to be enforced, won't just happen naturally
-- TODO error hit after the very first time
-- TODO does the left side in the union take precedence?
-- TODO not having identity is not the problem for forceIdempotent
moreRestrictiveEquiv :: S.Solver solver =>
                        solver ->
                        HS.HashSet Name ->
                        StateET ->
                        StateET ->
                        IO (Maybe (PrevMatch EquivTracker))
moreRestrictiveEquiv solver ns s1 s2 = do
  --putStrLn $ "MRE"
  --putStrLn $ show $ exprExtract s1
  --putStrLn $ show $ exprExtract s2
  let h1 = expr_env s1
      h2 = expr_env s2
      s1' = s1 { expr_env = E.union h1 h2 }
      s2' = s2 { expr_env = E.union h2 h1 }
  pm_maybe <- moreRestrictivePair solver ns [(s2', s1')] (s1, s2)
  case pm_maybe of
    Nothing -> trace ("FAILED " ++ show (track s1, track s2)) $ return Nothing
    Just (PrevMatch _ _ (hm, _) _) -> if isIdentityMap hm
                                      then return pm_maybe
                                      else trace ("NOT ID " ++ show hm) $ return Nothing
