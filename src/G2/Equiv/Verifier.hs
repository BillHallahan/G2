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

-- TODO
import G2.Execution.Reducer

data StateH = StateH {
    latest :: StateET
  , history :: [StateET]
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

runSymExec :: Config ->
              StateET ->
              StateET ->
              CM.StateT Bindings IO [(StateET, StateET)]
runSymExec config s1 s2 = do
  CM.liftIO $ putStrLn "runSymExec"
  ct1 <- CM.liftIO $ getCurrentTime
  let config' = config -- { logStates = Just $ "verifier_states/a" ++ show ct1 }
  bindings <- CM.get
  (er1, bindings') <- CM.lift $ runG2ForRewriteV s1 config' bindings
  CM.put bindings'
  let final_s1 = map final_state er1
  pairs <- mapM (\s1_ -> do
                    b_ <- CM.get
                    let s2_ = transferStateInfo s1_ s2
                    ct2 <- CM.liftIO $ getCurrentTime
                    let config'' = config -- { logStates = Just $ "verifier_states/b" ++ show ct2 }
                    (er2, b_') <- CM.lift $ runG2ForRewriteV s2_ config'' b_
                    CM.put b_'
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
transferStateInfo :: State t -> State t -> State t
transferStateInfo s1 s2 =
    let
        n_eenv = E.union (expr_env s1) (expr_env s2)
    in
    s2 { expr_env = n_eenv
       , path_conds = foldr P.insert (path_conds s1) (P.toList (path_conds s2))
       , symbolic_ids = map (\(Var i) -> i) . E.elems $ E.filterToSymbolic n_eenv
       , track = track s1 }

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
-- TODO attempt to prevent double wrapping
wrapRecursiveCall n e@(Tick (NamedLoc n'@(Name t _ _ _)) e') =
  if t == DT.pack "REC"
  then e
  else Tick (NamedLoc n') $ wrcHelper n e'
wrapRecursiveCall n e@(Var (Id n' _)) =
  if n == n'
  then Tick (NamedLoc rec_name) e
  else wrcHelper n e
wrapRecursiveCall n e = wrcHelper n e

wrcHelper :: Name -> Expr -> Expr
wrcHelper n = modifyChildren (wrapRecursiveCall n)

-- do not allow wrapping for symbolic variables
recWrap :: ExprEnv -> Name -> Expr -> Expr
recWrap h n =
  if E.isSymbolic n h
  then id
  else (wrcHelper n) . (wrapRecursiveCall n)

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

tickWrap :: Expr -> Expr
tickWrap e = Tick (NamedLoc loc_name) e

exprWrap :: Stck.Stack Frame -> Expr -> Expr
exprWrap sk e = stackWrap sk $ tickWrap e

-- TODO a Var can satisfy EVF if it's symbolic or if it's unmapped
isSWHNF :: State t -> Bool
isSWHNF (State { expr_env = h, curr_expr = CurrExpr _ e }) =
  let e' = stripTicks e
  in case e' of
    Var _ -> isPrimType (typeOf e') && isExprValueForm h e'
    _ -> isExprValueForm h e'

eitherEVF :: (State t, State t) -> Bool
eitherEVF (s1, s2) =
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
newStateH s = StateH { latest = s, history = [] }

appendH :: StateH -> StateET -> StateH
appendH sh s =
  StateH {
    latest = s
  , history = (latest sh):(history sh)
  }

replaceH :: StateH -> StateET -> StateH
replaceH sh s = sh { latest = s }

prevGuarded :: (StateH, StateH) -> [(StateET, StateET)]
prevGuarded (sh1, sh2) = [(p1, p2) | p1 <- history sh1, p2 <- history sh2]

prevUnguarded :: (StateH, StateH) -> [(StateET, StateET)]
prevUnguarded = (filter (not . eitherEVF)) . prevGuarded

verifyLoop :: S.Solver solver =>
              solver ->
              (HS.HashSet Name, HS.HashSet Name) ->
              [(StateH, StateH)] ->
              [(StateH, StateH)] ->
              Bindings ->
              Config ->
              IO (S.Result () ())
verifyLoop solver ns_pair states prev b config | not (null states) = do
  let current_states = map getLatest states
  (paired_states, b') <- CM.runStateT (mapM (uncurry (runSymExec config)) current_states) b
  let vl (sh1, sh2) = verifyLoop' solver ns_pair sh1 sh2 prev
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
    verifyLoop solver ns_pair new_obligations prev' b' config
  else
    return $ S.SAT ()
  | otherwise = do
    return $ S.UNSAT ()

exprExtract :: State t -> Expr
exprExtract (State { curr_expr = CurrExpr _ e }) = e

canUseGuarded :: Obligation -> Bool
canUseGuarded (Ob c _ _) = c

stateWrap :: StateET -> StateET -> Obligation -> (StateET, StateET)
stateWrap s1 s2 (Ob _ e1 e2) =
  ( s1 { curr_expr = CurrExpr Evaluate e1 }
  , s2 { curr_expr = CurrExpr Evaluate e2 } )

-- helper functions for induction
-- TODO can something other than Case be at the outermost level?
caseRecursion :: Expr -> Bool
caseRecursion (Case e _ _) = crHelper e
caseRecursion _ = False

crHelper :: Expr -> Bool
crHelper (Tick (NamedLoc (Name t _ _ _)) e) =
  t == DT.pack "REC" || crHelper e
crHelper (Case e _ _) = crHelper e
crHelper (App e _) = crHelper e
crHelper (Cast e _) = crHelper e
crHelper _ = False

canUseInduction :: Obligation -> Bool
canUseInduction (Ob _ e1 e2) = caseRecursion e1 && caseRecursion e2

-- TODO extra helper function, might want a better name
statePairInduction :: (State t, State t) -> Bool
statePairInduction (s1, s2) =
  (caseRecursion $ exprExtract s1) && (caseRecursion $ exprExtract s2)

concretize :: HM.HashMap Id Expr -> Expr -> Expr
concretize hm e =
  HM.foldrWithKey (\i -> replaceVar (idName i)) e hm

-- TODO also need to adjust expression environments
-- TODO I also need the expr_env that will supply nested bindings
-- h_new supplies those bindings, h_old receives them
-- low-effort approach:  just copy everything
-- TODO check later if it's sound
-- TODO also need to be careful about symbolic vars
-- is overwriting the way I do now fine?
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

-- TODO printing
-- TODO non-ready obligations are not necessarily the original exprs
-- Does it still make sense to graft them onto the starting states' histories?
verifyLoop' :: S.Solver solver =>
               solver ->
               (HS.HashSet Name, HS.HashSet Name) ->
               StateH ->
               StateH ->
               [(StateH, StateH)] ->
               IO (Maybe [(StateH, StateH)])
verifyLoop' solver ns_pair sh1 sh2 prev =
  let s1 = latest sh1
      s2 = latest sh2
  in
  case getObligations ns_pair s1 s2 of
    Nothing -> do
      putStr "N! "
      putStrLn $ show (exprExtract s1, exprExtract s2)
      return Nothing
    Just obs -> do
      putStr "J! "
      putStrLn $ show (exprExtract s1, exprExtract s2)
      let (obs_g, obs_u) = partition canUseGuarded obs
          (obs_i, obs_u') = partition canUseInduction obs_u
          states_g = map (stateWrap s1 s2) obs_g
          states_u = map (stateWrap s1 s2) obs_u'
          states_i = map (stateWrap s1 s2) obs_i
          prev_g = concat $ map prevGuarded prev
          prev_u = concat $ map prevUnguarded prev
          states_g' = filter (not . (moreRestrictivePair ns_pair prev_g)) states_g
          states_u' = filter (not . (moreRestrictivePair ns_pair prev_u)) states_u
          states_i' = filter (not . (induction ns_pair prev_u)) states_i
          states = states_g' ++ states_u' ++ states_i'
          -- TODO unnecessary to pass the induction states through this?
          (ready, not_ready) = partition statePairReadyForSolver states
          ready_exprs = HS.fromList $ map (\(r1, r2) -> (exprExtract r1, exprExtract r2)) ready
          not_ready_h = map (\(n1, n2) -> (replaceH sh1 n1, replaceH sh2 n2)) not_ready
      res <- checkObligations solver s1 s2 ready_exprs
      case res of
        S.UNSAT () -> putStrLn "V?"
        _ -> putStrLn "X?"
      case res of
        S.UNSAT () -> return $ Just (not_ready_h)
        _ -> return Nothing

{-
Algorithm:
Perform the sub-expression extraction in here
The prev list is fully expanded already
Compare the sub-expressions to the prev state pairs
If any match occurs, try extrapolating it
If extrapolation works, we can flag the real state pair as a repeat
-}
induction :: (HS.HashSet Name, HS.HashSet Name) ->
             [(StateET, StateET)] ->
             (StateET, StateET) ->
             Bool
induction ns_pair prev (s1, s2) =
  let s1' = inductionState s1
      s2' = inductionState s2
      prev' = filter statePairInduction prev
      prev'' = map (\(p1, p2) -> (inductionState p1, inductionState p2)) prev'
      hm_maybe_list = map (mrHelper' ns_pair (Just HM.empty) (s1', s2')) prev''
      -- try matching the prev state pair with other prev state pairs
      hm_maybe_zipped = zip hm_maybe_list prev'
      -- ignore the combinations that didn't work
      hm_maybe_zipped' = [(hm, p) | (Just hm, p) <- hm_maybe_zipped]
      csp = concretizeStatePair (expr_env s1, expr_env s2)
      concretized = map (uncurry csp) hm_maybe_zipped'
      -- TODO optimization:  just take the first one
      concretized' = if null concretized then [] else [head concretized]
      -- TODO am I using mrHelper' backward here?
      ind p p' = mrHelper' ns_pair (Just HM.empty) p p'
      -- TODO just took the full concretized list before
      ind_fns = map ind concretized'
      -- replace everything in the old expression pair used for the match
      hm_maybe_list' = concat $ map (\f -> map f prev) ind_fns
      res = filter isJust hm_maybe_list'
  in
  not $ null res

getObligations :: (HS.HashSet Name, HS.HashSet Name) ->
                  State t ->
                  State t ->
                  Maybe [Obligation]
getObligations ns_pair s1 s2 =
  case proofObligations ns_pair s1 s2 (exprExtract s1) (exprExtract s2) of
    Nothing -> Nothing
    Just obs -> Just $
                map (\(Ob c e1 e2) -> Ob c (addStackTickIfNeeded e1) (addStackTickIfNeeded e2)) $
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
        newState = s1 { expr_env = unionEnv, path_conds = allPC }
    in S.check solver newState allPC

obligationWrap :: HS.HashSet (Expr, Expr) -> Maybe PathCond
obligationWrap obligations =
    let obligation_list = HS.toList obligations
        eq_list = map (\(e1, e2) -> App (App (Prim Eq TyUnknown) e1) e2) obligation_list
        -- TODO type issue again
        conj = foldr1 (\o1 o2 -> App (App (Prim And TyUnknown) o1) o2) eq_list
    in
    if null eq_list
    then Nothing
    else Just $ ExtCond (App (Prim Not TyUnknown) conj) True

totalName :: [DT.Text] -> Name -> Bool
totalName texts (Name t _ _ _) = t `elem` texts

checkRule :: Config ->
             State t ->
             Bindings ->
             [DT.Text] ->
             RewriteRule ->
             IO (S.Result () ())
checkRule config init_state bindings total rule = do
  let (rewrite_state_l, bindings') = initWithLHS init_state bindings $ rule
      (rewrite_state_r, bindings'') = initWithRHS init_state bindings' $ rule
      -- convert from State t to StateET
      e_l = exprExtract rewrite_state_l
      e_r = exprExtract rewrite_state_r
      -- Tick wrapping for recursive functions
      h_l = expr_env rewrite_state_l
      h_r = expr_env rewrite_state_r
      -- handle corecursion, not just direct recursion
      wrap_l = wrapAllRecursion (G.getCallGraph h_l) h_l
      wrap_r = wrapAllRecursion (G.getCallGraph h_r) h_r
      total_names = filter (totalName total) (map idName $ ru_bndrs rule)
      -- TODO do I still need the HashSet usage elsewhere?
      total_hs = foldr HS.insert HS.empty total_names
      EquivTracker et m _ = emptyEquivTracker
      start_equiv_tracker = EquivTracker et m total_hs
      rewrite_state_l' = rewrite_state_l {
                           track = start_equiv_tracker
                         , curr_expr = CurrExpr Evaluate $ tickWrap $ e_l
                         , expr_env = E.mapWithKey wrap_l h_l
                         }
      rewrite_state_r' = rewrite_state_r {
                           track = start_equiv_tracker
                         , curr_expr = CurrExpr Evaluate $ tickWrap $ e_r
                         , expr_env = E.mapWithKey wrap_r h_r
                         }
      -- the keys are the same between the old and new environments
      ns_l = HS.fromList $ E.keys $ h_l
      ns_r = HS.fromList $ E.keys $ h_r
  S.SomeSolver solver <- initSolver config
  putStrLn $ "***\n" ++ (show $ ru_name rule) ++ "\n***"
  putStrLn $ show $ curr_expr rewrite_state_l'
  putStrLn $ show $ curr_expr rewrite_state_r'
  let rewrite_state_l'' = newStateH rewrite_state_l'
      rewrite_state_r'' = newStateH rewrite_state_r'
  res <- verifyLoop solver (ns_l, ns_r)
             [(rewrite_state_l'', rewrite_state_r'')]
             [(rewrite_state_l'', rewrite_state_r'')]
             bindings'' config
  -- UNSAT for good, SAT for bad
  return res

-- s1 is the old state, s2 is the new state
moreRestrictive :: State t ->
                   State t ->
                   HS.HashSet Name ->
                   HM.HashMap Id Expr ->
                   Expr ->
                   Expr ->
                   Maybe (HM.HashMap Id Expr)
moreRestrictive s1@(State {expr_env = h1}) s2@(State {expr_env = h2}) ns hm e1 e2 =
  case (e1, e2) of
    -- ignore all Ticks
    (Tick _ e1', _) -> moreRestrictive s1 s2 ns hm e1' e2
    (_, Tick _ e2') -> moreRestrictive s1 s2 ns hm e1 e2'
    -- TODO new cases, may make some old cases unreachable
    (Var i, _) | not $ E.isSymbolic (idName i) h1
               , not $ HS.member (idName i) ns
               , Just e <- E.lookup (idName i) h1 -> moreRestrictive s1 s2 ns hm e e2
    (_, Var i) | not $ E.isSymbolic (idName i) h2
               , not $ HS.member (idName i) ns
               , Just e <- E.lookup (idName i) h2 -> moreRestrictive s1 s2 ns hm e1 e
    -- TODO altered order
    (Var i1, Var i2) | HS.member (idName i1) ns
                     , idName i1 == idName i2 -> Just hm
                     | HS.member (idName i1) ns -> Nothing
                     | HS.member (idName i2) ns -> Nothing
    (Var i, _) | E.isSymbolic (idName i) h1
               , Nothing <- HM.lookup i hm -> Just (HM.insert i (inlineEquiv h2 ns e2) hm)
               | E.isSymbolic (idName i) h1
               , Just e <- HM.lookup i hm
               , e == inlineEquiv h2 ns e2 -> Just hm
               -- this last case means there's a mismatch
               | E.isSymbolic (idName i) h1 -> Nothing
               | not $ HS.member (idName i) ns -> error $ "unmapped variable " ++ (show i)
    (_, Var i) | E.isSymbolic (idName i) h2 -> Nothing -- sym replaces non-sym
               | not $ HS.member (idName i) ns -> error $ "unmapped variable " ++ (show i)
    (App f1 a1, App f2 a2) | Just hm_f <- moreRestrictive s1 s2 ns hm f1 f2
                           , Just hm_a <- moreRestrictive s1 s2 ns hm_f a1 a2 -> Just hm_a
                           | otherwise -> Nothing
    -- We just compare the names of the DataCons, not the types of the DataCons.
    -- This is because (1) if two DataCons share the same name, they must share the
    -- same type, but (2) "the same type" may be represented in different syntactic
    -- ways, most significantly bound variable names may differ
    -- "forall a . a" is the same type as "forall b . b", but fails a syntactic check.
    (Data (DataCon d1 _), Data (DataCon d2 _))
                                  | d1 == d2 -> Just hm
                                  | otherwise -> Nothing
    -- TODO potential problems with type equality checking?
    (Prim p1 t1, Prim p2 t2) | p1 == p2
                             , t1 == t2 -> Just hm
                             | otherwise -> Nothing
    (Lit l1, Lit l2) | l1 == l2 -> Just hm
                     | otherwise -> Nothing
    (Lam lu1 i1 b1, Lam lu2 i2 b2)
                | lu1 == lu2
                , i1 == i2 ->
                  let ns' = HS.insert (idName i1) ns
                  -- no need to insert twice over because they're equal
                  in moreRestrictive s1 s2 ns' hm b1 b2
                | otherwise -> Nothing
    -- ignore types, like in exprPairing
    (Type _, Type _) -> Just hm
    -- TODO if scrutinee is symbolic var, make Alt vars symbolic?
    (Case e1' i1 a1, Case e2' i2 a2)
                | Just hm' <- moreRestrictive s1 s2 ns hm e1' e2' ->
                  -- add the matched-on exprs to the envs beforehand
                  let h1' = E.insert (idName i1) e1' h1
                      h2' = E.insert (idName i2) e2' h2
                      s1' = s1 { expr_env = h1' }
                      s2' = s2 { expr_env = h2' }
                      mf hm_ (e1_, e2_) = moreRestrictiveAlt s1' s2' ns hm_ e1_ e2_
                      l = zip a1 a2
                  in foldM mf hm' l
    _ -> Nothing

inlineEquiv :: ExprEnv -> HS.HashSet Name -> Expr -> Expr
inlineEquiv h ns v@(Var (Id n _))
    | E.isSymbolic n h = v
    | HS.member n ns = v
    | Just e <- E.lookup n h = inlineEquiv h ns e
inlineEquiv h ns e = modifyChildren (inlineEquiv h ns) e

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
                      HM.HashMap Id Expr ->
                      Alt ->
                      Alt ->
                      Maybe (HM.HashMap Id Expr)
moreRestrictiveAlt s1 s2 ns hm (Alt am1 e1) (Alt am2 e2) =
  if altEquiv am1 am2 then
  case am1 of
    DataAlt _ t1 -> let n1 = map (\(Id n _) -> n) t1
                        ns' = foldr HS.insert ns n1
                    in moreRestrictive s1 s2 ns' hm e1 e2
    _ -> moreRestrictive s1 s2 ns hm e1 e2
  else Nothing

mrHelper :: State t ->
            State t ->
            HS.HashSet Name ->
            Maybe (HM.HashMap Id Expr) ->
            Maybe (HM.HashMap Id Expr)
mrHelper _ _ _ Nothing = Nothing
mrHelper s1 s2 ns (Just hm) =
  moreRestrictive s1 s2 ns hm (exprExtract s1) (exprExtract s2)

-- TODO better name?
-- TODO the first state pair is the new one
-- TODO do I really need two ns lists?
mrHelper' :: (HS.HashSet Name, HS.HashSet Name) ->
             Maybe (HM.HashMap Id Expr) ->
             (State t, State t) ->
             (State t, State t) ->
             Maybe (HM.HashMap Id Expr)
mrHelper' (ns1, ns2) hm_maybe (s1, s2) (p1, p2) =
  mrHelper p2 s2 ns2 $ mrHelper p1 s1 ns1 hm_maybe

moreRestrictivePair :: (HS.HashSet Name, HS.HashSet Name) ->
                       [(State t, State t)] ->
                       (State t, State t) ->
                       Bool
moreRestrictivePair (ns1, ns2) prev (s1, s2) =
  let
      mr (p1, p2) = isJust $ mrHelper p2 s2 ns2 $ mrHelper p1 s1 ns1 (Just HM.empty)
  in
      (not $ null $ filter mr prev)
