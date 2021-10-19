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
       , symbolic_ids = HS.fromList . map (\(Var i) -> i) . E.elems $ E.filterToSymbolic n_eenv
       , track = track s1 }

frameWrap :: Frame -> Expr -> Expr
frameWrap (CaseFrame i alts) e = Case e i alts
frameWrap (ApplyFrame e') e = App e e'
frameWrap (UpdateFrame _) e = e
frameWrap (MergePtFrame _) e = e
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
newStateH s = StateH { latest = s, history = [] }

appendH :: StateH -> StateET -> StateH
appendH sh s =
  StateH {
    latest = s
  , history = (latest sh):(history sh)
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
              IO (S.Result () ())
verifyLoop solver ns states prev b config | not (null states) = do
  let current_states = map getLatest states
  (paired_states, b') <- CM.runStateT (mapM (uncurry (runSymExec config)) current_states) b
  let vl (sh1, sh2) = verifyLoop' solver ns sh1 sh2 prev
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
    verifyLoop solver ns new_obligations prev' b' config
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

-- TODO helpers for "finite induction"
-- inline variables for this?
-- vars in the finite set count, so do Data constructors with finite args
-- also need list of symbolic vars, and list of vars not to inline?
-- TODO keep track of inlined vars to avoid cycles
finiteExpr :: HS.HashSet Name ->
              HS.HashSet Name ->
              ExprEnv ->
              [Name] -> -- ^ vars inlined so far
              Expr ->
              Bool
finiteExpr ns finite_hs h n e = case e of
  Var i | (idName i) `elem` finite_hs -> True
        | (idName i) `elem` ns -> False
        | (idName i) `elem` n -> False
        -- symbolic but not finite:  not allowed
        | E.isSymbolic (idName i) h -> False
        | m <- idName i
        , Just e' <- E.lookup m h -> finiteExpr ns finite_hs h (m:n) e'
        | otherwise -> error "unmapped variable"
  -- TODO can literal strings be infinite?  This assumes they can't be
  Lit _ -> True
  -- TODO also assumes types can't be infinite
  Prim _ _ -> True
  Data _ -> True
  -- TODO should I be more careful about this?
  App e1 e2 -> (finiteExpr ns finite_hs h n e1) && (finiteExpr ns finite_hs h n e2)
  Lam _ _ _ -> False
  -- TODO might not even need to handle these two cases at all
  Let _ _ -> False
  Case _ _ _ -> False
  Type _ -> True
  --Cast e' _ -> finiteExpr finite_hs e'
  --Coercion _ -> True
  Tick _ e' -> finiteExpr ns finite_hs h n e'
  _ -> error "unrecognized"

notM :: IO Bool -> IO Bool
notM b = do
  b' <- b
  return (not b')

andM :: IO Bool -> IO Bool -> IO Bool
andM b1 b2 = do
  b1' <- b1
  b2' <- b2
  return (b1' && b2')

-- TODO printing
verifyLoop' :: S.Solver solver =>
               solver ->
               HS.HashSet Name ->
               StateH ->
               StateH ->
               [(StateH, StateH)] ->
               IO (Maybe [(StateH, StateH)])
verifyLoop' solver ns sh1 sh2 prev =
  let s1 = latest sh1
      s2 = latest sh2
  in
  case getObligations ns s1 s2 of
    Nothing -> do
      -- obligation generation failed, so the expressions must not be equivalent
      putStr "N! "
      putStrLn $ show (exprExtract s1, exprExtract s2)
      return Nothing
    Just obs -> do
      putStrLn "J!"
      putStrLn $ printHaskell s1 $ exprExtract s1
      putStrLn $ printHaskell s2 $ exprExtract s2

      let prev' = concat $ map prevFiltered prev
          (obs_i, obs_c) = partition canUseInduction obs
          states_c = map (stateWrap s1 s2) obs_c
      states_c' <- filterM (notM . (moreRestrictivePair solver ns prev')) states_c

      let states_i = map (stateWrap s1 s2) obs_i
          states_i' = filter (not . (induction ns prev')) states_i

      -- TODO unnecessary to pass the induction states through this?
      let states = states_c' ++ states_i'
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
induction :: HS.HashSet Name ->
             [(StateET, StateET)] ->
             (StateET, StateET) ->
             Bool
induction ns prev (s1, s2) =
  let s1' = inductionState s1
      s2' = inductionState s2
      prev' = filter statePairInduction prev
      prev'' = map (\(p1, p2) -> (inductionState p1, inductionState p2)) prev'
      hm_maybe_list = map (indHelper ns (Just (HM.empty, HS.empty)) (s1', s2')) prev''
      -- try matching the prev state pair with other prev state pairs
      hm_maybe_zipped = zip hm_maybe_list prev'
      -- ignore the combinations that didn't work
      -- TODO ignoring extra obligations here; is that a problem?
      -- TODO modify the code to discard ones with extra obligations
      hm_maybe_zipped' = [(hm, p) | (Just (hm, hs), p) <- hm_maybe_zipped, HS.null hs]
      csp = concretizeStatePair (expr_env s1, expr_env s2)
      concretized = map (uncurry csp) hm_maybe_zipped'
      -- TODO optimization:  just take the first one
      -- just took the full concretized list before
      concretized' = case concretized of
        [] -> []
        c:_ -> [c]
      ind p p' = indHelper ns (Just (HM.empty, HS.empty)) p p'
      ind_fns = map ind concretized'
      -- replace everything in the old expression pair used for the match
      hm_maybe_list' = concat $ map (\f -> map f prev) ind_fns
      res = filter isJust hm_maybe_list'
  in
  not $ null res

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
      s' = s {
      track = et
    , curr_expr = CurrExpr Evaluate $ tickWrap $ exprExtract s
    , expr_env = E.mapWithKey wrap_cg h
    }
  in newStateH s'

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
      EquivTracker et m _ _ = emptyEquivTracker
      start_equiv_tracker = EquivTracker et m total_hs finite_hs
      -- the keys are the same between the old and new environments
      ns_l = HS.fromList $ E.keys $ expr_env rewrite_state_l
      ns_r = HS.fromList $ E.keys $ expr_env rewrite_state_r
      -- no need for two separate name sets
      ns = HS.union ns_l ns_r
      rewrite_state_l' = startingState start_equiv_tracker rewrite_state_l
      rewrite_state_r' = startingState start_equiv_tracker rewrite_state_r
  S.SomeSolver solver <- initSolver config
  putStrLn $ "***\n" ++ (show $ ru_name rule) ++ "\n***"
  res <- verifyLoop solver ns
             [(rewrite_state_l', rewrite_state_r')]
             [(rewrite_state_l', rewrite_state_r')]
             bindings'' config
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
    -- TODO if scrutinee is symbolic var, make Alt vars symbolic?
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

restrictHelper :: State t ->
                  State t ->
                  HS.HashSet Name ->
                  Maybe (HM.HashMap Id Expr, HS.HashSet (Expr, Expr)) ->
                  Maybe (HM.HashMap Id Expr, HS.HashSet (Expr, Expr))
restrictHelper _ _ _ Nothing = Nothing
restrictHelper s1 s2 ns (Just hm) =
  moreRestrictive s1 s2 ns hm [] [] (exprExtract s1) (exprExtract s2)

-- the first state pair is the new one, the second is the old
indHelper :: HS.HashSet Name ->
             Maybe (HM.HashMap Id Expr, HS.HashSet (Expr, Expr)) ->
             (State t, State t) ->
             (State t, State t) ->
             Maybe (HM.HashMap Id Expr, HS.HashSet (Expr, Expr))
indHelper ns hm_maybe (s1, s2) (p1, p2) =
  restrictHelper p2 s2 ns $ restrictHelper p1 s1 ns hm_maybe

concObligation :: HM.HashMap Id Expr -> Maybe PathCond
concObligation hm =
  let l = HM.toList hm
      l' = map (\(i, e) -> (Var i, e)) l
  in obligationWrap $ HS.fromList l'

-- All the PathConds that this receives are generated by symbolic execution.
-- Consequently, non-primitive types are not an issue here.
extractCond :: PathCond -> Expr
extractCond (ExtCond e True) = e
extractCond (ExtCond e False) = App (Prim Not TyUnknown) e
extractCond (AltCond l e True) =
  App (App (Prim Eq TyUnknown) e) (Lit l)
extractCond (AltCond l e False) =
  App (App (Prim Neq TyUnknown) e) (Lit l)

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

-- extra filter on top of isJust for maybe_pairs
-- if restrictHelper end result is Just, try checking the corresponding PCs
-- for True output, there needs to be an entry for which that check succeeds
-- should I replace the result with a Bool?
moreRestrictivePair :: S.Solver solver =>
                       solver ->
                       HS.HashSet Name ->
                       [(State t, State t)] ->
                       (State t, State t) ->
                       IO Bool
moreRestrictivePair solver ns prev (s1, s2) = do
  let mr (p1, p2) = restrictHelper p2 s2 ns $
                    restrictHelper p1 s1 ns (Just (HM.empty, HS.empty))
      getObs m = case m of
        Nothing -> HS.empty
        Just (_, hs) -> hs
      getConcretizations m = case m of
        Nothing -> HM.empty
        Just (hm, _) -> hm
      maybe_pairs = map mr prev
      obs_sets = map getObs maybe_pairs
      conc_sets = map getConcretizations maybe_pairs
      obs = foldr HS.union HS.empty obs_sets
      conc_obs = map concObligation conc_sets
      h1 = expr_env s1
      h2 = expr_env s2
      obs' = HS.filter (\(e1, e2) -> rfs h1 e1 && rfs h2 e2) obs
      mpc m = case m of
        (Just (hm, _), (s_old1, s_old2)) ->
          andM (moreRestrictivePC solver s_old1 s1 hm) (moreRestrictivePC solver s_old2 s2 hm)
        _ -> return False
      bools = map mpc (zip maybe_pairs prev)
  res <- checkObligations solver s1 s2 obs'
  bools' <- filterM (\x -> x) bools
  -- TODO HashSet doesn't have a "forall" function?
  case (HS.size obs == HS.size obs', res) of
    (True, S.UNSAT ()) -> return (not $ null bools')
    _ -> return False
