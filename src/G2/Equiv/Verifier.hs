{-# LANGUAGE OverloadedStrings #-}

module G2.Equiv.Verifier
    ( verifyLoop
    , runVerifier
    , checkRule
    ) where

import G2.Language

import G2.Config

import G2.Interface

import qualified Control.Monad.State.Lazy as CM

import qualified G2.Language.ExprEnv as E
import qualified G2.Language.Typing as T

import Data.List
import Data.Maybe
import qualified Data.Text as DT

import qualified Data.HashSet as HS
import qualified G2.Solver as S

import qualified G2.Language.PathConds as P

import G2.Equiv.InitRewrite
import G2.Equiv.EquivADT

-- TODO
import qualified Debug.Trace as D
import qualified Data.HashMap.Lazy as HM
import qualified G2.Language.Expr as X

exprReadyForSolver :: ExprEnv -> Expr -> Bool
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

-- TODO different underlying G2 usage
runSymExec :: Config ->
              State () ->
              State () ->
              CM.StateT (Bindings, Bindings) IO ([State ()], [State ()])
runSymExec config s1 s2 = do
  (bindings1, bindings2) <- CM.get
  (exec_res1, bindings1') <- CM.lift $ runG2ForRewriteV s1 config bindings1
  (exec_res2, bindings2') <- CM.lift $ runG2ForRewriteV s2 config bindings2
  CM.put (bindings1', bindings2')
  return (map final_state exec_res1, map final_state exec_res2)

runVerifier :: S.Solver solver =>
               solver ->
               String ->
               State () ->
               Bindings ->
               Config ->
               IO (S.Result () ())
runVerifier solver entry init_state bindings config = do
    let tentry = DT.pack entry
        rule = find (\r -> tentry == ru_name r) (rewrite_rules bindings)
        rule' = case rule of
                Just r -> r
                Nothing -> error "not found"
    let (rewrite_state_l, bindings_l) = initWithLHS init_state bindings $ rule'
        (rewrite_state_r, bindings_r) = initWithRHS init_state bindings $ rule'
    let pairs_l = symbolic_ids rewrite_state_l
        pairs_r = symbolic_ids rewrite_state_r
        ns_l = HS.fromList $ E.keys $ expr_env rewrite_state_l
        ns_r = HS.fromList $ E.keys $ expr_env rewrite_state_r
    verifyLoop solver (ns_l, ns_r) (zip pairs_l pairs_r)
               [(rewrite_state_l, rewrite_state_r)]
               [(rewrite_state_l, rewrite_state_r)]
               bindings_l bindings_r config

-- build initial hash set in Main before calling
verifyLoop :: S.Solver solver =>
              solver ->
              (HS.HashSet Name, HS.HashSet Name) ->
              [(Id, Id)] ->
              [(State (), State ())] ->
              [(State (), State ())] ->
              Bindings ->
              Bindings ->
              Config ->
              IO (S.Result () ())
verifyLoop solver ns_pair pairs states prev b1 b2 config | states /= [] = do
    (states', (b1', b2')) <- CM.runStateT (mapM (uncurry (runSymExec config)) states) (b1, b2)
    let sp = (\(l1, l2) -> statePairing l1 l2 pairs)
        paired_lists = concatMap sp states'
        vl (s1, s2, hs) = verifyLoop' solver ns_pair s1 s2 prev hs
    proof_list <- mapM vl paired_lists
    let proof_list' = [l | Just (_, l) <- proof_list]
        new_obligations = concat proof_list'
        -- TODO also get previously-solved equivalences to add to prev
        -- doesn't seem to help
        solved_list = concat [l | Just (l, _) <- proof_list]
    let -- TODO do I really need all of these?
        new_prev = new_obligations ++ solved_list ++ prev
        -- new_prev = HS.union prev (HS.fromList new_obligations)
    let verified = all isJust proof_list
    -- TODO wrapping may still be an issue here
    if verified then
        verifyLoop solver ns_pair pairs new_obligations new_prev b1' b2' config
    else
        return $ S.SAT ()
  | otherwise = return $ S.UNSAT ()

{-
currExprInsert :: State t -> Expr -> State t
currExprInsert s e = s { curr_expr = CurrExpr Evaluate e }
-}

exprExtract :: State t -> Expr
exprExtract (State { curr_expr = CurrExpr _ e }) = e

-- the hash set input is for the assumptions
-- TODO printing
verifyLoop' :: S.Solver solver =>
               solver ->
               (HS.HashSet Name, HS.HashSet Name) ->
               State () ->
               State () ->
               [(State (), State ())] ->
               HS.HashSet (Expr, Expr) ->
               IO (Maybe ([(State (), State ())], [(State (), State ())]))
verifyLoop' solver ns_pair s1 s2 prev assumption_set =
  let obligation_maybe = obligationStates s1 s2
  in case obligation_maybe of
      Nothing -> do return Nothing
      Just obs -> do
          let obligation_list = filter (not . (moreRestrictivePair ns_pair prev)) obs
              (ready, not_ready) = partition statePairReadyForSolver obligation_list
              ready_exprs = HS.fromList $ map (\(r1, r2) -> (exprExtract r1, exprExtract r2)) ready
          res <- checkObligations solver s1 s2 assumption_set ready_exprs
          case res of
            S.UNSAT () -> return $ Just (ready, not_ready)
            _ -> return Nothing
  {-
  -- TODO discard some obligations based on coinduction?
  -- TODO can I use curr_expr as the initial expression?
  -- TODO not sure about use of states here
  let obligation_set = obligationStates s1 s2
      -- TODO list and set naming
      obligation_list = filter (not . (moreRestrictivePair ns_pair prev)) obligation_set
      -- TODO adding difference to the returned list doesn't help
  {-
  putStr $ show $ length obligation_set
  putStr ", "
  putStr $ show $ length obligation_list
  putStr "\n"
  -}
  -- putStrLn $ show $ map (\(r1, r2) -> (exprExtract r1, exprExtract r2)) prev
  putStrLn $ show $ map (\(r1, r2) -> (exprExtract r1, exprExtract r2)) obligation_list
  -- putStrLn $ show $ HS.toList assumption_set
  let (ready, not_ready) = partition statePairReadyForSolver obligation_list
      ready_exprs = HS.fromList $ map (\(r1, r2) -> (exprExtract r1, exprExtract r2)) ready
  -- TODO is it still right to use s1 and s2 here?
  -- probably doesn't matter, check that nothing important changes
  res <- checkObligations solver s1 s2 assumption_set ready_exprs
  case res of
      S.UNSAT () -> return $ Just (ready, not_ready)
      _ -> return Nothing
  -}

-- TODO badDropSum triggers the Nothing case
getObligations :: State () -> State () -> Maybe (HS.HashSet (Expr, Expr))
getObligations s1 s2 =
  let CurrExpr _ e1 = curr_expr s1
      CurrExpr _ e2 = curr_expr s2
  in proofObligations s1 s2 e1 e2
  {-
  in case proofObligations s1 s2 e1 e2 of
      Nothing -> error "expressions not equivalent"
      Just po -> po
  -}

-- TODO wrap the expression pairs with their states
obligationStates ::  State () -> State () -> Maybe [(State (), State ())]
obligationStates s1 s2 =
  let stateWrap (e1, e2) =
        ( s1 { curr_expr = CurrExpr Evaluate e1 }
        , s2 { curr_expr = CurrExpr Evaluate e2 } )
  in case getObligations s1 s2 of
      Nothing -> Nothing
      Just obs -> Just $ map stateWrap $ HS.toList obs

checkObligations :: S.Solver solver =>
                    solver ->
                    State () ->
                    State () ->
                    HS.HashSet (Expr, Expr) ->
                    HS.HashSet (Expr, Expr) ->
                    IO (S.Result () ())
checkObligations solver s1 s2 assumption_set obligation_set | not $ HS.null obligation_set =
    let maybeAllPO = obligationWrap obligation_set
        -- snd should have the same type
        assumption_set' = HS.filter (isPrimType . typeOf . fst) assumption_set
        assumptionPC = HS.toList $ HS.map assumptionWrap assumption_set'
        newPC = foldr P.insert P.empty (assumptionPC)
    in
    case maybeAllPO of
        Nothing -> applySolver solver newPC s1 s2
        Just allPO -> applySolver solver (P.insert allPO newPC) s1 s2
  | otherwise = return $ S.UNSAT ()

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
    in
    S.check solver newState allPC

-- TODO replace with equivalent function from other branch G2q-merge-final
assumptionWrap :: (Expr, Expr) -> PathCond
assumptionWrap (e1, e2) =
    -- TODO what type for the equality?
    ExtCond (App (App (Prim Eq TyUnknown) e1) e2) True

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

checkRule :: Config ->
             State t ->
             Bindings ->
             RewriteRule ->
             IO (S.Result () ())
checkRule config init_state bindings rule = do
  let (rewrite_state_l, bindings_l) = initWithLHS init_state bindings $ rule
      (rewrite_state_r, bindings_r) = initWithRHS init_state bindings $ rule
      pairs_l = symbolic_ids rewrite_state_l
      pairs_r = symbolic_ids rewrite_state_r
      rewrite_state_l' = rewrite_state_l {track = ()}
      rewrite_state_r' = rewrite_state_r {track = ()}
      ns_l = HS.fromList $ E.keys $ expr_env rewrite_state_l
      ns_r = HS.fromList $ E.keys $ expr_env rewrite_state_r
  S.SomeSolver solver <- initSolver config
  -- convert from State t to State ()
  res <- verifyLoop solver (ns_l, ns_r) (zip pairs_l pairs_r)
             [(rewrite_state_l', rewrite_state_r')]
             [(rewrite_state_l', rewrite_state_r')]
             bindings_l bindings_r config
  -- UNSAT for good, SAT for bad
  return res

-- s1 is the old state, s2 is the new state
-- TODO look at var mappings in expr envs, not just the hash map
-- TODO use exprs as recursive arguments
-- no need for extra state manipulation then
moreRestrictive :: State t ->
                   State t ->
                   HS.HashSet Name ->
                   HM.HashMap Id Expr ->
                   Expr ->
                   Expr ->
                   Maybe (HM.HashMap Id Expr)
--moreRestrictive _ _ _ _ hm e1 e2 | e1 == e2 = Just hm
moreRestrictive s1@(State {expr_env = h1}) s2@(State {expr_env = h2}) ns hm e1 e2 =
  case (e1, e2) of
    (Var i1, Var i2) | HS.member (idName i1) ns
                     , idName i1 == idName i2 -> Just hm
    (Var i, _) -- | HS.member (idName i) ns -> error $ show (i, e2)
               | E.isSymbolic (idName i) h1
               , Nothing <- HM.lookup i hm -> Just (HM.insert i e2 hm)
               {-
               | E.isSymbolic (idName i) h1
               , Just e <- HM.lookup i hm -> D.trace "&&&" $ moreRestrictive s1 s2 hm e e2
               -}
               | E.isSymbolic (idName i) h1
               , Just e <- HM.lookup i hm
               , e == e2 -> Just hm
               -- this last case means there's a mismatch
               -- | E.isSymbolic (idName i) h1 -> Nothing
               -- non-symbolic cases
               | not $ HS.member (idName i) ns
               , Just e <- E.lookup (idName i) h1 -> moreRestrictive s1 s2 ns hm e e2
               | not $ HS.member (idName i) ns -> error "unmapped variable"
    (_, Var i) | E.isSymbolic (idName i) h2 -> Nothing
               -- the case above means sym replaces non-sym
               | Just e <- E.lookup (idName i) h2 -> moreRestrictive s1 s2 ns hm e1 e
               | otherwise -> error "unmapped variable"
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
    -- TODO do I need to be more careful about Lit equality?
    (Lit l1, Lit l2) | l1 == l2 -> Just hm
                     | otherwise -> Nothing
    -- TODO I presume I need syntactic equality for lambda expressions
    -- LamUse is a simple variant
    (Lam lu1 i1 b1, Lam lu2 i2 b2) | lu1 == lu2
                                   , i1 == i2 -> moreRestrictive s1 s2 ns hm b1 b2
                                   | otherwise -> Nothing
    -- TODO ignore types, like in exprPairing?
    (Type _, Type _) -> Just hm
    --(Case e1' i1 a1, Case e2' i2 a2) | i1 == i2
    -- _ -> D.trace (show (e1, e2)) $ error "nothing case"
    _ -> Nothing

isMoreRestrictive :: State t ->
                     State t ->
                     HS.HashSet Name ->
                     Bool
isMoreRestrictive s1 s2 ns =
  let CurrExpr _ e1 = curr_expr s1
      CurrExpr _ e2 = curr_expr s2
  in isJust $ moreRestrictive s1 s2 ns HM.empty e1 e2

moreRestrictivePair :: (HS.HashSet Name, HS.HashSet Name) ->
                       [(State t, State t)] ->
                       (State t, State t) ->
                       Bool
moreRestrictivePair (ns1, ns2) prev (s1, s2) =
  let mr (p1, p2) = isMoreRestrictive p1 s1 ns1 && isMoreRestrictive p2 s2 ns2
  in
      not $ null $ filter mr prev
