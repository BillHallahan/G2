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
import qualified Data.Text as T
import qualified Data.HashMap.Lazy as HM
import qualified G2.Language.Expr as X

exprReadyForSolver :: ExprEnv -> Expr -> Bool
exprReadyForSolver h (Var i) = E.isSymbolic (idName i) h && T.isPrimType (typeOf i)
exprReadyForSolver h (App f a) = exprReadyForSolver h f && exprReadyForSolver h a
exprReadyForSolver _ (Prim _ _) = True
exprReadyForSolver _ (Lit _) = True
exprReadyForSolver _ _ = False

exprPairReadyForSolver :: (ExprEnv, ExprEnv) -> (Expr, Expr) -> Bool
exprPairReadyForSolver (h1, h2) (e1, e2) =
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
        -- CurrExpr _ orig_l = curr_expr rewrite_state_l
        -- CurrExpr _ orig_r = curr_expr rewrite_state_r
        f_name = ru_head rule'
        -- TODO doesn't cover Nothing case
        Just f = E.lookup f_name (expr_env init_state)
        t = T.typeOf f
        i = Id f_name t
        v = Var i
        orig_l = X.mkApp (v:ru_args rule')
        orig_r = ru_rhs rule'

    verifyLoop solver (zip pairs_l pairs_r)
               [(rewrite_state_l, rewrite_state_r)]
               (orig_l, orig_r)
               bindings_l bindings_r config

-- build initial hash set in Main before calling
verifyLoop :: S.Solver solver =>
              solver ->
              [(Id, Id)] ->
              [(State (), State ())] ->
              (Expr, Expr) ->
              Bindings ->
              Bindings ->
              Config ->
              IO (S.Result () ())
verifyLoop solver pairs states orig b1 b2 config | states /= [] = do
    (states', (b1', b2')) <- CM.runStateT (mapM (uncurry (runSymExec config)) states) (b1, b2)
    let sp = (\(l1, l2) -> statePairing l1 l2 pairs)
        paired_lists = concatMap sp states'
        vl (s1, s2, hs) = verifyLoop' solver s1 s2 orig hs
    proof_list <- mapM vl paired_lists
    let proof_list' = [l | Just l <- proof_list]
        new_obligations = concat proof_list'
    let verified = all isJust proof_list
    if verified then
        verifyLoop solver pairs new_obligations orig b1' b2' config
    else
        return $ S.SAT ()
  | otherwise = return $ S.UNSAT ()

-- the hash set input is for the assumptions
-- TODO printing
verifyLoop' :: S.Solver solver =>
               solver ->
               State () ->
               State () ->
               (Expr, Expr) ->
               HS.HashSet (Expr, Expr) ->
               IO (Maybe [(State (), State ())])
verifyLoop' solver s1 s2 orig assumption_set = do
  -- putStrLn "***VERIFY LOOP***"
  -- let h1 = expr_env s1
  -- putStrLn (show $ E.lookup l_name h1)
  -- putStrLn "***CONTINUE***"
  -- TODO discard some obligations based on coinduction?
  -- TODO can I use curr_expr as the initial expression?
  let obligation_set = getObligations s1 s2
      -- TODO need the original expressions
      -- CurrExpr _ orig1 = curr_expr s1
      -- CurrExpr _ orig2 = curr_expr s2
  -- putStrLn $ show $ fst orig
  -- putStrLn "*-*-*-*"
  let obligation_set' = HS.filter (not . (moreRestrictivePair s1 s2 orig)) obligation_set
      obligation_list = HS.toList obligation_set'
      (ready, not_ready) = partition (exprPairReadyForSolver (expr_env s1, expr_env s2)) obligation_list
      ready_hs = HS.fromList ready
  res <- checkObligations solver s1 s2 assumption_set ready_hs
  let currExprWrap e = CurrExpr Evaluate e
      currExprInsert s e = s { curr_expr = currExprWrap e }
  case res of
      S.UNSAT () -> return $ Just [(currExprInsert s1 e1, currExprInsert s2 e2) | (e1, e2) <- not_ready]
      _ -> return Nothing

-- l_name :: Name
-- l_name = (Name (T.pack "l") Nothing 6989586621679189074 (Just (Span {start = Loc {line = 49, col = 20, file = "tests/RewriteVerify/Correct/CoinductionCorrect.hs"}, end = Loc {line = 49, col = 21, file = "tests/RewriteVerify/Correct/CoinductionCorrect.hs"}})))

-- TODO adding stuff for debugging
getObligations :: State () -> State () -> HS.HashSet (Expr, Expr)
getObligations s1 s2 =
  let CurrExpr _ e1 = curr_expr s1
      CurrExpr _ e2 = curr_expr s2
      h1 = expr_env s1
  in case proofObligations s1 s2 e1 e2 of
      Nothing -> error "TODO expressions not equivalent"
      Just po -> po

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
        -- pcList = map extWrap $ HS.toList extraPC
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
      CurrExpr _ orig_l = curr_expr rewrite_state_l
      CurrExpr _ orig_r = curr_expr rewrite_state_r
  S.SomeSolver solver <- initSolver config
  -- convert from State t to State ()
  res <- verifyLoop solver (zip pairs_l pairs_r)
             [(rewrite_state_l {track = ()}, rewrite_state_r {track = ()})]
             (orig_l, orig_r)
             bindings_l bindings_r config
  -- UNSAT for good, SAT for bad
  return res

-- TODO check equivalence of path constraints
-- alternatively, old path constraints imply the new
-- should that go in a different file instead?
-- check negation of the implication and get UNSAT
-- split the path constraints into lists?
-- make conjunctions of those, then the needed implication
-- would need to handle AltCond constructor
-- can I represent the AltCond matching with an Expr?
-- TODO where do I need to distinguish state pair lists?

pathCondExpr :: PathCond -> Expr
pathCondExpr (ExtCond e _) = e
pathCondExpr (AltCond _ _ _) = error "TODO AltCond"

-- TODO no bool type?
exprConj :: Expr -> Expr -> Expr
exprConj e1 e2 =
    App (App (Prim And TyUnknown) e1) e2

-- get path cond list
-- make into expr list
-- fold to get a single big expr
-- put that expr into an implication
-- negate the implication

-- TODO the input must be non-empty
pathCondConj :: PathConds -> Expr
pathCondConj pc =
    let pc_list = P.toList pc
        pc_exprs = map pathCondExpr pc_list
    in
        foldr exprConj (head pc_exprs) (tail pc_exprs)

-- TODO actually returns the negation of the implication
pathCondImplication :: PathConds -> PathConds -> Expr
pathCondImplication pc_old pc_new =
    let conj_old = pathCondConj pc_old
        conj_new = pathCondConj pc_new
        impl = App (App (Prim Implies TyUnknown) conj_old) conj_new
    in
        App (Prim Not TyUnknown) impl

pathCondComparison :: PathConds -> PathConds -> PathConds
pathCondComparison pc_old pc_new =
    let not_impl = pathCondImplication pc_old pc_new
        cond = ExtCond not_impl True
    in
        P.fromList [cond]

-- TODO better name?
-- TODO what state do I use?
-- other comparisons to make here?
-- TODO do I need to clean out the path conds in s1 and s2?
checkContainment :: S.Solver solver =>
                    solver ->
                    PathConds ->
                    PathConds ->
                    State t ->
                    State t ->
                    IO (S.Result () ())
checkContainment solver pc_old pc_new s1 s2 =
    applySolver solver (pathCondComparison pc_old pc_new) s1 s2

-- TODO originally in EquivADT
moreRestrictive :: State t ->
                   (HM.HashMap Id Expr) ->
                   Expr ->
                   Expr ->
                   Maybe (HM.HashMap Id Expr)
moreRestrictive s@(State {expr_env = h}) hm e1 e2 =
  case (e1, e2) of
    (Var i, _) | E.isSymbolic (idName i) h -> Just (HM.insert i e2 hm)
               -- TODO insert syntax?
    (Var i1, Var i2) | E.isSymbolic (idName i2) h -> Nothing
                     -- the case above means sym replaces non-sym
                     | i1 == i2 -> Just hm
                     | otherwise -> Nothing
    -- TODO function application case
    -- TODO valid syntax?
    -- TODO no need for the safe union
    (App f1 a1, App f2 a2) | Just hm_f <- moreRestrictive s hm f1 f2
                           , Just hm_a <- moreRestrictive s hm_f a1 a2 -> Just hm_a
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
                                   , i1 == i2 -> moreRestrictive s hm b1 b2
                                   | otherwise -> Nothing
    -- TODO ignore types, like in exprPairing?
    (Type _, Type _) -> Just hm
    (Let d1 b1, Let d2 b2) -> error "TODO"
    (Case _ _ _, Case _ _ _) -> error "TODO"
    (Cast e1' c1, Cast e2' c2) -> error "TODO"
    (Coercion c1, Coercion c2) -> error "TODO"
    -- this case means that the constructors do not match or are not covered
    _ -> Nothing

-- TODO never hits the true case
isMoreRestrictive :: State t ->
                     Expr ->
                     Expr ->
                     Bool
isMoreRestrictive s e1 e2 =
  case moreRestrictive s HM.empty e1 e2 of
    Nothing -> False
    Just _ -> D.trace (show (e1, e2)) True

-- TODO check all elements of the HashSet
-- see if any pair fits with isMoreRestrictive
-- TODO this might not be efficient as it is now
moreRestrictivePair :: State t ->
                       State t ->
                       (Expr, Expr) ->
                       (Expr, Expr) ->
                       Bool
moreRestrictivePair s1 s2 (orig1, orig2) (e1, e2) =
  -- D.trace (show e1) $
  (isMoreRestrictive s1 orig1 e1) && (isMoreRestrictive s2 orig2 e2)

{-
moreRestrictivePair :: State t ->
                       State t ->
                       HS.HashSet (Expr, Expr) ->
                       (Expr, Expr) ->
                       Bool
moreRestrictivePair s1 s2 prev (e1, e2) =
  let mr (p1, p2) = (isMoreRestrictive s1 p1 e1) && (isMoreRestrictive s2 p2 e2)
  in
      not (HS.null $ HS.filter mr prev)
-}
