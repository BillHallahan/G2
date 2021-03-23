{-# LANGUAGE OverloadedStrings #-}

module G2.Equiv.Verifier (verifyLoop) where

import G2.Language

import G2.Config

import G2.Interface

import qualified Control.Monad.State.Lazy as CM

import qualified G2.Language.ExprEnv as E
import qualified G2.Language.Typing as T

import Data.List
import Data.Maybe

import qualified Data.HashSet as HS
import qualified G2.Solver as S

import qualified G2.Language.PathConds as P

import G2.Equiv.InitRewrite
import G2.Equiv.EquivADT

exprReadyForSolver :: ExprEnv -> Expr -> Bool
exprReadyForSolver h (Var i) = E.isSymbolic (idName i) h && T.isPrimType (typeOf i)
exprReadyForSolver h (App f a) = exprReadyForSolver h f && exprReadyForSolver h a
exprReadyForSolver h (Prim _ _) = True
exprReadyForSolver h (Lit _) = True
exprReadyForSolver h _ = False

exprPairReadyForSolver :: (ExprEnv, ExprEnv) -> (Expr, Expr) -> Bool
exprPairReadyForSolver (h1, h2) (e1, e2) =
  exprReadyForSolver h1 e1 && exprReadyForSolver h2 e2

readyForSolver :: (State (), State ()) -> Bool
readyForSolver (s1, s2) =
  let CurrExpr _ e1 = curr_expr s1
      CurrExpr _ e2 = curr_expr s2
  in
  exprPairReadyForSolver (expr_env s1, expr_env s2) (e1, e2)

runSymExec :: Config ->
              State () ->
              State () ->
              CM.StateT (Bindings, Bindings) IO ([State ()], [State ()])
runSymExec config s1 s2 = do
  (bindings1, bindings2) <- CM.get
  (exec_res1, bindings1') <- CM.lift $ runG2WithConfig s1 config bindings1
  (exec_res2, bindings2') <- CM.lift $ runG2WithConfig s2 config bindings2
  CM.put (bindings1', bindings2')
  return (map final_state exec_res1, map final_state exec_res2)

{-
runSymExec :: Config ->
              State () ->
              CM.StateT Bindings IO [State ()]
runSymExec config s1 = do
  bindings1 <- CM.get
  (exec_res1, bindings1') <- CM.lift $ runG2WithConfig s1 config bindings1
  CM.put bindings1'
  return (map final_state exec_res1)
-}

tupleListFlatten :: [([State ()], [State ()])] -> [(State (), State ())]
tupleListFlatten [] = []
tupleListFlatten ((l1, l2) : t) = (zip l1 l2) ++ tupleListFlatten t

-- build initial hash set in Main before calling
{-
Things to do:
Iterate over every pair of states produced
Put it into the solver, see if it's equivalent
If any pair isn't, reject
TODO which wrappings from the other files matter?
TODO is there a way to group multiple Results into one?
TODO also catch the Nothing case for proofObligations
TODO where do the PathConds come in?
-}
verifyLoop :: S.Solver solver =>
              solver ->
              [(Id, Id)] ->
              [(State (), State ())] ->
              Bindings ->
              Bindings ->
              Config ->
              IO (S.Result () ())
verifyLoop solver pairs states b1 b2 config | states /= [] = do
    print $ length states
    -- print (length states1, length states2)
    (states', (b1', b2')) <- CM.runStateT (mapM (uncurry (runSymExec config)) states) (b1, b2)
    let sp = (\(l1, l2) -> statePairing l1 l2 pairs)
        paired_lists = concatMap sp states'
        -- proof_list = map getObligations paired_lists
        -- proof_list' = concatMap toList proof_list
        -- proof_list' = zip proof_list paired_lists
        vl (s1, s2, hs) = verifyLoop' solver s1 s2 hs
    proof_list <- mapM vl paired_lists
    let proof_list' = [l | Just l <- proof_list]
        new_obligations = concat proof_list'
        -- rfs_state (_, (s1, s2, _)) = readyForSolver (s1, s2)
    -- (states1', b1') <- CM.runStateT (mapM (runSymExec config) states1) b1
    -- (states2', b2') <- CM.runStateT (mapM (runSymExec config) states2) b2
    -- print (curr_expr $ head $ head states1', curr_expr $ head $ head states2')
    -- let states1'' = concat states1'
        -- states2'' = concat states2'
        -- (solver_states1, recursion_states1) = partition readyForSolver states1''
        -- (solver_states2, recursion_states2) = partition readyForSolver states2''
        -- paired_states = statePairing states1'' states2'' pairs
    -- res <- mapM (checkObligations solver) solver_states
    let verified = all isJust proof_list
    if verified then
        verifyLoop solver pairs new_obligations b1' b2' config
    else
        return $ S.SAT ()
  -- | states1 == [], states2 == [] = return (S.UNSAT ())
  -- | otherwise = return (S.SAT ())
  | otherwise = return $ S.UNSAT ()

-- TODO get the obligations in here
-- the hash set input is for the assumptions
verifyLoop' :: S.Solver solver =>
               solver ->
               State () ->
               State () ->
               HS.HashSet (Expr, Expr) ->
               IO (Maybe [(State (), State ())])
verifyLoop' solver s1 s2 assumption_set = do
  let obligation_set = getObligations s1 s2
      obligation_list = HS.toList obligation_set
      (ready, not_ready) = partition (exprPairReadyForSolver (expr_env s1, expr_env s2)) obligation_list
      ready_hs = HS.fromList ready
  print "---"
  print assumption_set
  print ready
  print not_ready
  print "---"
  res <- checkObligations solver s1 s2 assumption_set ready_hs
  let {- ng1 = name_gen b1
      ng2 = name_gen b2
      (n1, ng1') = N.freshName ng1
      (n2, ng2') = N.freshName ng2
      b1' = b1 { name_gen = ng1' }
      b2' = b2 { name_gen = ng2' }
      -}
      currExprWrap e = CurrExpr Evaluate e
      currExprInsert s e = s { curr_expr = currExprWrap (caseWrap e) }
  case res of
      S.UNSAT () -> return $ Just [(currExprInsert s1 e1, currExprInsert s2 e2) | (e1, e2) <- not_ready]
      _ -> return Nothing

getObligations :: State () -> State () -> HS.HashSet (Expr, Expr)
getObligations s1 s2 =
  let CurrExpr _ e1 = curr_expr s1
      CurrExpr _ e2 = curr_expr s2
  in case proofObligations s1 s2 e1 e2 of
      Nothing -> error "TODO expressions not equivalent"
      Just po -> po

-- TODO added Bindings argument
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

caseWrap :: Expr -> Expr
caseWrap e =
  let matchId = Id (Name "caseWrap" Nothing 0 Nothing) (typeOf e) in
  Case e matchId [Alt Default (Var matchId)]
