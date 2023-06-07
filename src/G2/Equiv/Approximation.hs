module G2.Equiv.Approximation where

import G2.Equiv.Types
import G2.Language
import qualified G2.Language.Approximation as A
import qualified G2.Language.ExprEnv as E

import qualified Data.HashSet as HS
import qualified Data.HashMap.Lazy as HM
import Data.List
import Data.Maybe

moreRestrictive :: StateET
                -> StateET
                -> HS.HashSet Name
                -> (HM.HashMap Id Expr, HS.HashSet (Expr, Expr))
                -> Either [Lemma] (HM.HashMap Id Expr, HS.HashSet (Expr, Expr))
moreRestrictive s1 s2 =
    let
        lkp n s = lookupConcOrSymBoth n (expr_env s) (opp_env $ track s)
    in
    A.moreRestrictive moreRestrictiveCont generateLemma lkp s1 s2

moreRestrictiveCont :: StateET
                    -> StateET
                    -> HS.HashSet Name
                    -> (HM.HashMap Id Expr, HS.HashSet (Expr, Expr))
                    -> Bool -- ^ indicates whether this is part of the "active expression"
                    -> [(Name, Expr)] -- ^ variables inlined previously on the LHS
                    -> [(Name, Expr)] -- ^ variables inlined previously on the RHS
                    -> Expr
                    -> Expr
                    -> Either [Lemma] (HM.HashMap Id Expr, HS.HashSet (Expr, Expr))
moreRestrictiveCont s1 s2 ns hm active n1 n2 e1 e2 =
    let
        lkp n s = lookupConcOrSymBoth n (expr_env s) (opp_env $ track s)
    in
    case (e1, e2) of
        (Tick t1 e1', Tick t2 e2') | labeledErrorName t1 == labeledErrorName t2 ->
              A.moreRestrictive' moreRestrictiveCont generateLemma lkp s1 s2 ns hm active n1 n2 e1' e2'
        (Tick t e1', _) | isNothing $ labeledErrorName t ->
              A.moreRestrictive' moreRestrictiveCont generateLemma lkp s1 s2 ns hm active n1 n2 e1' e2
        (_, Tick t e2') | isNothing $ labeledErrorName t ->
              A.moreRestrictive' moreRestrictiveCont generateLemma lkp s1 s2 ns hm active n1 n2 e1 e2'
        _ -> Left []

-- When we make the two sides for a new lemma, if the two expressions
-- contain any variables that aren't present in the expression environment,
-- we add them to the expression environment as non-total symbolic
-- variables.  This can happen if an expression for a lemma is a
-- sub-expression of a Case branch, a Let statement, or a lambda expression
-- body.  It is possible that we may lose information about the variables
-- because of these insertions, but this cannot lead to spurious
-- counterexamples because these insertions apply only to lemmas and lemmas
-- are not used for counterexample generation.
generateLemma :: A.GenerateLemma EquivTracker Lemma
generateLemma s1 s2@(State {expr_env = h2}) hm e1 e2 =
      let
        h2' = opp_env $ track s2

        v_rep = HM.toList $ fst hm
        e1' = replaceVars e1 v_rep
        cs (E.Conc e_) = E.Conc e_
        cs (E.Sym i_) = case E.lookupConcOrSym (idName i_) h2' of
          Nothing -> E.Sym i_
          Just c -> c
        h2_ = envMerge (E.mapConcOrSym cs h2) h2'
        h2_' = E.mapConc (flip replaceVars v_rep) h2_
        et' = (track s2) { opp_env = E.empty }
        ids1 = varIds e1'
        ids1' = filter (\(Id n _) -> not $ E.member n h2_') ids1
        ids2 = varIds e2
        ids2' = filter (\(Id n _) -> not $ E.member n h2_) ids2
        ids_both = nub $ ids1' ++ ids2'
        h_lem1 = foldr E.insertSymbolic h2_' ids_both
        h_lem2 = foldr E.insertSymbolic h2_ ids_both
        ls1 = s2 { expr_env = h_lem1, curr_expr = CurrExpr Evaluate e1', track = et' }
        ls2 = s2 { expr_env = h_lem2, curr_expr = CurrExpr Evaluate e2, track = et' }
    in
    mkProposedLemma "lemma" s1 s2 ls2 ls1

replaceVars :: Expr -> [(Id, Expr)] -> Expr
replaceVars = foldr (\(Id n _, e) -> replaceVar n e)

mkProposedLemma :: String
                -> StateET
                -> StateET
                -> StateET
                -> StateET
                -> ProposedLemma
mkProposedLemma lm_name or_s1 or_s2 s1 s2 =
    let h1 = expr_env s1
        h2 = expr_env s2
        cs _ (E.Conc e) = E.Conc e
        cs h (E.Sym i) = case E.lookupConcOrSym (idName i) h of
          Nothing -> E.Sym i
          Just c -> c
        h1' = E.mapConcOrSym (cs h2) h1
        h2' = E.mapConcOrSym (cs h1) h2
        f (E.SymbObj _) e2 = e2
        f e1 _ = e1
        h1'' = E.unionWith f h1' h2'
        h2'' = E.unionWith f h2' h1'
        s1' = s1 { expr_env = h1'' }
        s2' = s2 { expr_env = h2'' }
    in
        Lemma { lemma_name = lm_name
              , lemma_lhs = s1'
              , lemma_rhs = s2'
              , lemma_lhs_origin = folder_name . track $ or_s1
              , lemma_rhs_origin = folder_name . track $ or_s2
              , lemma_to_be_proven  =[(newStateH s1', newStateH s2')] }

syncEnvs :: StateET -> StateET -> (StateET, StateET)
syncEnvs s1 s2 =
  let h1 = envMerge (expr_env s1) (expr_env s2)
      h2 = envMerge (expr_env s2) (expr_env s1)
  in (s1 { expr_env = h1 }, s2 { expr_env = h2 })

-- the left one takes precedence
envMerge :: ExprEnv -> ExprEnv -> ExprEnv
envMerge env h =
  let f (E.SymbObj _) e2 = e2
      f e1 _ = e1
  in E.unionWith f env h
