{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module G2.Equiv.Tactics
    ( module G2.Equiv.Types
    , TacticResult (..)
    , Tactic

    , Lemmas (..)

    , isSWHNF
    , tryEquality
    , moreRestrictiveEqual
    , tryCoinduction
    , checkObligations
    , LA.applySolver
    , backtrackOne
    , syncSymbolic
    , A.syncEnvs

    , emptyLemmas
    , insertProposedLemma
    , proposedLemmas
    , replaceProposedLemmas
    , insertProvenLemma
    , provenLemmas

    , disprovenLemmas
    , insertDisprovenLemma

    , A.mkProposedLemma
    , checkCycle
    )
    where

import G2.Language

import qualified Control.Monad.State.Lazy as CM

import qualified G2.Equiv.Approximation as A
import qualified G2.Language.Approximation as LA
import qualified G2.Language.ExprEnv as E
import G2.Language.Monad.AST
import qualified G2.Language.Typing as T

import Data.List
import Data.Maybe
import Data.Tuple
import qualified Data.HashSet as HS
import qualified G2.Solver as S

import qualified G2.Language.PathConds as P

import G2.Equiv.G2Calls
import G2.Equiv.Types

import Data.Either
import Data.Either.Extra
import qualified Data.HashMap.Lazy as HM
import Data.Monoid ((<>))

import G2.Execution.NormalForms
import Control.Monad.Extra

import qualified Control.Monad.Writer.Lazy as W

-- the Bool value for Failure is True if a cycle has been found
data TacticResult = Success
                  | NoProof [Lemma]
                  | Failure Bool

-- this takes a list of fresh names as input
-- equality and coinduction don't need them
-- induction just needs one
-- all tactics now take a lemma count
type Tactic s = s ->
                Int ->
                HS.HashSet Name ->
                Lemmas ->
                [Name] ->
                (StateH, StateH) ->
                (StateET, StateET) ->
                W.WriterT [Marker] IO TacticResult

validTotal :: StateET ->
              StateET ->
              HS.HashSet Name ->
              HM.HashMap Id Expr ->
              Bool
validTotal s1 s2 ns hm =
  let hm_list = HM.toList hm
      total_hs = total_vars $ track s1
      check (i, e) = (not $ (idName i) `elem` total_hs) || (totalExpr s2 ns [] e)
  in all check hm_list

validTypes :: HM.HashMap Id Expr -> Bool
validTypes hm = all (\((Id _ t), e) -> e T..:: t) $ HM.toList hm

restrictHelper :: StateET ->
                  StateET ->
                  HS.HashSet Name ->
                  Either [Lemma] (HM.HashMap Id Expr, HS.HashSet (Expr, Expr)) ->
                  Either [Lemma] (HM.HashMap Id Expr, HS.HashSet (Expr, Expr))
restrictHelper s1 s2 ns hm_hs =
    (\(hm, hs) -> if (validTotal s1 s2 ns hm) && (validTypes hm)
                              then Right (hm, hs)
                              else Left [])
    =<< A.moreRestrictive s1 s2 ns =<< hm_hs

syncSymbolic :: StateET -> StateET -> (StateET, StateET)
syncSymbolic s1 s2 =
  let et1 = (track s1) { opp_env = expr_env s2 }
      et2 = (track s2) { opp_env = expr_env s1 }
  in (s1 { track = et1 }, s2 { track = et2 })

obligationWrap :: HS.HashSet (Expr, Expr) -> Maybe PathCond
obligationWrap obligations =
    let obligation_list = HS.toList obligations
        eq_list = map (\(e1, e2) -> App (App (Prim Eq TyUnknown) e1) e2) obligation_list
        conj = foldr1 (\o1 o2 -> App (App (Prim And TyUnknown) o1) o2) eq_list
    in
    if null eq_list
    then Nothing
    else Just $ ExtCond (App (Prim Not TyUnknown) conj) True

checkObligations :: S.Solver solver =>
                    solver ->
                    StateET ->
                    StateET ->
                    HS.HashSet (Expr, Expr) ->
                    IO (S.Result () () ())
checkObligations solver s1 s2 obligation_set | not $ HS.null obligation_set =
    case obligationWrap $ modifyASTs stripTicks obligation_set of
        Nothing -> LA.applySolver solver P.empty s1 s2
        Just allPO -> LA.applySolver solver (P.insert allPO P.empty) s1 s2
  | otherwise = return $ S.UNSAT ()

-- extra filter on top of isJust for maybe_pairs
-- if restrictHelper end result is Just, try checking the corresponding PCs
-- for True output, there needs to be an entry for which that check succeeds
-- return the previous state pair that was used for the discharge
-- return Nothing if there was no discharge
-- if there are multiple, just return the first
-- first pair is "current," second pair is the match from the past
-- the third entry in a prev triple is the original for left or right
moreRestrictivePair :: S.Solver solver =>
                       solver ->
                       ((StateET, StateET) -> (StateET, StateET) -> Bool) ->
                       HS.HashSet Name ->
                       [(StateET, StateET)] ->
                       (StateET, StateET) ->
                        W.WriterT [Marker] IO (Either [Lemma] (PrevMatch EquivTracker))
moreRestrictivePair solver valid ns prev (s1, s2) | dc_path (track s1) == dc_path (track s2) = do
  let (s1', s2') = syncSymbolic s1 s2
      mr (p1, p2) =
          if valid (p1, p2) (s1', s2') then
            let hm_obs = let (p1', p2') = syncSymbolic p1 p2
                         in restrictHelper p2' s2' ns $
                         restrictHelper p1' s1' ns (Right (HM.empty, HS.empty))
                hm_obs_ = case hm_obs of
                  Left lems -> Left $ zip lems [1..length lems]
                  Right hmo -> Right hmo
            in
              mapLeft (fmap (\(l, i) -> l { lemma_name = "Lem" ++ show i
                                                  ++ " past_1 = " ++ folder p1
                                                  ++ " present_1 = " ++ folder s1
                                                  ++ " past_2 = " ++ folder p2
                                                  ++ " present_2 = " ++ folder s2  }))
            $ fmap (\hm_obs' -> PrevMatch (s1, s2) (p1, p2) hm_obs' p2) hm_obs_
          else Left []
      
      (possible_lemmas, possible_matches) = partitionEithers $ map mr prev

      folder = folder_name . track
      -- As a heuristic, take only lemmas where both sides are not in SWHNF
      possible_lemmas' = filter (\(Lemma { lemma_lhs = s1_, lemma_rhs = s2_ }) ->
                                              not (isSWHNF s1_)
                                           && not (isSWHNF s2_))
                       $ concat possible_lemmas

      mpc (PrevMatch _ (p1, p2) (hm, _) _) =
          andM [LA.moreRestrictivePC solver p1 s1 hm, LA.moreRestrictivePC solver p2 s2 hm]

  possible_matches' <- filterM mpc possible_matches
  -- check obligations individually rather than as one big group
  res_list <- W.liftIO (findM (\pm -> isUnsat =<< checkObligations solver s1 s2 (snd . conditions $ pm)) (possible_matches'))
  return $ maybe (Left possible_lemmas') Right res_list
  | otherwise = return $ Left []
  where
      isUnsat (S.UNSAT _) = return True
      isUnsat _ = return False

moreRestrictiveSingle :: S.Solver solver =>
                         solver ->
                         HS.HashSet Name ->
                         StateET ->
                         StateET ->
                         W.WriterT [Marker] IO (Either [Lemma] (HM.HashMap Id Expr))
moreRestrictiveSingle solver ns s1 s2 = do
    case restrictHelper s1 s2 ns $ Right (HM.empty, HS.empty) of
        (Left l) -> return $ Left l
        Right (hm, obs) -> do
            more_res_pc <- LA.moreRestrictivePC solver s1 s2 hm
            case more_res_pc of
                False -> return $ Left []
                True -> do
                    obs' <- W.liftIO (checkObligations solver s1 s2 obs)
                    case obs' of
                        S.UNSAT _ -> return (Right hm)
                        _ -> return $ Left []

-------------------------------------------------------------------------------
-- Equality
-------------------------------------------------------------------------------

-- approximation should be the identity map
-- needs to be enforced, won't just happen naturally
moreRestrictiveEqual :: S.Solver solver =>
                        solver ->
                        Int ->
                        HS.HashSet Name ->
                        Lemmas ->
                        StateET ->
                        StateET ->
                        W.WriterT [Marker] IO (Maybe (PrevMatch EquivTracker))
moreRestrictiveEqual solver num_lems ns lemmas s1 s2 = do
    let (s1', s2') = syncSymbolic s1 s2
    if dc_path (track s1') /= dc_path (track s2') then return Nothing
    else do
      -- no need to enforce dc path condition for this function
      pm_maybe <- moreRestrictivePairWithLemmasPast solver num_lems ns lemmas [(s2', s1')] (s1', s2')
      case pm_maybe of
        Left _ -> return Nothing
        Right (_, _, pm@(PrevMatch _ _ (hm, _) _)) ->
          if all isIdentity $ HM.toList hm
          then return $ Just pm
          else return Nothing
    where
        isIdentity :: (Id, Expr) -> Bool
        isIdentity (i1, Tick _ e2) = isIdentity (i1, e2)
        isIdentity (i1, (Var i2)) = i1 == i2
        isIdentity _ = False

-- This tries all of the allowable combinations for equality checking.  First
-- it tries matching the left-hand present state with all of the previously
-- encountered right-hand states.  If all of those fail, it tries matching the
-- right-hand present state with all of the previously encountered left-hand
-- states.
equalFold :: S.Solver solver =>
             solver ->
             Int ->
             HS.HashSet Name ->
             Lemmas ->
             (StateH, StateH) ->
             (StateET, StateET) ->
             W.WriterT [Marker] IO (Maybe (PrevMatch EquivTracker))
equalFold solver num_lems ns lemmas (sh1, sh2) (s1, s2) = do
  -- This attempts to find a pair of equal expressions between the left and right
  -- sides.  The state used for the left side stays constant, but the recursion
  -- iterates through all of the states in the right side's history.
  let equalFoldL s = firstJustM (moreRestrictiveEqual solver num_lems ns lemmas s)

  pm_l <- equalFoldL s1 (s2:history sh2)
  case pm_l of
    Just pm -> return $ Just pm
    _ -> do
      pm_r <- equalFoldL s2 (s1:history sh1)
      return $ fmap (\pm -> pm { present = swap $ present pm }) pm_r

tryEquality :: S.Solver s => Tactic s
tryEquality solver num_lems ns lemmas _ sh_pair (s1, s2) = do
  res <- equalFold solver num_lems ns lemmas sh_pair (s1, s2)
  case res of
    Just pm -> do
      W.tell $ [Marker sh_pair $ Equality $ EqualMarker (s1, s2) (present pm)]
      return Success
    _ -> return (NoProof [])

-------------------------------------------------------------------------------
-- Coinduction
-------------------------------------------------------------------------------

-- This attempts to find a past-present combination that works for coinduction.
-- The left-hand present state stays fixed, but the recursion iterates through
-- all of the possible options for the right-hand present state.
coinductionFoldL :: S.Solver solver =>
                    solver ->
                    Int ->
                    HS.HashSet Name ->
                    Lemmas ->
                    [Lemma] ->
                    (StateH, StateH) ->
                    (StateET, StateET) ->
                    W.WriterT [Marker] IO (Either [Lemma] ([(StateET, Lemma)], [(StateET, Lemma)], PrevMatch EquivTracker))
coinductionFoldL solver num_lems ns lemmas gen_lemmas (sh1, sh2) (s1, s2) = do
  let prev = [(p1, p2) | p1 <- history sh1, p2 <- history sh2]
  res <- moreRestrictivePairWithLemmasOnFuncApps solver num_lems validCoinduction ns lemmas prev (s1', s2')
  case res of
    Right _ -> return res
    Left new_lems -> backtrack new_lems
  where
      (s1', s2') = syncSymbolic s1 s2

      backtrack new_lems_ =
          case backtrackOne sh2 of
              Nothing -> return . Left $ new_lems_ ++ gen_lemmas
              Just sh2' -> coinductionFoldL solver num_lems ns lemmas
                                       (new_lems_ ++ gen_lemmas) (sh1, sh2') (s1, latest sh2')

validCoinduction :: (StateET, StateET) -> (StateET, StateET) -> Bool
validCoinduction (p1, p2) (q1, q2) =
  let dcp1 = dc_path $ track p1
      dcp2 = dc_path $ track p2
      dcq1 = dc_path $ track q1
      dcq2 = dc_path $ track q2
      consistent = dcp1 == dcp2 && dcq1 == dcq2
      unguarded = all (not . isSWHNF) [p1, p2, q1, q2]
      guarded = length dcp1 < length dcq1
  in consistent && (guarded || unguarded)

backtrackOne :: StateH -> Maybe StateH
backtrackOne sh =
  case history sh of
    [] -> Nothing
    h:t -> Just $ sh { latest = h
                     , history = t
                     }

tryCoinduction :: S.Solver s => Tactic s
tryCoinduction solver num_lems ns lemmas _ (sh1, sh2) (s1, s2) = do
  res_l <- coinductionFoldL solver num_lems ns lemmas [] (sh1, sh2) (s1, s2)
  case res_l of
    Right (lem_l, lem_r, pm) -> do
      let cml = CoMarker {
        co_real_present = (s1, s2)
      , co_used_present = present pm
      , co_past = past pm
      , lemma_used_left = lem_l
      , lemma_used_right = lem_r
      }
      W.tell [Marker (sh1, sh2) $ Coinduction cml]
      return Success
    Left l_lemmas -> do
      res_r <- coinductionFoldL solver num_lems ns lemmas [] (sh2, sh1) (s2, s1)
      case res_r of
        Right (lem_l, lem_r, pm) -> do
          let cmr = CoMarker {
            co_real_present = (s2, s1)
          , co_used_present = present pm
          , co_past = past pm
          , lemma_used_left = lem_l
          , lemma_used_right = lem_r
          }
          W.tell [Marker (sh1, sh2) $ Coinduction $ reverseCoMarker cmr]
          return Success
        Left r_lemmas -> return . NoProof $ l_lemmas ++ r_lemmas

-------------------------------------------------------------------------------
-- Lemmas
-------------------------------------------------------------------------------

data Lemmas = Lemmas { proposed_lemmas :: [ProposedLemma]
                     , proven_lemmas :: [ProvenLemma]
                     , disproven_lemmas :: [DisprovenLemma]}

emptyLemmas :: Lemmas
emptyLemmas = Lemmas [] [] []

insertProposedLemma :: S.Solver solver => solver -> HS.HashSet Name -> Lemma -> Lemmas -> W.WriterT [Marker] IO Lemmas
insertProposedLemma solver ns lem lems@(Lemmas { proposed_lemmas = prop_lems
                                               , proven_lemmas = proven_lems
                                               , disproven_lemmas = disproven_lems }) = do
    same_as_proposed <- equivLemma solver ns lem prop_lems
    implied_by_proven <- moreRestrictiveLemma solver ns lem proven_lems
    implies_disproven <- anyM (\dl -> moreRestrictiveLemma solver ns dl [lem]) disproven_lems
    case same_as_proposed || implied_by_proven || implies_disproven of
        True -> return lems
        False -> do
          W.tell [LMarker $ LemmaProposed lem]
          return lems { proposed_lemmas = lem:prop_lems }

proposedLemmas :: Lemmas -> [ProposedLemma]
proposedLemmas = proposed_lemmas

provenLemmas :: Lemmas -> [ProposedLemma]
provenLemmas = proven_lemmas

disprovenLemmas :: Lemmas -> [ProposedLemma]
disprovenLemmas = disproven_lemmas

replaceProposedLemmas :: [ProposedLemma] -> Lemmas -> Lemmas
replaceProposedLemmas pl lems = lems { proposed_lemmas = pl }

-- proactively confirm lemmas implied by this
-- this might be redundant with the verifier's work
insertProvenLemma :: S.Solver solver =>
                     solver
                  -> HS.HashSet Name
                  -> Lemmas
                  -> ProvenLemma
                  -> W.WriterT [Marker] IO Lemmas
insertProvenLemma solver ns lems lem = do
  W.tell [LMarker $ LemmaProven lem]
  let prop_lems = proposed_lemmas lems
  (extra_proven, still_prop) <- partitionM (\l -> moreRestrictiveLemma solver ns l [lem]) prop_lems
  W.tell $ map (\l -> LMarker $ LemmaProvenEarly (lem, l)) extra_proven
  return $ lems {
      proposed_lemmas = still_prop
    , proven_lemmas = lem:(extra_proven ++ proven_lemmas lems)
  }

-- remove lemmas that imply the disproven lemma
-- for every discarded lemma, add a marker
insertDisprovenLemma :: S.Solver solver =>
                        solver
                     -> HS.HashSet Name
                     -> Lemmas
                     -> DisprovenLemma
                     -> W.WriterT [Marker] IO Lemmas
insertDisprovenLemma solver ns lems lem = do
  W.tell [LMarker $ LemmaRejected lem]
  -- the one implied is the more specific one
  -- the one doing the implying is the more general one
  let prop_lems = proposed_lemmas lems
  (extra_disproven, still_prop) <- partitionM (\l -> moreRestrictiveLemma solver ns lem [l]) prop_lems
  W.tell $ map (\l -> LMarker $ LemmaRejectedEarly (lem, l)) extra_disproven
  return $ lems {
      proposed_lemmas = still_prop
    , disproven_lemmas = lem:(extra_disproven ++ disproven_lemmas lems)
  }

moreRestrictiveLemma :: S.Solver solver => solver -> HS.HashSet Name -> Lemma -> [Lemma] -> W.WriterT [Marker] IO Bool 
moreRestrictiveLemma solver ns (Lemma { lemma_lhs = l1_1, lemma_rhs = l1_2 }) lems = do
    mr <- moreRestrictivePair solver (\_ _ -> True) ns
                              (map (\(Lemma { lemma_lhs = l2_1, lemma_rhs = l2_2 }) -> (l2_1, l2_2)) lems)
                              (l1_1, l1_2)
    case mr of
        Left _ -> return False
        Right _ -> return True

equivLemma :: S.Solver solver => solver -> HS.HashSet Name -> Lemma -> [Lemma] -> W.WriterT [Marker] IO Bool 
equivLemma solver ns (Lemma { lemma_lhs = l1_1, lemma_rhs = l1_2 }) lems = do
    anyM (\(Lemma { lemma_lhs = l2_1, lemma_rhs = l2_2 }) -> do
                    mr1 <- moreRestrictivePair solver (\_ _ -> True) ns [(l2_1, l2_2)] (l1_1, l1_2)
                    mr2 <- moreRestrictivePair solver (\_ _ -> True) ns [(l1_1, l1_2)] (l2_1, l2_2)
                    case (mr1, mr2) of
                        (Right _, Right _) -> return True
                        _ -> return False) lems

-- TODO: Does substLemma need to do something more to check correctness of path constraints?
-- `substLemma state lemmas` tries to apply each proven lemma in `lemmas` to `state`.
-- In particular, for each `lemma = (lemma_l `equiv lemma_r` in the proven lemmas, it
-- searches for a subexpression `e'` of `state`'s current expression such that `e' <=_V lemma_l`.
-- If it find such a subexpression, it adds state[e'[V(x)/x]] to the returned
-- list of States.
substLemma :: S.Solver solver =>
              solver ->
              HS.HashSet Name ->
              StateET ->
              Lemmas ->
              W.WriterT [Marker] IO [(Lemma, StateET)]
substLemma solver ns s =
    mapMaybeM (\lem -> replaceMoreRestrictiveSubExpr solver ns lem s) . provenLemmas

-- int counter is a safeguard against divergence
-- optimization:  lemmas that go unused in one iteration are removed for
-- the next iteration; lost opportunities possible but not observed yet
substLemmaLoopAux :: S.Solver solver =>
                     Int ->
                     solver ->
                     HS.HashSet Name ->
                     Lemmas ->
                     [(Lemma, StateET)] ->
                     StateET ->
                     W.WriterT [Marker] IO [([(Lemma, StateET)], StateET)]
substLemmaLoopAux 0 _ _ _ _ _ =
    return []
substLemmaLoopAux i solver ns lems past_lems s = do
    lem_states <- substLemma solver ns s lems
    let lem_states' = map (\(l, s') -> ((l, s):past_lems, s')) lem_states
        lems_used = lems { proven_lemmas = nub $ map fst lem_states }
    lem_state_lists <- mapM (uncurry (substLemmaLoopAux (i - 1) solver ns lems_used)) lem_states'
    return $ lem_states' ++ concat lem_state_lists

substLemmaLoop :: S.Solver solver =>
                  Int ->
                  solver ->
                  HS.HashSet Name ->
                  StateET ->
                  Lemmas ->
                  W.WriterT [Marker] IO [([(Lemma, StateET)], StateET)]
substLemmaLoop i solver ns s lems = substLemmaLoopAux i solver ns lems [] s

replaceMoreRestrictiveSubExpr :: S.Solver solver =>
                                 solver ->
                                 HS.HashSet Name ->
                                 Lemma ->
                                 StateET ->
                                 W.WriterT [Marker] IO (Maybe (Lemma, StateET))
replaceMoreRestrictiveSubExpr solver ns lemma s@(State { curr_expr = CurrExpr er _ }) = do
    let sound = lemmaSound ns s lemma
    (e, replaced) <- CM.runStateT (replaceMoreRestrictiveSubExpr' solver ns lemma s sound $ getExpr s) Nothing
    case replaced of
      Nothing -> return Nothing
      Just new_vars -> let new_ids = map fst new_vars
                           h = foldr E.insertSymbolic (expr_env s) new_ids
                           new_total = map (idName . fst) $ filter snd new_vars
                           total' = foldr HS.insert (total_vars $ track s) new_total
                           track' = (track s) { total_vars = total' }
                           s' = s {
                             curr_expr = CurrExpr er e
                           , expr_env = h
                           , track = track'
                           }
                       in return $ Just (lemma, s')

{-
If a symbolic variable is on the RHS of a lemma but not the LHS, add it to the
expression environment of the state receiving the substitution.
No need to carry over concretized ones because of inlineEquiv.
Get all of the symbolic IDs that are not in v_rep from the lemma RHS.
Keep track of totality info for variables that get migrated.
If the variable is concrete in one location but symbolic in another, making the
substitution from the symbolic place to the concrete place is still valid.
If it's unmapped, put it in as symbolic.
If it's concrete or symbolic, just leave it as it is.
This implementation does not cover finiteness information.
The Bool argument of this function is used to determine whether a lemma
substitution can be applied soundly at the current location.  If an
expression is in FAF with no nested applications of the function at the
outermost layer, substitutions are sound.  Any sub-expression of an FAF
expression like this can also receive substitutions soundly.  If the
recursion has ever passed through a sub-expression that fits the FAF
format, then the Bool argument carries that information down to lower
recursive calls.
-}
replaceMoreRestrictiveSubExpr' :: S.Solver solver =>
                                  solver ->
                                  HS.HashSet Name ->
                                  Lemma ->
                                  StateET ->
                                  Bool ->
                                  Expr ->
                                  CM.StateT (Maybe [(Id, Bool)]) (W.WriterT [Marker] IO) Expr
replaceMoreRestrictiveSubExpr' solver ns lemma@(Lemma { lemma_lhs = lhs_s, lemma_rhs = rhs_s })
                                         s2 sound e = do
    replaced <- CM.get
    if isNothing replaced then do
        mr_sub <- CM.lift $ moreRestrictiveSingle solver ns lhs_s (s2 { curr_expr = CurrExpr Evaluate e })
        case mr_sub of
            Right hm -> do
                let v_rep = HM.toList hm
                    ids_l = E.symbolicIds $ opp_env $ track rhs_s
                    ids_r = E.symbolicIds $ expr_env rhs_s
                    ids_both = nub (ids_l ++ ids_r)
                    new_ids = filter (\(Id n _) -> not (E.member n (expr_env s2) || E.member n (opp_env $ track s2))) ids_both
                    new_info = map (\(Id n _) -> n `elem` (total_vars $ track rhs_s)) new_ids
                    
                    lkp n s = lookupConcOrSymBoth n (expr_env s) (opp_env $ track s)
                    rhs_e' = A.replaceVars (LA.inlineEquiv lkp rhs_s ns $ getExpr rhs_s) v_rep
                CM.put $ Just $ zip new_ids new_info
                return rhs_e'
            Left _ -> do
                let ns' = foldr HS.insert ns (bind e)
                    sound' = lemmaSound ns' s2 lemma
                modifyChildrenM (replaceMoreRestrictiveSubExpr' solver ns' lemma s2 (sound || sound')) e
    else return e
    where
        bind (Lam _ i _) = [idName i]
        bind (Case _ i _ as) = idName i:concatMap altBind as
        bind (Let b _) = map (idName . fst) b
        bind _ = []

        altBind (Alt (DataAlt _ is) _) = map idName is
        altBind _ = []

-- This is a looser version of the lemma soundness check from the paper.
-- Instead of checking that the expression receiving the substitution is
-- a suitable function application at the outermost level, we simply look
-- for a sub-expression that fits that mold.  Substitutions can only
-- happen within sub-expressions that satisfy the conditions.
-- This is still just as safe as the original soundness check.  The
-- original soundness check serves to prevent lemmas from reversing
-- evaluation steps so that a substitution does not trick Nebula into
-- thinking that it has reached a cycle when it has not.  If we confirm
-- that evaluation steps are not being reversed within a sub-expression,
-- that same guarantee should extend to the expression as a whole.
lemmaSound :: HS.HashSet Name -> StateET -> Lemma -> Bool
lemmaSound ns s lem =
  let lkp n s_ = lookupConcOrSymBoth n (expr_env s_) (opp_env $ track s_) in
  case unApp . modifyASTs stripTicks . LA.inlineEquiv lkp s ns $ getExpr s of
    Var (Id f _):_ ->
        let
            lem_vars = varNames $ LA.inlineEquiv lkp s ns $ getExpr (lemma_rhs lem)
        in
        not $ f `elem` lem_vars
    _ -> False

-- Tries to apply lemmas to expressions only in FAF form, and only if the function being applied can not be
-- called in any way by the lemma.
moreRestrictivePairWithLemmasOnFuncApps :: S.Solver solver =>
                                           solver ->
                                           Int ->
                                           ((StateET, StateET) -> (StateET, StateET) -> Bool) ->
                                           HS.HashSet Name ->
                                           Lemmas ->
                                           [(StateET, StateET)] ->
                                           (StateET, StateET) ->
                                           W.WriterT [Marker] IO (Either [Lemma] ([(StateET, Lemma)], [(StateET, Lemma)], PrevMatch EquivTracker))
moreRestrictivePairWithLemmasOnFuncApps solver num_lems valid ns =
    moreRestrictivePairWithLemmas solver num_lems valid ns

moreRestrictivePairWithLemmas :: S.Solver solver =>
                                 solver ->
                                 Int ->
                                 ((StateET, StateET) -> (StateET, StateET) -> Bool) ->
                                 HS.HashSet Name ->
                                 Lemmas ->
                                 [(StateET, StateET)] ->
                                 (StateET, StateET) ->
                                 W.WriterT [Marker] IO (Either [Lemma] ([(StateET, Lemma)], [(StateET, Lemma)], PrevMatch EquivTracker))
moreRestrictivePairWithLemmas solver num_lems valid ns lemmas past_list (s1, s2) = do
    let (s1', s2') = syncSymbolic s1 s2
    xs1 <- substLemmaLoop num_lems solver ns s1' lemmas
    xs2 <- substLemmaLoop num_lems solver ns s2' lemmas

    let xs1' = ([], s1'):xs1
        xs2' = ([], s2'):xs2
        pairs = [ (pair1, pair2) | pair1 <- xs1', pair2 <- xs2' ]

    rp <- mapM (\((l1, s1_), (l2, s2_)) -> do
            mrp <- moreRestrictivePair solver valid ns past_list (s1_, s2_)
            -- the underscore states here are ones with substs applied
            let l1' = map swap l1
            let l2' = map swap l2
            return $ fmap (l1', l2', ) mrp) pairs
    let (possible_lemmas, possible_matches) = partitionEithers rp

    case possible_matches of
        x:_ -> return $ Right x
        [] -> return . Left $ concat possible_lemmas

moreRestrictivePairWithLemmasPast :: S.Solver solver =>
                                     solver ->
                                     Int ->
                                     HS.HashSet Name ->
                                     Lemmas ->
                                     [(StateET, StateET)] ->
                                     (StateET, StateET) ->
                                     W.WriterT [Marker] IO (Either [Lemma] ([(StateET, Lemma)], [(StateET, Lemma)], PrevMatch EquivTracker))
moreRestrictivePairWithLemmasPast solver num_lems ns lemmas past_list s_pair = do
    let (past1, past2) = unzip past_list
    xs_past1 <- mapM (\(q1, _) -> substLemmaLoop num_lems solver ns q1 lemmas) past_list
    xs_past2 <- mapM (\(_, q2) -> substLemmaLoop num_lems solver ns q2 lemmas) past_list
    let plain_past1 = map (\s_ -> (Nothing, s_)) past1
        plain_past2 = map (\s_ -> (Nothing, s_)) past2
        xs_past1' = plain_past1 ++ (map (\(l, s) -> (Just l, s)) $ concat xs_past1)
        xs_past2' = plain_past2 ++ (map (\(l, s) -> (Just l, s)) $ concat xs_past2)
        pair_past (_, p1) (_, p2) = syncSymbolic p1 p2
        past_list' = [pair_past pair1 pair2 | pair1 <- xs_past1', pair2 <- xs_past2']
    moreRestrictivePairWithLemmas solver num_lems (\_ _ -> True) ns lemmas past_list' s_pair

-------------------------------------------------------------------------------
-- CounterExample Generation
-------------------------------------------------------------------------------

-- TODO incorporate lemmas into this?
checkCycle :: S.Solver s => Tactic s
checkCycle solver _ ns _ _ (sh1, sh2) (s1, s2) = do
  --W.liftIO $ putStrLn $ "Cycle?" ++ (folder_name $ track s1) ++ (folder_name $ track s2)
  let (s1', s2') = syncSymbolic s1 s2
      hist1 = filter (\p -> dc_path (track p) == dc_path (track s1')) $ history sh1
      hist2 = filter (\p -> dc_path (track p) == dc_path (track s2')) $ history sh2
      hist1' = zip hist1 (map expr_env hist2)
      hist2' = zip hist2 (map expr_env hist1)
  -- histories must have the same length and have matching entries
  mr1 <- mapM (\(p1, hp2) -> moreRestrictiveSingle solver ns s1' (p1 { track = (track p1) { opp_env = hp2 } })) hist1'
  mr2 <- mapM (\(p2, hp1) -> moreRestrictiveSingle solver ns s2' (p2 { track = (track p2) { opp_env = hp1 } })) hist2'
  let vh _ (Left _, _) = False
      vh s (Right hm, p) = validHigherOrder s p ns $ Right (hm, HS.empty)
      mr1_pairs = zip mr1 hist1
      mr1_pairs' = filter (vh s1') mr1_pairs
      mr1_pair = find (isRight . fst) mr1_pairs'
      mr2_pairs = zip mr2 hist2
      mr2_pairs' = filter (vh s2') mr2_pairs
      mr2_pair = find (isRight . fst) mr2_pairs'
  case (isSWHNF s1', isSWHNF s2', mr2_pair) of
    (True, False, Just (Right hm, p2)) -> do
      W.tell [Marker (sh1, sh2) $ CycleFound $ CycleMarker (s1, s2) p2 hm IRight]
      return $ Failure True
    _ -> case (isSWHNF s1', isSWHNF s2', mr1_pair) of
      (False, True, Just (Right hm, p1)) -> do
        W.tell [Marker (sh1, sh2) $ CycleFound $ CycleMarker (s1, s2) p1 hm ILeft]
        return $ Failure True
      _ -> return $ NoProof []

-- This function helps us to avoid certain spurious counterexamples when
-- dealing with symbolic functions.  Specifically, it detects apparent
-- counterexamples that are invalid because they map expressions with
-- differently-concretized symbolic function mappings to each other.
validHigherOrder :: StateET ->
                    StateET ->
                    HS.HashSet Name ->
                    Either [Lemma] (HM.HashMap Id Expr, HS.HashSet (Expr, Expr)) ->
                    Bool
validHigherOrder s1 s2 ns hm_hs | Right (hm, _) <- hm_hs =
  let -- empty these to avoid an infinite loop
      s1' = s1 { track = (track s1) { higher_order = HM.empty } }
      s2' = s2 { track = (track s2) { higher_order = HM.empty } }
      -- if the Id isn't present, the mapping isn't relevant
      mappings1 = HM.toList $ higher_order $ track s1
      mappings2 = HM.toList $ higher_order $ track s2
      old_pairs = filter (\(_, i) -> (E.member (idName i) (expr_env s1)) || (E.member (idName i) (opp_env $ track s1))) mappings1
      new_pairs = filter (\(_, i) -> (E.member (idName i) (expr_env s2)) || (E.member (idName i) (opp_env $ track s2))) mappings2
      old_states = map (\(e, i) -> (s1' { curr_expr = CurrExpr Evaluate e },
                                    s1' { curr_expr = CurrExpr Evaluate (Var i) })) old_pairs
      new_states = map (\(e, i) -> (s2' { curr_expr = CurrExpr Evaluate e },
                                    s2' { curr_expr = CurrExpr Evaluate (Var i) })) new_pairs
      zipped = [(p, q) | p <- old_states, q <- new_states]
      -- only current expressions change between all these states
      -- I can keep the other-side expr envs the same
      check ((p1, p2), (q1, q2)) =
        case restrictHelper p1 q1 ns hm_hs of
          Right (hm', hs') -> if HM.size hm' == HM.size hm
                              then restrictHelper p2 q2 ns (Right (hm', hs'))
                              else Right (hm', hs')
          _ -> hm_hs
  in all isRight $ map check zipped
  | otherwise = False
