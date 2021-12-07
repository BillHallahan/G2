{-# LANGUAGE OverloadedStrings #-}

module G2.Equiv.Tactics
    ( StateH (..)
    , PrevMatch (..)
    , Marker (..)
    , ActMarker (..)
    , CoMarker (..)
    , IndMarker (..)
    , EqualMarker (..)
    , Side (..)
    , TacticResult (..)
    , Tactic (..)
    , isSWHNF
    , tryEquality
    , moreRestrictiveEqual
    , tryCoinduction
    , exprExtract
    , moreRestrictivePairAux
    , exprReadyForSolver
    , checkObligations
    , applySolver
    , backtrackOne
    , prevFiltered
    )
    where

-- TODO may not need all imports

import G2.Language

import G2.Config

import G2.Interface

import qualified Control.Monad.State.Lazy as CM

import qualified G2.Language.ExprEnv as E
import qualified G2.Language.Typing as T

import Data.List
import Data.Maybe
import Data.Tuple
import qualified Data.Sequence as DS

import qualified Data.HashSet as HS
import qualified G2.Solver as S

import qualified G2.Language.PathConds as P

import G2.Equiv.InitRewrite
import G2.Equiv.EquivADT
import G2.Equiv.G2Calls

import qualified Data.HashMap.Lazy as HM
import qualified Data.Map as M
import G2.Execution.Memory
import Data.Monoid (Any (..))

import Debug.Trace

import G2.Execution.NormalForms
import Control.Monad

import Data.Time

import G2.Execution.Reducer
import G2.Lib.Printers

import qualified Control.Monad.Writer.Lazy as W

data StateH = StateH {
    latest :: StateET
  , history :: [StateET]
  , inductions :: [IndMarker]
  , discharge :: Maybe StateET
}

instance Named StateH where
  names (StateH s h ims d) =
    names s DS.>< names h DS.>< names ims DS.>< names d
  rename old new (StateH s h ims d) =
    StateH (rename old new s) (rename old new h) (rename old new ims) (rename old new d)

-- The container field is only relevant for induction.  When the expression for
-- one past state is actually an inner scrutinee of an expression that really
-- was encountered in the past, the container holds the full expression.
data PrevMatch t = PrevMatch {
    present :: (State t, State t)
  , past :: (State t, State t)
  , conditions :: (HM.HashMap Id Expr, HS.HashSet (Expr, Expr))
  , container :: State t
}

data ActMarker = Induction IndMarker
               | Coinduction CoMarker
               | Equality EqualMarker
               | NoObligations (StateET, StateET)
               | NotEquivalent (StateET, StateET)
               | SolverFail (StateET, StateET)

instance Named ActMarker where
  names (Induction im) = names im
  names (Coinduction cm) = names cm
  names (Equality em) = names em
  names (NoObligations s_pair) = names s_pair
  names (NotEquivalent s_pair) = names s_pair
  names (SolverFail s_pair) = names s_pair
  rename old new m = case m of
    Induction im -> Induction $ rename old new im
    Coinduction cm -> Coinduction $ rename old new cm
    Equality em -> Equality $ rename old new em
    NoObligations s_pair -> NoObligations $ rename old new s_pair
    NotEquivalent s_pair -> NotEquivalent $ rename old new s_pair
    SolverFail s_pair -> SolverFail $ rename old new s_pair

data Marker = Marker (StateH, StateH) ActMarker

instance Named Marker where
  names (Marker (sh1, sh2) m) =
    names sh1 DS.>< names sh2 DS.>< names m
  rename old new (Marker (sh1, sh2) m) =
    Marker (rename old new sh1, rename old new sh2) $ rename old new m

data Side = ILeft | IRight deriving (Show)

data IndMarker = IndMarker {
    ind_real_present :: (StateET, StateET)
  , ind_used_present :: (StateET, StateET)
  , ind_past :: (StateET, StateET)
  , ind_result :: (StateET, StateET)
  , ind_present_scrutinees :: (Expr, Expr)
  , ind_past_scrutinees :: (StateET, StateET)
  , ind_side :: Side
  , ind_fresh_name :: Name
}

-- TODO shouldn't need present scrutinees
instance Named IndMarker where
  names im =
    let (s1, s2) = ind_real_present im
        (q1, q2) = ind_used_present im
        (p1, p2) = ind_past im
        (s1', s2') = ind_result im
        (r1, r2) = ind_past_scrutinees im
        states = [s1, s2, q1, q2, p1, p2, s1', s2', r1, r2]
    in foldr (DS.><) DS.empty $ map names states
  rename old new im =
    let r = rename old new
    in im {
      ind_real_present = r $ ind_real_present im
    , ind_used_present = r $ ind_used_present im
    , ind_past = r $ ind_past im
    , ind_result = r $ ind_result im
    , ind_present_scrutinees = rename old new $ ind_present_scrutinees im
    , ind_past_scrutinees = r $ ind_past_scrutinees im
    , ind_fresh_name = rename old new $ ind_fresh_name im
    }

data CoMarker = CoMarker {
    co_real_present :: (StateET, StateET)
  , co_used_present :: (StateET, StateET)
  , co_past :: (StateET, StateET)
}

-- TODO remove duplicates?
instance Named CoMarker where
  names (CoMarker (s1, s2) (q1, q2) (p1, p2)) =
    foldr (DS.><) DS.empty $ map names [s1, s2, q1, q2, p1, p2]
  rename old new (CoMarker (s1, s2) (q1, q2) (p1, p2)) =
    let r = rename old new
        s1' = r s1
        s2' = r s2
        q1' = r q1
        q2' = r q2
        p1' = r p1
        p2' = r p2
    in CoMarker (s1', s2') (q1', q2') (p1', p2')

data EqualMarker = EqualMarker {
    eq_real_present :: (StateET, StateET)
  , eq_used_present :: (StateET, StateET)
}

instance Named EqualMarker where
  names (EqualMarker (s1, s2) (q1, q2)) =
    foldr (DS.><) DS.empty $ map names [s1, s2, q1, q2]
  rename old new (EqualMarker (s1, s2) (q1, q2)) =
    let r = rename old new
        s1' = r s1
        s2' = r s2
        q1' = r q1
        q2' = r q2
    in EqualMarker (s1', s2') (q1', q2')

-- TODO add debug info with these?
data TacticResult = Success (Maybe (Int, Int, StateET, StateET))
                  | NoProof

-- this takes a list of fresh names as input
-- equality and coinduction don't need them
-- induction just needs one
type Tactic s = s ->
                HS.HashSet Name ->
                [Name] ->
                (StateH, StateH) ->
                (StateET, StateET) ->
                W.WriterT [Marker] IO TacticResult

-- TODO not used?
reverseCoMarker :: CoMarker -> CoMarker
reverseCoMarker (CoMarker (s1, s2) (q1, q2) (p1, p2)) =
  CoMarker (s2, s1) (q2, q1) (p2, p1)

andM :: Monad m => m Bool -> m Bool -> m Bool
andM = liftM2 (&&)

stripTicks :: Expr -> Expr
stripTicks (Tick _ e) = e
stripTicks e = e

exprReadyForSolver :: ExprEnv -> Expr -> Bool
exprReadyForSolver h (Tick _ e) = exprReadyForSolver h e
exprReadyForSolver h (Var i) = E.isSymbolic (idName i) h && T.isPrimType (typeOf i)
exprReadyForSolver h (App f a) = exprReadyForSolver h f && exprReadyForSolver h a
exprReadyForSolver _ (Prim _ _) = True
exprReadyForSolver _ (Lit _) = True
exprReadyForSolver _ _ = False

exprExtract :: State t -> Expr
exprExtract (State { curr_expr = CurrExpr _ e }) = e

-- A Var counts as being in EVF if it's symbolic or if it's unmapped.
-- TODO remove ticks recursively?
isSWHNF :: State t -> Bool
isSWHNF (State { expr_env = h, curr_expr = CurrExpr _ e }) =
  let e' = modifyASTs stripTicks e
  in case e' of
    Var _ -> isPrimType (typeOf e') && isExprValueForm h e'
    _ -> isExprValueForm h e'

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

prevFull :: (StateH, StateH) -> [(StateET, StateET)]
prevFull (sh1, sh2) = [(p1, p2) | p1 <- history sh1, p2 <- history sh2]

-- The conditions for expr-value form do not align exactly with SWHNF.
-- A symbolic variable is in SWHNF only if it is of primitive type.
prevFiltered :: (StateH, StateH) -> [(StateET, StateET)]
prevFiltered =
  let neitherSWHNF (s1, s2) = not (isSWHNF s1 || isSWHNF s2)
  in (filter neitherSWHNF) . prevFull

-- s1 is old state, s2 is new state
-- only apply to old-new state pairs for which moreRestrictive works
moreRestrictivePC :: S.Solver solver =>
                     solver ->
                     StateET ->
                     StateET ->
                     HM.HashMap Id Expr ->
                     W.WriterT [Marker] IO Bool
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
         then W.liftIO $ applySolver solver (P.insert neg_conj P.empty) s1 s2
         else W.liftIO $ applySolver solver (P.insert neg_imp P.empty) s1 s2
  case res of
    S.UNSAT () -> return True
    _ -> return False

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
                 --trace ("INLINE L " ++ show i ++ show e) $
                 moreRestrictive s1 s2 ns hm ((m, e2):n1) n2 e e2
    (_, Var i) | m <- idName i
               , not $ E.isSymbolic m h2
               , not $ HS.member m ns
               , not $ (m, e1) `elem` n2
               , Just e <- E.lookup m h2 ->
                 --trace ("INLINE R " ++ show i ++ show e) $
                 moreRestrictive s1 s2 ns hm n1 ((m, e1):n2) e1 e
    (Var i1, Var i2) | HS.member (idName i1) ns
                     , idName i1 == idName i2 -> Just hm
                     | HS.member (idName i1) ns -> {-trace ("VLeft " ++ show (i1, i2))-} Nothing
                     | HS.member (idName i2) ns -> {-trace ("VRight " ++ show (i1, i2))-} Nothing
    (Var i, _) | E.isSymbolic (idName i) h1
               , (hm', hs) <- hm
               , Nothing <- HM.lookup i hm' -> Just (HM.insert i (inlineEquiv [] h2 ns e2) hm', hs)
               | E.isSymbolic (idName i) h1
               , Just e <- HM.lookup i (fst hm)
               , e == inlineEquiv [] h2 ns e2 -> Just hm
               -- this last case means there's a mismatch
               | E.isSymbolic (idName i) h1 -> {-trace ("VSymLeft " ++ show i)-} Nothing
               | not $ (idName i, e2) `elem` n1
               , not $ HS.member (idName i) ns -> error $ "unmapped variable " ++ (show i)
    (_, Var i) | E.isSymbolic (idName i) h2 -> {-trace ("VSymRight " ++ show i)-} Nothing -- sym replaces non-sym
               | not $ (idName i, e1) `elem` n2
               , not $ HS.member (idName i) ns -> error $ "unmapped variable " ++ (show i)
    (App f1 a1, App f2 a2) | Just hm_f <- {-trace ("APP FN " ++ show (printHaskellDirty e1) ++ "\n" ++ show (printHaskellDirty e2))-} moreRestrictive s1 s2 ns hm n1 n2 f1 f2
                           , Just hm_a <- {-trace ("APP ARG " ++ show hm_f ++ "\n" ++ show (printHaskellDirty a1) ++ "\n" ++ show (printHaskellDirty a2))-} moreRestrictive s1 s2 ns hm_f n1 n2 a1 a2 -> Just hm_a
    -- TODO ignoring lam use; these are never used seemingly
    -- TODO shouldn't lead to non-termination
    {-
    (App (Lam _ i b) a, _) -> let e1' = replaceASTs (Var i) a b
                              in trace ("LAM L" ++ show i) $ moreRestrictive s1 s2 ns hm n1 n2 e1' e2
    (_, App (Lam _ i b) a) -> let e2' = replaceASTs (Var i) a b
                              in trace ("LAM R" ++ show i) $ moreRestrictive s1 s2 ns hm n1 n2 e1 e2'
    -}
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
-- TODO remove ticks with this?
inlineTop :: [Name] -> ExprEnv -> Expr -> Expr
inlineTop acc h v@(Var (Id n _))
    | n `elem` acc = v
    | E.isSymbolic n h = v
    | Just e <- E.lookup n h = inlineTop (n:acc) h e
inlineTop acc h (Tick _ e) = inlineTop acc h e
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

validMap :: State t -> State t -> HM.HashMap Id Expr -> Bool
validMap s1 s2 hm =
  let hm_list = HM.toList hm
      check (_, e) = (not $ isSWHNF $ s1 { curr_expr = CurrExpr Evaluate e })
                  || (not $ isSWHNF $ s2 { curr_expr = CurrExpr Evaluate e })
                  || isPrimType (typeOf e)
  in foldr (&&) True (map check hm_list)

restrictHelper :: StateET ->
                  StateET ->
                  HS.HashSet Name ->
                  Maybe (HM.HashMap Id Expr, HS.HashSet (Expr, Expr)) ->
                  Maybe (HM.HashMap Id Expr, HS.HashSet (Expr, Expr))
restrictHelper s1 s2 ns hm_hs = case restrictAux s1 s2 ns hm_hs of
  Nothing -> Nothing
  Just (hm, hs) -> if validMap s1 s2 hm then Just (hm, hs) else Nothing

restrictAux :: StateET ->
               StateET ->
               HS.HashSet Name ->
               Maybe (HM.HashMap Id Expr, HS.HashSet (Expr, Expr)) ->
               Maybe (HM.HashMap Id Expr, HS.HashSet (Expr, Expr))
restrictAux _ _ _ Nothing = Nothing
restrictAux s1 s2 ns (Just hm) =
  moreRestrictive s1 s2 ns hm [] [] (exprExtract s1) (exprExtract s2)

syncSymbolic :: StateET -> StateET -> (StateET, StateET)
syncSymbolic s1 s2 =
  let f (E.SymbObj _) e2 = e2
      f e1 _ = e1
      h1 = E.unionWith f (expr_env s1) (expr_env s2)
      h2 = E.unionWith f (expr_env s2) (expr_env s1)
  in (s1 { expr_env = h1 }, s2 { expr_env = h2 })

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
                    IO (S.Result () ())
checkObligations solver s1 s2 obligation_set | not $ HS.null obligation_set =
    case obligationWrap $ modifyASTs stripTicks obligation_set of
        Nothing -> applySolver solver P.empty s1 s2
        Just allPO -> applySolver solver (P.insert allPO P.empty) s1 s2
  | otherwise = return $ S.UNSAT ()

-- shortcut:  don't invoke Z3 if there are no path conds
applySolver :: S.Solver solver =>
               solver ->
               PathConds ->
               StateET ->
               StateET ->
               IO (S.Result () ())
applySolver solver extraPC s1 s2 =
    let unionEnv = E.union (expr_env s1) (expr_env s2)
        rightPC = P.toList $ path_conds s2
        unionPC = foldr P.insert (path_conds s1) rightPC
        allPC = foldr P.insert unionPC (P.toList extraPC)
        -- TODO what if I use extraPC here instead of allPC?
        newState = s1 { expr_env = unionEnv, path_conds = extraPC }
    in case (P.toList allPC) of
      [] -> return $ S.SAT ()
      _ -> trace ("APPLY SOLVER " ++ (show $ folder_name $ track s1)) $
           trace (show $ P.number $ path_conds s1) $
           trace (show $ folder_name $ track s2) $
           trace (show $ P.number $ path_conds s2) $
           S.check solver newState allPC

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
                          [(StateET, StateET, StateET)] ->
                          (StateET, StateET) ->
                          W.WriterT [Marker] IO (Maybe (PrevMatch EquivTracker))
moreRestrictivePairAux solver ns prev (s1, s2) = do
  let (s1', s2') = syncSymbolic s1 s2
      mr (p1, p2, _) = restrictHelper p2 s2' ns $
                       restrictHelper p1 s1' ns (Just (HM.empty, HS.empty))
      rfs h e = (exprReadyForSolver h e) && (T.isPrimType $ typeOf e)
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
  res_list <- W.liftIO $ mapM (checkObligations solver s1 s2) obs_sets'
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
                       [(StateET, StateET)] ->
                       (StateET, StateET) ->
                       W.WriterT [Marker] IO (Maybe (PrevMatch EquivTracker))
moreRestrictivePair solver ns prev (s1, s2) =
  let prev' = map (\(p1, p2) -> (p1, p2, p2)) prev
  in moreRestrictivePairAux solver ns prev' (s1, s2)

-- TODO tick adjusting here?
isIdentity :: (Id, Expr) -> Bool
isIdentity (i1, Tick _ e2) = isIdentity (i1, e2)
isIdentity (i1, (Var i2)) = i1 == i2
isIdentity _ = False

-- approximation should be the identity map
-- needs to be enforced, won't just happen naturally
moreRestrictiveEqual :: S.Solver solver =>
                        solver ->
                        HS.HashSet Name ->
                        StateET ->
                        StateET ->
                        W.WriterT [Marker] IO (Maybe (PrevMatch EquivTracker))
moreRestrictiveEqual solver ns s1 s2 = do
  let h1 = expr_env s1
      h2 = expr_env s2
      s1' = s1 { expr_env = E.union h1 h2 }
      s2' = s2 { expr_env = E.union h2 h1 }
  pm_maybe <- moreRestrictivePair solver ns [(s2', s1')] (s1, s2)
  case pm_maybe of
    Nothing -> return Nothing
    Just (PrevMatch _ _ (hm, _) _) ->
      if foldr (&&) True (map isIdentity $ HM.toList hm)
      then return pm_maybe
      else return Nothing

-- This attempts to find a pair of equal expressions between the left and right
-- sides.  The state used for the left side stays constant, but the recursion
-- iterates through all of the states in the right side's history.
equalFoldL :: S.Solver solver =>
              solver ->
              HS.HashSet Name ->
              [StateET] ->
              StateET ->
              W.WriterT [Marker] IO (Maybe (PrevMatch EquivTracker))
equalFoldL solver ns prev2 s1 = do
  case prev2 of
    [] -> return Nothing
    p2:t -> do
      mre <- moreRestrictiveEqual solver ns s1 p2
      case mre of
        Just pm -> return $ Just pm
        _ -> equalFoldL solver ns t s1

-- TODO clean up code
-- This tries all of the allowable combinations for equality checking.  First
-- it tries matching the left-hand present state with all of the previously
-- encountered right-hand states.  If all of those fail, it tries matching the
-- right-hand present state with all of the previously encountered left-hand
-- states.
equalFold :: S.Solver solver =>
             solver ->
             HS.HashSet Name ->
             (StateH, StateH) ->
             (StateET, StateET) ->
             W.WriterT [Marker] IO (Maybe (PrevMatch EquivTracker, Side))
equalFold solver ns (sh1, sh2) (s1, s2) = do
  pm_l <- equalFoldL solver ns (s2:history sh2) s1
  case pm_l of
    Just pm -> return $ Just (pm, ILeft)
    _ -> do
      pm_r <- equalFoldL solver ns (s1:history sh1) s2
      case pm_r of
        Just pm' -> return $ Just (pm', IRight)
        _ -> return Nothing

{-
tryEquality :: S.Solver solver =>
               solver ->
               HS.HashSet Name ->
               (StateH, StateH) ->
               (StateET, StateET) ->
               W.WriterT [Marker] IO (Maybe (PrevMatch EquivTracker))
tryEquality solver ns sh_pair (s1, s2) = do
  res <- equalFold solver ns sh_pair (s1, s2)
  case res of
    Just (pm, sd) -> do
      let (q1, q2) = case sd of
                       ILeft -> present pm
                       IRight -> swap $ present pm
      W.tell $ [Marker sh_pair $ Equality $ EqualMarker (s1, s2) (q1, q2)]
      return $ Just pm
    _ -> return Nothing
-}

tryEquality :: S.Solver s => Tactic s
tryEquality solver ns _ sh_pair (s1, s2) = do
  res <- equalFold solver ns sh_pair (s1, s2)
  case res of
    Just (pm, sd) -> do
      let (q1, q2) = case sd of
                       ILeft -> present pm
                       IRight -> swap $ present pm
      W.tell $ [Marker sh_pair $ Equality $ EqualMarker (s1, s2) (q1, q2)]
      return $ Success Nothing
    _ -> return NoProof

backtrackOne :: StateH -> StateH
backtrackOne sh =
  case history sh of
    [] -> error "No Backtrack Possible"
    h:t -> sh {
        latest = h
      , history = t
      }

-- This attempts to find a past-present combination that works for coinduction.
-- The left-hand present state stays fixed, but the recursion iterates through
-- all of the possible options for the right-hand present state.
coinductionFoldL :: S.Solver solver =>
                    solver ->
                    HS.HashSet Name ->
                    (StateH, StateH) ->
                    (StateET, StateET) ->
                    W.WriterT [Marker] IO (Maybe (PrevMatch EquivTracker))
coinductionFoldL solver ns (sh1, sh2) (s1, s2) = do
  let prev = prevFiltered (sh1, sh2)
  res <- moreRestrictivePair solver ns prev (s1, s2)
  case res of
    Just _ -> return res
    _ -> case history sh2 of
      [] -> return Nothing
      p2:_ -> coinductionFoldL solver ns (sh1, backtrackOne sh2) (s1, p2)

{-
tryCoinduction :: S.Solver solver =>
                  solver ->
                  HS.HashSet Name ->
                  (StateH, StateH) ->
                  (StateET, StateET) ->
                  W.WriterT [Marker] IO (Maybe (PrevMatch EquivTracker))
tryCoinduction solver ns (sh1, sh2) (s1, s2) = do
  res_l <- coinductionFoldL solver ns (sh1, sh2) (s1, s2)
  case res_l of
    Just pm -> do
      let cml = CoMarker {
        co_real_present = (s1, s2)
      , co_used_present = present pm
      , co_past = past pm
      }
      W.tell [Marker (sh1, sh2) $ Coinduction cml]
      return res_l
    _ -> do
      res_r <- coinductionFoldL solver ns (sh2, sh1) (s2, s1)
      case res_r of
        Just pm' -> do
          let cmr = CoMarker {
            co_real_present = (s2, s1)
          , co_used_present = present pm'
          , co_past = past pm'
          }
          W.tell [Marker (sh1, sh2) $ Coinduction $ reverseCoMarker cmr]
          return res_r
        _ -> return Nothing
-}

tryCoinduction :: S.Solver s => Tactic s
tryCoinduction solver ns _ (sh1, sh2) (s1, s2) = do
  res_l <- coinductionFoldL solver ns (sh1, sh2) (s1, s2)
  case res_l of
    Just pm -> do
      let cml = CoMarker {
        co_real_present = (s1, s2)
      , co_used_present = present pm
      , co_past = past pm
      }
      W.tell [Marker (sh1, sh2) $ Coinduction cml]
      return $ Success Nothing
    _ -> do
      res_r <- coinductionFoldL solver ns (sh2, sh1) (s2, s1)
      case res_r of
        Just pm' -> do
          let cmr = CoMarker {
            co_real_present = (s2, s1)
          , co_used_present = present pm'
          , co_past = past pm'
          }
          W.tell [Marker (sh1, sh2) $ Coinduction $ reverseCoMarker cmr]
          return $ Success Nothing
        _ -> return NoProof
