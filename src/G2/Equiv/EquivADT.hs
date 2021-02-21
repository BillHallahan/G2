module G2.Equiv.EquivADT (proofObligations, assumptions, statePairing) where

import Data.List
import G2.Language
import qualified G2.Language.ExprEnv as E
-- TODO decide between lazy and strict
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import qualified G2.Language.Naming as N

-- TODO import for foldM
import Control.Monad

-- TODO states include lists of symbolic vars
proofObligations :: State t ->
                    State t ->
                    Expr ->
                    Expr ->
                    Bindings ->
                    Maybe (HS.HashSet (Expr, Expr))
-- get ExprEnv from both states
-- look up symbolic vars in the ExprEnv
-- check concretizations for each of them
proofObligations s1 s2 e1 e2 b =
  -- TODO need anything else from the state, or just ExprEnv?
  exprPairingWrapped s1 s2 e1 e2 b

-- TODO also add wrapping here
assumptions :: State t ->
               State t ->
               Expr ->
               Expr ->
               Maybe (HS.HashSet (Expr, Expr))
assumptions s1 s2 e1 e2 =
  exprPairing s1 s2 e1 e2 HS.empty

idPairing :: State t -> State t -> (Id, Id) -> Maybe (HS.HashSet (Expr, Expr))
idPairing s1 s2 (i1, i2) =
  assumptions s1 s2 (Var i1) (Var i2)

-- helper function for wrapping
-- the second function is the accumulator
wrapHelper :: (Expr, Expr) ->
              (HS.HashSet (Expr, Expr), N.NameGen) ->
              (HS.HashSet (Expr, Expr), N.NameGen)
wrapHelper (e1, e2) (hs, ng) =
  let (e1', ng') = caseWrap e1 ng
      (e2', ng'') = caseWrap e2 ng'
      hs' = HS.insert (e1', e2') hs
  in
  (hs', ng'')

-- iterate over all entries of the HashSet
-- wrap them and use the new NameGen for the next step
exprPairingWrapped :: State t ->
                      State t ->
                      Expr ->
                      Expr ->
                      Bindings ->
                      Maybe (HS.HashSet (Expr, Expr))
exprPairingWrapped s1 s2 e1 e2 b =
  let ep = exprPairing s1 s2 e1 e2 HS.empty
  in
  case ep of
    Nothing -> Nothing
    Just hs -> let ep_list = HS.toList hs
                   ng = name_gen b
                   (hs', _) = foldr wrapHelper (HS.empty, ng) ep_list
               in
               Just hs'

-- TODO new version
exprPairing :: State t ->
               State t ->
               Expr ->
               Expr ->
               HS.HashSet (Expr, Expr) ->
               Maybe (HS.HashSet (Expr, Expr))
exprPairing s1@(State {expr_env = h1}) s2@(State {expr_env = h2}) e1 e2 pairs =
  case (e1, e2) of
    -- TODO needed to add expr_env as input for isSymbolic
    (Var i, _) | E.isSymbolic (idName i) h1 -> Just (HS.insert (e1, e2) pairs)
               | Just e <- E.lookup (idName i) h1 -> exprPairing s1 s2 e e2 pairs
               | otherwise -> error "unmapped variable"
    (_, Var i) | E.isSymbolic (idName i) h2 -> Just (HS.insert (e1, e2) pairs)
               | Just e <- E.lookup (idName i) h2 -> exprPairing s1 s2 e1 e pairs
               | otherwise -> error "unmapped variable"
    -- TODO need to modify this case because of compiler errors
    (App _ _, App _ _) | (Data d1):l1 <- unApp e1
                       , (Data d2):l2 <- unApp e2
                       , d1 == d2 -> let ep = uncurry (exprPairing s1 s2)
                                         ep' hs p = ep p hs
                                         l = zip l1 l2
                                     in foldM ep' pairs l
    (App _ _, _) -> Just (HS.insert (e1, e2) pairs)
    (_, App _ _) -> Just (HS.insert (e1, e2) pairs)
    (Data d1, Data d2) | d1 == d2 -> Just pairs
                       | otherwise -> Nothing
    (Prim _ _, _) -> Just (HS.insert (e1, e2) pairs)
    (_, Prim _ _) -> Just (HS.insert (e1, e2) pairs)
    (Lit l1, Lit l2) | l1 == l2 -> Just pairs
                     | otherwise -> Nothing
    (Lam _ _ _, _) -> Just (HS.insert (e1, e2) pairs)
    (_, Lam _ _ _) -> Just (HS.insert (e1, e2) pairs)
    _ -> error "catch-all case"

matchAll :: [(Id, Id)] ->
            (State t, State t) ->
            Maybe (State t, State t, HS.HashSet (Expr, Expr))
matchAll idPairs (s1, s2) =
  let maybes = map (idPairing s1 s2) idPairs
      hashSets = [hs | Just hs <- maybes]
  in
  if length maybes /= length hashSets then Nothing
  else Just (s1, s2, foldr HS.union HS.empty hashSets)

-- to be paired, states need to match on all Id pairs
-- TODO do we need Name pairs or Expr pairs?  It was Name before
statePairing :: [State t] ->
                [State t] ->
                [(Id, Id)] ->
                [(State t, State t, HS.HashSet (Expr, Expr))]
statePairing states1 states2 idPairs =
  let statePairs = [(s1, s2) | s1 <- states1, s2 <- states2]
      maybes = map (matchAll idPairs) statePairs
  in
  [triple | Just triple <- maybes]

-- TODO wrap the expressions for proof obligations
caseWrap :: Expr -> N.NameGen -> (Expr, N.NameGen)
caseWrap e ng =
    -- TODO TyUnknown causes errors, using TyLitInt now
    let (matchId, ng') = N.freshId TyLitInt ng
        c = Case (Var matchId) matchId [Alt Default e]
    in
    (c, ng')
