module G2.Equiv.EquivADT (findEquivVars) where

import Data.List
import G2.Language
import qualified G2.Language.ExprEnv as E
-- TODO decide between lazy and strict
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS

-- TODO states include lists of symbolic vars
findEquivVars :: State t ->
                 State t ->
                 Expr ->
                 Expr ->
                 Maybe (HS.HashSet (Name, Name))
-- get ExprEnv from both states
-- look up symbolic vars in the ExprEnv
-- check concretizations for each of them
findEquivVars s1 s2 e1 e2 =
  -- TODO need anything else from the state, or just ExprEnv?
  namePairing s1 s2 e1 e2 HS.empty

namePairing :: State t ->
               State t ->
               Expr ->
               Expr ->
               HS.HashSet (Name, Name) ->
               Maybe (HS.HashSet (Name, Name))
namePairing s1@(State {expr_env = h1}) s2@(State {expr_env = h2}) e1 e2 pairs =
  case (e1, e2) of
    (Data d1, Data d2) | d1 == d2 -> Just pairs
                       | otherwise -> Nothing
    (Data _, _) -> Nothing
    (_, Data _) -> Nothing
    (Var i1, Var i2) | E.isSymbolic i1, E.isSymbolic i2 -> Just (HS.insert (i1, i2) pairs)
    (Var i, _) | E.isSymbolic i -> error "symbolic"
               | Just e <- E.lookup (idName i) h1 -> namePairing s1 s2 e e2 pairs
               | otherwise -> Nothing
    (_, Var i) | E.isSymbolic i -> error "symbolic"
               | Just e <- E.lookup (idName i) h2 -> namePairing s1 s2 e1 e pairs
               | otherwise -> Nothing
    (Lit l1, Lit l2) | l1 == l2 -> Just pairs
                     | otherwise -> Nothing
    (Lit _, _) -> Nothing
    (_, Lit _) -> Nothing
    (Prim p1 t1, Prim p2 t2) -> error "primitive"
    (Prim _ _, _) -> Nothing
    (_, Prim _ _) -> Nothing
    (App f1 a1, App f2 a2) -> let pairs1 = namePairing s1 s2 f1 f2 pairs
                                  pairs2 = namePairing s1 s2 a1 a2 pairs
                              in (HS.union) <$> pairs1 <*> pairs2
    (App _ _, _) -> error "not fully evaluated"
    (_, App _ _) -> error "not fully evaluated"
    _ -> error "catch-all case"

idPairing :: State t -> State t -> (Id, Id) -> Maybe (HS.HashSet (Name, Name))
idPairing s1 s2 (i1, i2) =
  findEquivVars s1 s2 (Var i1) (Var i2)

-- TODO returns Nothing if and only if findEquivVars does
-- for the Just case, it returns a set of proof obligations
-- the returned pairs need to be shown to be equivalent
exprPairing :: State t ->
               State t ->
               Expr ->
               Expr ->
               Maybe (HS.HashSet (Expr, Expr))
exprPairing s1@(State {expr_env = h1}) s2@(State {expr_env = h2}) e1 e2 =
  Nothing

matchAll :: [(Id, Id)] ->
            (State t, State t) ->
            Maybe (State t, State t, HS.HashSet (Name, Name))
matchAll idPairs (s1, s2) =
  let maybes = map (idPairing s1 s2) idPairs
      hashSets = [hs | Just hs <- maybes]
  in
  if length maybes /= length hashSets then Nothing
  else Just (s1, s2, foldl HS.union HS.empty hashSets)

-- to be paired, states need to match on all Id pairs
statePairing :: [State t] -> [State t] -> [(Id, Id)] -> [(State t, State t, HS.HashSet (Name, Name))]
statePairing states1 states2 idPairs =
  let statePairs = [(s1, s2) | s1 <- states1, s2 <- states2]
      maybes = map (matchAll idPairs) statePairs
  in
  [triple | Just triple <- maybes]
