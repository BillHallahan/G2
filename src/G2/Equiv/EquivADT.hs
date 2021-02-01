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
                 Maybe (HS.HashSet (Expr, Expr))
-- get ExprEnv from both states
-- look up symbolic vars in the ExprEnv
-- check concretizations for each of them
findEquivVars s1 s2 e1 e2 =
  -- TODO need anything else from the state, or just ExprEnv?
  exprPairing s1 s2 e1 e2 HS.empty

{-
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
-}

idPairing :: State t -> State t -> (Id, Id) -> Maybe (HS.HashSet (Expr, Expr))
idPairing s1 s2 (i1, i2) =
  findEquivVars s1 s2 (Var i1) (Var i2)

-- TODO returns Nothing if findEquivVars does
-- TODO does it need to be if and only if?
-- actually, it could return as non-null all the time
-- the output only needs to be meaningful when findEquivVars is non-null
-- for the Just case, it returns a set of proof obligations
-- the returned pairs need to be shown to be equivalent
-- TODO does this need an extra argument to be an accumulator?
{-
exprPairing :: State t ->
               State t ->
               Expr ->
               Expr ->
               HS.HashSet (Expr, Expr)
exprPairing s1@(State {expr_env = h1}) s2@(State {expr_env = h2}) e1 e2 =
  case (e1, e2) of
    -- TODO don't need all these cases
    (Data _, _) -> HS.empty
    (_, Data _) -> HS.empty
    (Lit _, _) -> HS.empty
    (_, Lit _) -> HS.empty
    (Var i, _) | E.isSymbolic i -> error "symbolic"
               | Just e <- E.lookup (idName i) h1 -> exprPairing s1 s2 e e2
               | otherwise -> HS.empty
    (_, Var i) | E.isSymbolic i -> error "symbolic"
               | Just e <- E.lookup (idName i) h2 -> exprPairing s1 s2 e1 e
               | otherwise -> HS.empty
    (Prim _ _, Prim _ _) -> HS.insert (e1, e2) HS.empty
    -- TODO does this need to come before the Var case?
    (App _ _, _) -> HS.insert (e1, e2) HS.empty
    (_, App _ _) -> HS.insert (e1, e2) HS.empty
    _ -> HS.empty
-}

-- TODO new version
exprPairing :: State t ->
               State t ->
               Expr ->
               Expr ->
               HS.HashSet (Expr, Expr) ->
               Maybe HS.HashSet (Expr, Expr)
exprPairing s1@(State {expr_env = h1}) s2@(State {expr_env = h2}) e1 e2 pairs =
  case (e1, e2) of
    (Var i, _) | E.isSymbolic i -> Just (HS.insert (e1, e2) pairs)
               | Just e <- E.lookup (idName i) h1 -> exprPairing s1 s2 e e2 pairs
               | otherwise -> error "unmapped variable"
    (_, Var i) | E.isSymbolic i -> Just (HS.insert (e1, e2) pairs)
               | Just e <- E.lookup (idName i) h2 -> exprPairing s1 s2 e1 e pairs
               | otherwise -> error "unmapped variable"
    (App _ _, App _ _) | (Data d1):l1 <- unApp e1
                       , (Data d2):l2 <- unApp e2
                       , d1 == d2 -> let ep = uncurry (exprPairing s1 s2)
                                         l = zip l1 l2
                                     in foldM ep pairs l
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
