module G2.Equiv.EquivADT (proofObligations, statePairing) where

import G2.Language
import qualified G2.Language.ExprEnv as E
import qualified Data.HashSet as HS

import qualified Data.HashMap.Lazy as HM

import Control.Monad

-- TODO
import qualified Debug.Trace as D

proofObligations :: State t ->
                    State t ->
                    Expr ->
                    Expr ->
                    Maybe (HS.HashSet (Expr, Expr))
proofObligations s1 s2 e1 e2 =
  exprPairing s1 s2 e1 e2 HS.empty

assumptions :: State t ->
               State t ->
               Expr ->
               Expr ->
               Maybe (HS.HashSet (Expr, Expr))
assumptions s1 s2 e1 e2 =
  exprPairing s1 s2 e1 e2 HS.empty

idPairing :: State t -> State t -> (Id, Id) -> Maybe (HS.HashSet (Expr, Expr))
idPairing s1 s2 (i1, i2) =
  case assumptions s1 s2 (Var i1) (Var i2) of
    Just hs -> D.trace (show hs) $ D.trace (show (i1, i2)) $ Just hs
    Nothing -> Nothing

exprPairing :: State t ->
               State t ->
               Expr ->
               Expr ->
               HS.HashSet (Expr, Expr) ->
               Maybe (HS.HashSet (Expr, Expr))
exprPairing s1@(State {expr_env = h1}) s2@(State {expr_env = h2}) e1 e2 pairs =
  case (e1, e2) of
    (Var i, _) | E.isSymbolic (idName i) h1 -> Just (HS.insert (e1, e2) pairs)
               | Just e <- E.lookup (idName i) h1 -> exprPairing s1 s2 e e2 pairs
               | otherwise -> error "unmapped variable"
    (_, Var i) | E.isSymbolic (idName i) h2 -> Just (HS.insert (e1, e2) pairs)
               | Just e <- E.lookup (idName i) h2 -> exprPairing s1 s2 e1 e pairs
               | otherwise -> error "unmapped variable"
    -- See note in `moreRestrictive` regarding comparing DataCons
    (App _ _, App _ _) | (Data (DataCon d1 _)):l1 <- unApp e1
                       , (Data (DataCon d2 _)):l2 <- unApp e2 ->
        if d1 == d2 then
            let ep = uncurry (exprPairing s1 s2)
                ep' hs p = ep p hs
                l = zip l1 l2
            in foldM ep' pairs l
            else Nothing
            -- D.trace "AAA" $ D.trace (show (e1, e2)) $ D.trace "aaa" $ Nothing
    (App _ _, _) -> Just (HS.insert (e1, e2) pairs)
    (_, App _ _) -> Just (HS.insert (e1, e2) pairs)
    (Data (DataCon d1 _), Data (DataCon d2 _))
                       | d1 == d2 -> Just pairs
                       | otherwise -> D.trace "BBB" Nothing
    -- TODO Error and Undefined primitives
    (Prim p1 _, Prim p2 _) | p1 == Error || p1 == Undefined
                           , p2 == Error || p2 == Undefined -> Just pairs
    (Prim _ _, _) -> Just (HS.insert (e1, e2) pairs)
    (_, Prim _ _) -> Just (HS.insert (e1, e2) pairs)
    (Lit l1, Lit l2) | l1 == l2 -> Just pairs
                     | otherwise -> D.trace "CCC" Nothing
    (Lam _ _ _, _) -> Just (HS.insert (e1, e2) pairs)
    (_, Lam _ _ _) -> Just (HS.insert (e1, e2) pairs)
    -- TODO assume for now that all types line up between the two expressions
    (Type _, Type _) -> Just pairs
    _ -> error $ "catch-all case\n" ++ show e1 ++ "\n" ++ show e2

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
statePairing :: [State t] ->
                [State t] ->
                [(Id, Id)] ->
                [(State t, State t, HS.HashSet (Expr, Expr))]
statePairing states1 states2 idPairs =
  let statePairs = [(s1, s2) | s1 <- states1, s2 <- states2]
      maybes = map (matchAll idPairs) statePairs
  in
  [triple | Just triple <- maybes]
