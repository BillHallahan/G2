module G2.Equiv.EquivADT (proofObligations) where

import G2.Language
import qualified G2.Language.ExprEnv as E
import qualified Data.HashSet as HS

import Control.Monad

proofObligations :: State t ->
                    State t ->
                    Expr ->
                    Expr ->
                    Maybe (HS.HashSet (Expr, Expr))
-- get ExprEnv from both states
-- look up symbolic vars in the ExprEnv
-- check concretizations for each of them
proofObligations s1 s2 e1 e2 =
  exprPairing s1 s2 e1 e2 HS.empty

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
    -- TODO assume for now that all types line up between the two expressions
    (Type _, Type _) -> Just pairs
    _ -> error "catch-all case"