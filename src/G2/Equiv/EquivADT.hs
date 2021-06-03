module G2.Equiv.EquivADT (proofObligations, assumptions, statePairing) where

import G2.Language
import qualified G2.Language.ExprEnv as E
import qualified Data.HashSet as HS

import qualified Data.HashMap.Lazy as HM

-- TODO remove
import qualified Debug.Trace as D

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

-- TODO intersection is left-biased
-- I presume this means
-- TODO elem syntax
-- TODO might not actually need
safeMapUnion :: Maybe (HM.HashMap Id Expr) ->
                Maybe (HM.HashMap Id Expr) ->
                Maybe (HM.HashMap Id Expr)
safeMapUnion Nothing _ = Nothing
safeMapUnion _ Nothing = Nothing
safeMapUnion (Just hm1) (Just hm2) =
  let inter = HM.intersection hm1 hm2
      matches = HM.mapWithKey (\k v -> (Just v) == HM.lookup k hm2) inter
      matches_list = HM.elems matches
  in
      if False `elem` matches_list
      then Nothing
      else Just (HM.union hm1 hm2)

-- TODO how to define "more restrictive" for coinduction?
-- checks whether the second expr is more restrictive than the first
-- all variables must be mapped
-- TODO need to check same replacements for a symbolic var everywhere
-- TODO does the value returned by non-sym lookup matter?
-- if it's not symbolic, they need to be the same variable
-- TODO can a symbolic var be replaced by a different symbolic var?
-- TODO need an upward accumulation of hash map info
-- TODO should have only one state here
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
    (Data d1, Data d2) | d1 == d2 -> Just hm
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

isMoreRestrictive :: State t ->
                     Expr ->
                     Expr ->
                     Bool
isMoreRestrictive s e1 e2 =
  case moreRestrictive s HM.empty e1 e2 of
    Nothing -> False
    Just _ -> True

-- TODO check all elements of the HashSet
-- see if any pair fits with isMoreRestrictive
-- TODO this might not be efficient as it is now
moreRestrictivePair :: State t ->
                       State t ->
                       HS.HashSet (Expr, Expr) ->
                       Expr ->
                       Expr ->
                       Bool
moreRestrictivePair s1 s2 exprs e1 e2 =
  let mr (p1, p2) = (isMoreRestrictive s1 p1 e1) && (isMoreRestrictive s2 p2 e2)
  in
      not (HS.null $ HS.filter mr exprs)

-- TODO coinductive version of exprPairing
-- if a matching sub-expression is found, stop the recursion
-- TODO not sure about all the implementation details
epc :: State t ->
       State t ->
       HS.HashSet (Expr, Expr) ->
       Expr ->
       Expr ->
       HS.HashSet (Expr, Expr) ->
       Maybe (HS.HashSet (Expr, Expr))
epc s1@(State {expr_env = h1}) s2@(State {expr_env = h2}) exprs e1 e2 pairs =
  case (e1, e2) of
    -- TODO new termination case?
    -- needs to allow for more restrictive versions as well
    _ | moreRestrictivePair s1 s2 exprs e1 e2 -> Just pairs
    (Var i, _) | E.isSymbolic (idName i) h1 -> Just (HS.insert (e1, e2) pairs)
               -- TODO adjust the recursion?
               | Just e <- E.lookup (idName i) h1 -> epc s1 s2 (HS.insert (e1, e2) exprs) e e2 pairs
               | otherwise -> D.trace (show i) $ error "unmapped variable"
    (_, Var i) | E.isSymbolic (idName i) h2 -> Just (HS.insert (e1, e2) pairs)
               -- TODO same issue
               | Just e <- E.lookup (idName i) h2 -> epc s1 s2 (HS.insert (e1, e2) exprs) e1 e pairs
               | otherwise -> D.trace (show i) $ error "unmapped variable"
    (App _ _, App _ _) | (Data d1):l1 <- unApp e1
                       , (Data d2):l2 <- unApp e2
                       , d1 == d2 -> let ep = uncurry (epc s1 s2 (HS.insert (e1, e2) exprs))
                                         -- TODO recursion here, how to adjust?
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

exprPairing :: State t ->
               State t ->
               Expr ->
               Expr ->
               HS.HashSet (Expr, Expr) ->
               Maybe (HS.HashSet (Expr, Expr))
exprPairing s1 s2 =
  epc s1 s2 HS.empty

{-
exprPairing s1@(State {expr_env = h1}) s2@(State {expr_env = h2}) e1 e2 pairs =
  case (e1, e2) of
    (Var i, _) | E.isSymbolic (idName i) h1 -> Just (HS.insert (e1, e2) pairs)
               | Just e <- E.lookup (idName i) h1 -> exprPairing s1 s2 e e2 pairs
               -- TODO remove print later
               | otherwise -> D.trace (show i) $ error "unmapped variable"
    (_, Var i) | E.isSymbolic (idName i) h2 -> Just (HS.insert (e1, e2) pairs)
               | Just e <- E.lookup (idName i) h2 -> exprPairing s1 s2 e1 e pairs
               | otherwise -> D.trace (show i) $ error "unmapped variable"
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
-}

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
