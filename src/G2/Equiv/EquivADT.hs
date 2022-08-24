{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}

module G2.Equiv.EquivADT (
    proofObligations
  , Obligation (..)
  , unAppNoTicks
  ) where

import G2.Language
import qualified G2.Language.ExprEnv as E
import qualified Data.HashSet as HS

import qualified Data.HashMap.Lazy as HM

import Control.Monad

import G2.Execution.NormalForms
import G2.Equiv.G2Calls

import GHC.Generics (Generic)
import Data.Data
import Data.Hashable
import Data.Maybe

-- the bool is True if guarded coinduction can be used
-- TODO do I need all of these typeclasses?
-- earlier DataCons in the list are farther out
-- the first Int tag indicates which argument of the constructor this was
-- the second one indicates the total number of arguments for that constructor
-- if there are lambdas, we handle them in Verifier
data Obligation = Ob [(DataCon, Int, Int)] Expr Expr
                  deriving (Show, Eq, Read, Generic, Typeable, Data)

instance Hashable Obligation

proofObligations :: HS.HashSet Name
                 -> State t
                 -> State t
                 -> Expr
                 -> Expr
                 ->  Maybe (HS.HashSet Obligation)
proofObligations ns s1 s2 e1 e2 =
  exprPairing ns s1 s2 e1 e2 HS.empty [] []

removeTicks :: Expr -> Expr
removeTicks (Tick _ e) = removeTicks e
removeTicks e = e

removeAllTicks :: Expr -> Expr
removeAllTicks = modifyASTs removeTicks

unAppNoTicks :: Expr -> [Expr]
unAppNoTicks e =
  let e_list = unApp e
  in case e_list of
    e':t -> (removeTicks e'):t
    _ -> e_list

-- TODO getting catch-all case from infEq with inf1 and inf2
-- also getting two REC ticks on the variables at the beginning, which is wrong
exprPairing :: HS.HashSet Name -- ^ vars that should not be inlined on either side
            -> State t
            -> State t
            -> Expr
            -> Expr
            -> HS.HashSet Obligation -- ^ accumulator for output obligations
            -> [Name] -- ^ variables inlined previously on the LHS
            -> [Name] -- ^ variables inlined previously on the RHS
            -> Maybe (HS.HashSet Obligation)
exprPairing ns s1@(State {expr_env = h1}) s2@(State {expr_env = h2}) e1 e2 pairs n1 n2 =
  case (e1, e2) of
    _ | e1 == e2 -> Just pairs
    -- ignore all Ticks
    (Tick t1 e1', Tick t2 e2') | labeledErrorName t1 == labeledErrorName t2 -> exprPairing ns s1 s2 e1' e2' pairs n1 n2
    (Tick t e1', _) | isNothing $ labeledErrorName t -> exprPairing ns s1 s2 e1' e2 pairs n1 n2
    (_, Tick t e2') | isNothing $ labeledErrorName t -> exprPairing ns s1 s2 e1 e2' pairs n1 n2
    -- catch mismatches between labeled errors and other SWHNF expressions
    (Tick _ _, _) | isExprValueForm h2 (removeAllTicks e2) -> Nothing
    (_, Tick _ _) | isExprValueForm h1 (removeAllTicks e1) -> Nothing
    -- We have two error labels that are different from each other
    (Tick t1 e1', Tick t2 e2') -> Nothing
    -- keeping track of inlined vars prevents looping
    (Var i1, Var i2) | (idName i1) `elem` n1
                     , (idName i2) `elem` n2 -> Just $ HS.insert (Ob [] e1 e2) pairs
    (Var i, _) | E.isSymbolic (idName i) h1 -> Just $ HS.insert (Ob [] e1 e2) pairs
               | m <- idName i
               , not $ m `elem` ns
               , Just e <- E.lookup m h1 -> exprPairing ns s1 s2 e e2 pairs (m:n1) n2
               | not $ (idName i) `elem` ns -> error "unmapped variable"
    (_, Var i) | E.isSymbolic (idName i) h2 -> Just $ HS.insert (Ob [] e1 e2) pairs
               | m <- idName i
               , not $ m `elem` ns
               , Just e <- E.lookup m h2 -> exprPairing ns s1 s2 e1 e pairs n1 (m:n2)
               | not $ (idName i) `elem` ns -> error "unmapped variable"
    (Prim p1 _, Prim p2 _) | p1 == Error || p1 == Undefined
                           , p2 == Error || p2 == Undefined -> Just pairs
    -- extra cases for avoiding Error problems
    (Prim p _, _) | (p == Error || p == Undefined)
                  , isExprValueForm h2 (removeAllTicks e2) -> Nothing
    (_, Prim p _) | (p == Error || p == Undefined)
                  , isExprValueForm h1 (removeAllTicks e1) -> Nothing
    -- TODO test equivalence of functions and arguments?
    -- Might cause the verifier to miss some important things
    -- doesn't seem to help with int-nat difference
    -- on top of that, it breaks expNat, even with these constraints
    {-
    (App f1 a1, App f2 a2)
                  | (Var i1):l1 <- unApp e1
                  , (Var i2):l2 <- unApp e2
                  , (idName i1) `elem` ns
                  , (idName i2) `elem` ns
                  , Just pairs' <- exprPairing ns s1 s2 a1 a2 pairs n1 n2 ->
                    exprPairing ns s1 s2 f1 f2 pairs' n1 n2
    -}
    (Lit l1, Lit l2) | l1 == l2 -> Just pairs
                     | otherwise -> Nothing
    -- assume that all types line up between the two expressions
    (Type _, Type _) -> Just pairs
    -- See note in `moreRestrictive` regarding comparing DataCons
    _
        | (Data d@(DataCon d1 _)):l1 <- unAppNoTicks e1
        , (Data (DataCon d2 _)):l2 <- unAppNoTicks e2 ->
            if d1 == d2 then
                let ep = uncurry (exprPairing ns s1 s2)
                    ep' hs p = ep p hs n1 n2
                    l = zip l1 l2
                    extend i (Ob ds e1_ e2_) = Ob ((d, i, length l):ds) e1_ e2_
                    -- TODO inefficient list conversion
                    hl = map (\m -> case m of
                               Nothing -> Nothing
                               Just hs -> Just $ HS.toList hs) $ map (ep' HS.empty) l
                    hl' = map (\(i, m) -> case m of
                                Nothing -> Nothing
                                Just hs_l -> Just $ map (extend i) hs_l)
                              (zip [0..] hl)
                in
                if any isNothing hl'
                then Nothing
                else Just $ HS.union pairs $ HS.fromList $ concat (map fromJust hl')
                else Nothing
        | otherwise -> Just $ HS.insert (Ob [] e1 e2) pairs
