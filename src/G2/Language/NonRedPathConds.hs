{-# LANGUAGE BangPatterns, DeriveDataTypeable, DeriveGeneric, MultiParamTypeClasses, OverloadedStrings, PatternSynonyms, ViewPatterns #-}

module G2.Language.NonRedPathConds ( NonRedPathConds
                                   , NRPC
                                   , emptyNRPC
                                   , addNRPC
                                   , addFirstNRPC
                                   , getNRPC
                                   , getLastNRPC
                                   , nullNRPC
                                   , toListNRPC
                                   , pattern (:*>)
                                   , pattern (:<*)
                                   , toListInternalNRPC) where

import G2.Language.Naming
import G2.Language.Syntax

import qualified Data.Foldable as F
import Data.Sequence

type NRPC = (Expr, Expr)
type NonRedPathConds = Seq NRPC

emptyNRPC :: NonRedPathConds
emptyNRPC = Empty

addNRPC :: NameGen -> Expr -> Expr -> NonRedPathConds -> (NameGen, NonRedPathConds)
addNRPC ng e1 e2 nrpc =
    let (e1', e2') = varOnRight e1 e2 in
    (ng, nrpc :|> (e1', e2'))

addFirstNRPC :: NameGen -> Expr -> Expr -> NonRedPathConds -> (NameGen, NonRedPathConds)
addFirstNRPC ng e1 e2 nrpc =
    let (e1', e2') = varOnRight e1 e2 in
    (ng, (e1', e2') :<| nrpc )

varOnRight :: Expr -> Expr -> (Expr, Expr)
varOnRight e1@(Var _) e2 = (e2, e1)
varOnRight e1@(Tick _ (Var _)) e2 = (e2, e1)
varOnRight e1 e2 = (e1, e2)

getNRPC :: NonRedPathConds -> Maybe ((Expr, Expr), NonRedPathConds)
getNRPC Empty = Nothing
getNRPC ((e1, e2) :<| nrpc) = Just ((e1, e2), nrpc)

getLastNRPC :: NonRedPathConds -> Maybe ((Expr, Expr), NonRedPathConds)
getLastNRPC Empty = Nothing
getLastNRPC (nrpc :|> (e1, e2)) = Just ((e1, e2), nrpc)

nullNRPC :: NonRedPathConds -> Bool
nullNRPC Empty = False
nullNRPC _ = True

toListNRPC :: NonRedPathConds -> [(Expr, Expr)]
toListNRPC nrpc = F.toList nrpc

toListInternalNRPC :: NonRedPathConds -> [NRPC]
toListInternalNRPC = F.toList

pattern (:*>) :: (Expr, Expr) -> NonRedPathConds -> NonRedPathConds
pattern e1_e2 :*> nrpc <- (getNRPC -> Just (e1_e2, nrpc))

pattern (:<*) :: NonRedPathConds -> (Expr, Expr) -> NonRedPathConds
pattern nrpc :<* e1_e2 <- (getLastNRPC -> Just (e1_e2, nrpc))