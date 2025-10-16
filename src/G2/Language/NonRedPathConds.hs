{-# LANGUAGE BangPatterns, DeriveDataTypeable, DeriveGeneric, MultiParamTypeClasses, OverloadedStrings, PatternSynonyms, ViewPatterns #-}

module G2.Language.NonRedPathConds ( NonRedPathConds
                                   , NRPC
                                   , emptyNRPC
                                   , emptyNRPCNonUniq
                                   , addNRPC
                                   , addFirstNRPC
                                   , getNRPC
                                   , getLastNRPC
                                   , nullNRPC
                                   , toListNRPC
                                   , pattern (:*>)
                                   , pattern (:<*)
                                   , getNRPCUnique ) where

import G2.Language.AST
import G2.Language.Naming
import G2.Language.Syntax

import Data.Data
import qualified Data.Foldable as F
import Data.Hashable
import Data.Sequence
import GHC.Generics

type NRPC = (Expr, Expr)
data NonRedPathConds = NRPCs { nrpcs :: Seq NRPC, nrpc_uniq :: Unique }
                          deriving (Eq, Read, Show, Data, Generic, Typeable)

instance Hashable NonRedPathConds

emptyNRPC :: NameGen -> (NonRedPathConds, NameGen)
emptyNRPC ng = let (uniq, ng') = freshUnique ng in (NRPCs Empty uniq, ng')

emptyNRPCNonUniq :: NonRedPathConds
emptyNRPCNonUniq = NRPCs Empty 0

addNRPC :: NameGen -> Expr -> Expr -> NonRedPathConds -> (NameGen, NonRedPathConds)
addNRPC ng e1 e2 (NRPCs nrpc _) =
    let
        (e1', e2') = varOnRight e1 e2
        (uniq, ng') = freshUnique ng
    in
    (ng', NRPCs (nrpc :|> (e1', e2')) uniq)

addFirstNRPC :: NameGen -> Expr -> Expr -> NonRedPathConds -> (NameGen, NonRedPathConds)
addFirstNRPC ng e1 e2 (NRPCs nrpc _) =
    let
        (e1', e2') = varOnRight e1 e2
        (uniq, ng') = freshUnique ng
    in
    (ng', NRPCs ((e1', e2') :<| nrpc) uniq)

varOnRight :: Expr -> Expr -> (Expr, Expr)
varOnRight e1@(Var _) e2 = (e2, e1)
varOnRight e1@(Tick _ (Var _)) e2 = (e2, e1)
varOnRight e1 e2 = (e1, e2)

getNRPC :: NonRedPathConds -> Maybe ((Expr, Expr), NonRedPathConds)
getNRPC (NRPCs Empty _) = Nothing
getNRPC (NRPCs ((e1, e2) :<| nrpc) uniq) = Just ((e1, e2), NRPCs nrpc uniq)

getLastNRPC :: NonRedPathConds -> Maybe ((Expr, Expr), NonRedPathConds)
getLastNRPC (NRPCs Empty _) = Nothing
getLastNRPC (NRPCs (nrpc :|> (e1, e2)) uniq) = Just ((e1, e2), NRPCs nrpc uniq)

nullNRPC :: NonRedPathConds -> Bool
nullNRPC (NRPCs Empty _) = True
nullNRPC _ = False

toListNRPC :: NonRedPathConds -> [NRPC]
toListNRPC = F.toList . nrpcs

getNRPCUnique :: NonRedPathConds -> Unique
getNRPCUnique = nrpc_uniq

pattern (:*>) :: (Expr, Expr) -> NonRedPathConds -> NonRedPathConds
pattern e1_e2 :*> nrpc <- (getNRPC -> Just (e1_e2, nrpc))

pattern (:<*) :: NonRedPathConds -> (Expr, Expr) -> NonRedPathConds
pattern nrpc :<* e1_e2 <- (getLastNRPC -> Just (e1_e2, nrpc))

instance ASTContainer NonRedPathConds Expr where
    containedASTs = containedASTs . nrpcs
    modifyContainedASTs f (NRPCs nrpc uniq) = NRPCs { nrpcs = modifyContainedASTs f nrpc, nrpc_uniq = uniq } 

instance ASTContainer NonRedPathConds Type where
    containedASTs = containedASTs . nrpcs
    modifyContainedASTs f (NRPCs nrpc uniq) = NRPCs { nrpcs = modifyContainedASTs f nrpc, nrpc_uniq = uniq } 

instance Named NonRedPathConds where
    names (NRPCs nrpc _) = names nrpc
    rename old new (NRPCs nrpc uniq) = NRPCs (rename old new nrpc) uniq
    renames hm (NRPCs nrpc uniq) = NRPCs (renames hm nrpc) uniq