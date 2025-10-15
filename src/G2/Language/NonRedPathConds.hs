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

import G2.Language.AST
import G2.Language.Naming
import G2.Language.Syntax

import Data.Data
import qualified Data.Foldable as F
import Data.Hashable
import Data.Sequence
import GHC.Generics

type NRPC = (Expr, Expr)
newtype NonRedPathConds = NRPCs { nrpcs :: Seq NRPC }
                          deriving (Eq, Read, Show, Data, Generic, Typeable)

instance Hashable NonRedPathConds

emptyNRPC :: NonRedPathConds
emptyNRPC = NRPCs Empty

addNRPC :: NameGen -> Expr -> Expr -> NonRedPathConds -> (NameGen, NonRedPathConds)
addNRPC ng e1 e2 (NRPCs nrpc) =
    let (e1', e2') = varOnRight e1 e2 in
    (ng, NRPCs $ nrpc :|> (e1', e2'))

addFirstNRPC :: NameGen -> Expr -> Expr -> NonRedPathConds -> (NameGen, NonRedPathConds)
addFirstNRPC ng e1 e2 (NRPCs nrpc) =
    let (e1', e2') = varOnRight e1 e2 in
    (ng, NRPCs $ (e1', e2') :<| nrpc)

varOnRight :: Expr -> Expr -> (Expr, Expr)
varOnRight e1@(Var _) e2 = (e2, e1)
varOnRight e1@(Tick _ (Var _)) e2 = (e2, e1)
varOnRight e1 e2 = (e1, e2)

getNRPC :: NonRedPathConds -> Maybe ((Expr, Expr), NonRedPathConds)
getNRPC (NRPCs Empty) = Nothing
getNRPC (NRPCs ((e1, e2) :<| nrpc)) = Just ((e1, e2), NRPCs nrpc)

getLastNRPC :: NonRedPathConds -> Maybe ((Expr, Expr), NonRedPathConds)
getLastNRPC (NRPCs Empty) = Nothing
getLastNRPC (NRPCs (nrpc :|> (e1, e2))) = Just ((e1, e2), NRPCs nrpc)

nullNRPC :: NonRedPathConds -> Bool
nullNRPC (NRPCs Empty) = False
nullNRPC _ = True

toListNRPC :: NonRedPathConds -> [(Expr, Expr)]
toListNRPC = F.toList . nrpcs

toListInternalNRPC :: NonRedPathConds -> [NRPC]
toListInternalNRPC = F.toList . nrpcs

pattern (:*>) :: (Expr, Expr) -> NonRedPathConds -> NonRedPathConds
pattern e1_e2 :*> nrpc <- (getNRPC -> Just (e1_e2, nrpc))

pattern (:<*) :: NonRedPathConds -> (Expr, Expr) -> NonRedPathConds
pattern nrpc :<* e1_e2 <- (getLastNRPC -> Just (e1_e2, nrpc))

instance ASTContainer NonRedPathConds Expr where
    containedASTs = containedASTs . nrpcs
    modifyContainedASTs f (NRPCs nrpc) = NRPCs { nrpcs = modifyContainedASTs f nrpc } 

instance ASTContainer NonRedPathConds Type where
    containedASTs = containedASTs . nrpcs
    modifyContainedASTs f (NRPCs nrpc) = NRPCs { nrpcs = modifyContainedASTs f nrpc } 

instance Named NonRedPathConds where
    names (NRPCs nrpc) = names nrpc
    rename old new (NRPCs nrpc) = NRPCs (rename old new nrpc)
    renames hm (NRPCs nrpc) = NRPCs (renames hm nrpc)