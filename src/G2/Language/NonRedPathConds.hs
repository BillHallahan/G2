{-# LANGUAGE BangPatterns, DeriveDataTypeable, DeriveGeneric, MultiParamTypeClasses, OverloadedStrings, PatternSynonyms, ViewPatterns #-}
{-# LANGUAGE InstanceSigs #-}

module G2.Language.NonRedPathConds ( Focus (..)
                                   , NonRedPathConds
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
                                   , getNRPCUnique
                                   , setFocus
                                   , allNRPC ) where

import G2.Language.AST
import G2.Language.Naming
import G2.Language.Syntax
import qualified G2.Language.ExprEnv as E

import Data.Data
import qualified Data.Foldable as F
import Data.Hashable
import Data.Sequence
import GHC.Generics
import G2.Language.ExprEnv (deepLookupVar)

type NRPC = (Focus, Expr, Expr)
data NonRedPathConds = NRPCs { nrpcs :: Seq NRPC, nrpc_uniq :: Unique }
                          deriving (Eq, Read, Show, Data, Generic, Typeable)

instance Hashable NonRedPathConds

-- Is evaluation of the NRPC being forced? I.e. does evaluation of the state definitely evaluate the NRPC expression(s)
data Focus = Focused | Unfocused
             deriving (Eq, Read, Show, Data, Generic, Typeable)

instance Hashable Focus

emptyNRPC :: NameGen -> (NonRedPathConds, NameGen)
emptyNRPC ng = let (uniq, ng') = freshUnique ng in (NRPCs Empty uniq, ng')

emptyNRPCNonUniq :: NonRedPathConds
emptyNRPCNonUniq = NRPCs Empty 0

addNRPC :: NameGen -> Focus -> Expr -> Expr -> NonRedPathConds -> (NameGen, NonRedPathConds)
addNRPC ng focus e1 e2 (NRPCs nrpc curr_uniq) =
    let
        (e1', e2') = varOnRight e1 e2
        (uniq, ng') = if focus == Focused then freshUnique ng else (curr_uniq, ng)
    in
    (ng', NRPCs (nrpc :|> (focus, e1', e2')) uniq)

addFirstNRPC :: NameGen -> Focus -> Expr -> Expr -> NonRedPathConds -> (NameGen, NonRedPathConds)
addFirstNRPC ng focus e1 e2 (NRPCs nrpc curr_uniq) =
    let
        (e1', e2') = varOnRight e1 e2
        (uniq, ng') = if focus == Focused then freshUnique ng else (curr_uniq, ng)
    in
    (ng', NRPCs ((focus, e1', e2') :<| nrpc) uniq)

varOnRight :: Expr -> Expr -> (Expr, Expr)
varOnRight e1@(Var _) e2 = (e2, e1)
varOnRight e1@(Tick _ (Var _)) e2 = (e2, e1)
varOnRight e1 e2 = (e1, e2)

getNRPC :: NonRedPathConds -> Maybe (NRPC, NonRedPathConds)
getNRPC (NRPCs Empty _) = Nothing
getNRPC (NRPCs ((focus, e1, e2) :<| nrpc) uniq) = Just ((focus, e1, e2), NRPCs nrpc uniq)

getLastNRPC :: NonRedPathConds -> Maybe (NRPC, NonRedPathConds)
getLastNRPC (NRPCs Empty _) = Nothing
getLastNRPC (NRPCs (nrpc :|> (focus, e1, e2)) uniq) = Just ((focus, e1, e2), NRPCs nrpc uniq)

nullNRPC :: NonRedPathConds -> Bool
nullNRPC (NRPCs Empty _) = True
nullNRPC _ = False

toListNRPC :: NonRedPathConds -> [NRPC]
toListNRPC = F.toList . nrpcs

getNRPCUnique :: NonRedPathConds -> Unique
getNRPCUnique = nrpc_uniq

setFocus :: Name -> Focus -> E.ExprEnv -> NonRedPathConds -> NonRedPathConds
setFocus n focus eenv (NRPCs nrpc uniq) = NRPCs (fmap set nrpc) uniq
    where
        set (_, e1, e2@(Var (Id n' _))) | areSame n' = (focus, e1, e2)
        set e1_e2 = e1_e2

        areSame n' = deepLookupVar n eenv == deepLookupVar n' eenv

allNRPC :: (NRPC -> Bool) -> NonRedPathConds -> Bool
allNRPC p (NRPCs nrpc _) = all p nrpc

pattern (:*>) :: (Focus, Expr, Expr) -> NonRedPathConds -> NonRedPathConds
pattern e1_e2 :*> nrpc <- (getNRPC -> Just (e1_e2, nrpc))

pattern (:<*) :: NonRedPathConds -> (Focus, Expr, Expr) -> NonRedPathConds
pattern nrpc :<* e1_e2 <- (getLastNRPC -> Just (e1_e2, nrpc))

instance ASTContainer Focus Expr where
    containedASTs _ = []
    modifyContainedASTs _ focus = focus

instance ASTContainer Focus Type where
    containedASTs _ = []
    modifyContainedASTs _ focus = focus

instance Named Focus where
    names _ = Empty
    rename _ _ focus = focus
    renames _ focus = focus

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