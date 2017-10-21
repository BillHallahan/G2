{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module G2.Internals.Language.PathConds ( PathCond (..)
                                       , PathConds
                                       , insert
                                       , toList) where

import G2.Internals.Language.AST
import G2.Internals.Language.Naming
import G2.Internals.Language.Syntax

import Data.Coerce
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S

-- For each name, we record
--      (a) all PathConds that use that name
--      (b) all other names contained in those PathConds
newtype PathConds = PathConds (M.Map Name ([PathCond], [Name]))

-- | Path conditions represent logical constraints on our current execution
-- path. We can have path constraints enforced due to case/alt branching, due
-- to assertion / assumptions made, or some externally coded factors.
data PathCond = AltCond AltMatch Expr Bool
              | ExtCond Expr Bool
              | ConsCond DataCon Expr Bool
              | PCExists Id
              deriving (Show, Eq, Read)

toMap :: PathConds -> M.Map Name ([PathCond], [Name])
toMap = coerce

insert :: PathCond -> PathConds -> PathConds
insert p (PathConds pcs) =
    let
        ns = names p
    in
    PathConds $ foldr (M.alter (insert' p ns)) pcs ns

insert' :: PathCond -> [Name] -> Maybe ([PathCond], [Name]) -> Maybe ([PathCond], [Name])
insert' p ns Nothing = Just ([p], ns)
insert' p ns (Just (p', ns')) = Just (p:p', ns ++ ns')

-- TODO: Figure out the efficient way to do this...
scc :: [Name] -> PathConds -> PathConds
scc ns (PathConds pc) =
    let
        ns' = scc' ns S.empty pc
    in
    PathConds $ foldr (M.delete) pc ns'

scc' :: [Name] -> S.Set Name -> (M.Map Name ([PathCond], [Name])) -> S.Set Name
scc' [] lookedUp _ = lookedUp
scc' (n:ns) lookedUp pcs =
    if n `S.notMember` lookedUp then
        let
            pcns = M.lookup n pcs
        in
        case pcns of
            Just (pc, ns') -> scc' (ns' ++ ns) (foldr (S.insert) lookedUp ns') pcs
            Nothing -> error "Error in scc"
    else scc' ns lookedUp pcs

toList :: PathConds -> [PathCond]
toList = L.nub . concatMap fst . M.elems . toMap

instance ASTContainer PathCond Expr where
    containedASTs (ExtCond e _ )   = [e]
    containedASTs (AltCond _ e _) = [e]
    containedASTs (ConsCond _ e _) = [e]
    containedASTs (PCExists _) = []

    modifyContainedASTs f (ExtCond e b) = ExtCond (modifyContainedASTs f e) b
    modifyContainedASTs f (AltCond a e b) =
        AltCond (modifyContainedASTs f a) (modifyContainedASTs f e) b
    modifyContainedASTs f (ConsCond dc e b) =
        ConsCond (modifyContainedASTs f dc) (modifyContainedASTs f e) b
    modifyContainedASTs _ pc = pc

instance ASTContainer PathCond Type where
    containedASTs (ExtCond e _)   = containedASTs e
    containedASTs (AltCond e a _) = containedASTs e ++ containedASTs a
    containedASTs (ConsCond dcl e _) = containedASTs dcl ++ containedASTs e
    containedASTs (PCExists i) = containedASTs i

    modifyContainedASTs f (ExtCond e b) = ExtCond e' b
      where e' = modifyContainedASTs f e
    modifyContainedASTs f (AltCond e a b) = AltCond e' a' b
      where e' = modifyContainedASTs f e
            a' = modifyContainedASTs f a
    modifyContainedASTs f (ConsCond dc e b) =
        ConsCond (modifyContainedASTs f dc) (modifyContainedASTs f e) b
    modifyContainedASTs f (PCExists i) = PCExists (modifyContainedASTs f i)

instance Named PathCond where
    names (AltCond am e _) = names am ++ names e
    names (ExtCond e _) = names e
    names (ConsCond d e _) = names d ++  names e
    names (PCExists i) = names i

    rename old new (AltCond am e b) = AltCond (rename old new am) (rename old new e) b
    rename old new (ExtCond e b) = ExtCond (rename old new e) b
    rename old new (ConsCond d e b) = ConsCond (rename old new d) (rename old new e) b
    rename old new (PCExists i) = PCExists (rename old new i)
