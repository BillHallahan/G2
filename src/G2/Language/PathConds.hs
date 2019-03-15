{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module G2.Language.PathConds ( PathCond (..)
                                       , Constraint
                                       , Assertion
                                       , PathConds(..)
                                       , toMap
                                       , empty
                                       , fromList
                                       , map
                                       , filter
                                       , insert
                                       , null
                                       , number
                                       , relevant
                                       , relatedSets
                                       , scc
                                       , varIdsInPC
                                       , toList) where

import G2.Language.AST
import G2.Language.Ids
import qualified G2.Language.KnownValues as KV
import G2.Language.Typing
import G2.Language.Naming
import G2.Language.Syntax

import Data.Coerce
import GHC.Generics (Generic)
import Data.Hashable
import qualified Data.HashSet as HS
import qualified Data.List as L
import qualified Data.Map as M
import Data.Maybe
import Prelude hiding (map, filter, null)
import qualified Prelude as P (map)

-- In the implementation:
-- Each name (Just n) maps to some (but not neccessarily all) of the PathCond's that
-- contain n, and a list of all names that appear in some PathCond alongside
-- the name n
-- PathConds that contain no names are stored in Nothing
--
-- You can visualize this as a graph, with Names and Nothing as Nodes.
-- Edges exist in a PathConds pcs netween a name n, and any names in
-- snd $ M.lookup n (toMap pcs)

-- | You can visualize a PathConds as [PathCond] (accessible via toList)
newtype PathConds = PathConds (M.Map (Maybe Name) (HS.HashSet PathCond, [Name]))
                    deriving (Show, Eq, Read)

-- | Path conditions represent logical constraints on our current execution
-- path. We can have path constraints enforced due to case/alt branching, due
-- to assertion / assumptions made, or some externally coded factors.
data PathCond = AltCond AltMatch Expr Bool -- ^ The expression and alt must match
              | ExtCond Expr Bool -- ^ The expression must be a (true) boolean
              | ConsCond DataCon Expr Bool -- ^ The expression and datacon must match
              | PCExists Id -- ^ Makes sure we find some value for the given name, of the correct type
              | AssumePC Expr PathCond -- The expression must be (true) boolean
              deriving (Show, Eq, Read, Generic)

type Constraint = PathCond
type Assertion = PathCond

instance Hashable PathCond

{-# INLINE toMap #-}
toMap :: PathConds -> M.Map (Maybe Name) (HS.HashSet PathCond, [Name])
toMap = coerce

{-# INLINE empty #-}
-- | Constructs an empty `PathConds`.
empty :: PathConds
empty = PathConds M.empty

fromList :: KV.KnownValues -> [PathCond] -> PathConds
fromList kv = coerce . foldr (insert kv) empty

map :: (PathCond -> a) -> PathConds -> [a]
map f = L.map f . toList

filter :: (PathCond -> Bool) -> PathConds -> PathConds
filter f = PathConds 
         . M.filter (not . HS.null . fst)
         . M.map (\(pc, ns) -> (HS.filter f pc, ns))
         . toMap

-- Each name n maps to all other names that are in any PathCond containing n
-- However, each n does NOT neccessarily map to all PCs containing n- instead each
-- PC is associated with only one name.
-- This is ok, because the PCs can only be externally accessed by toList (which 
-- returns all PCs anyway) or scc (which forces exploration over all shared names)
{-# INLINE insert #-}
insert :: KV.KnownValues -> PathCond -> PathConds -> PathConds
insert = insert' varNamesInPC

insert' :: (KV.KnownValues -> PathCond -> [Name]) -> KV.KnownValues -> PathCond -> PathConds -> PathConds
insert' f kv p (PathConds pcs) =
    let
        ns = f kv p

        (hd, insertAt) = case ns of
            [] -> (Nothing, [Nothing])
            (h:_) -> (Just h, P.map Just ns)
    in
    PathConds $ M.adjust (\(p', ns') -> (HS.insert p p', ns')) hd
              $ foldr (M.alter (insert'' ns)) pcs insertAt

insert'' :: [Name] -> Maybe (HS.HashSet PathCond, [Name]) -> Maybe (HS.HashSet PathCond, [Name])
insert'' ns Nothing = Just (HS.empty, ns)
insert'' ns (Just (p', ns')) = Just (p', ns ++ ns')

{-# INLINE number #-}
number :: PathConds -> Int
number = length . toList

{-# INLINE null #-}
null :: PathConds -> Bool
null = M.null . toMap

-- | Filters a PathConds to only those PathCond's that potentially impact the
-- given PathCond's satisfiability (i.e. they are somehow linked by variable names)
relevant :: KV.KnownValues -> [PathCond] -> PathConds -> PathConds
relevant kv pc pcs = 
    case concatMap (varNamesInPC kv) pc of
        [] -> fromList kv pc
        rel -> scc rel pcs

-- Returns a list of PathConds, where the union of the output PathConds
-- is the input PathConds, and the PathCond are seperated into there SCCs
relatedSets :: KV.KnownValues -> PathConds -> [PathConds]
relatedSets kv pc@(PathConds pcm) = 
    let
        epc = case M.lookup Nothing pcm of
                Just v -> PathConds $ M.singleton Nothing v
                Nothing -> PathConds M.empty

        ns = catMaybes $ M.keys pcm
    in
    if null epc then relatedSets' kv pc ns else epc:relatedSets' kv pc ns

relatedSets' :: KV.KnownValues -> PathConds -> [Name] -> [PathConds]
relatedSets' kv pc ns =
    case ns of
      k:_ ->
          let
              s = scc [k] pc
              ns' = concat $ map (varNamesInPC kv) s
          in
          s:relatedSets' kv pc (ns L.\\ (k:ns'))
      [] ->  []


varIdsInPC :: KV.KnownValues -> PathCond -> [Id]
-- [AltCond]
-- Optimization
-- When we have an AltCond with a Var expr, we only have to look at
-- other PC's with that Var's name.  This is because we assign all
-- DCs from the same part in a DC tree the same name, and a DC's
-- parents/children can't impose restrictions on it.  We are completely
-- guided by pattern matching from case statements.
-- See note [ChildrenNames] in Execution/Rules.hs
varIdsInPC kv (AltCond altC@(DataAlt (DataCon _ _) _) (Cast e _) b) = varIdsInPC kv $ AltCond altC e b
varIdsInPC kv (AltCond (DataAlt (DataCon _ _) _) (Var i@(Id _ t)) _) 
             | t /= tyBool kv = [i]
varIdsInPC _ (AltCond a e _) = varIdsInAltMatch a ++ varIds e
varIdsInPC _ (ExtCond e _) = varIds e
varIdsInPC _ (ConsCond _ e _) = varIds e
varIdsInPC _ (PCExists _) = []
varIdsInPC kv (AssumePC _ pc) = varIdsInPC kv pc

varIdsInAltMatch :: AltMatch -> [Id]
varIdsInAltMatch (DataAlt _ i) = i
varIdsInAltMatch _ = []

varNamesInPC :: KV.KnownValues -> PathCond -> [Name]
varNamesInPC kv = P.map idName . varIdsInPC kv

{-# INLINE scc #-}
scc :: [Name] -> PathConds -> PathConds
scc ns (PathConds pc) = PathConds $ scc' ns pc M.empty

scc' :: [Name]
     -> (M.Map (Maybe Name) (HS.HashSet PathCond, [Name]))
     -> (M.Map (Maybe Name) (HS.HashSet PathCond, [Name]))
     -> (M.Map (Maybe Name) (HS.HashSet PathCond, [Name]))
scc' [] _ pc = pc
scc' (n:ns) pc newpc =
    -- Check if we already inserted the name information
    case M.lookup (Just n) newpc of
        Just _ -> scc' ns pc newpc
        Nothing ->
            -- If we didn't, lookup info to insert,
            -- and add names to the list of names to search
            case M.lookup (Just n) pc of
                Just pcn@(_, ns') -> scc' (ns ++ ns') pc (M.insert (Just n) pcn newpc)
                Nothing -> scc' ns pc newpc

{-# INLINE toList #-}
toList :: PathConds -> [PathCond]
toList = concatMap (HS.toList . fst) . M.elems . toMap

instance ASTContainer PathConds Expr where
    containedASTs = containedASTs . toMap
    
    modifyContainedASTs f = coerce . modifyContainedASTs f . toMap

instance ASTContainer PathConds Type where
    containedASTs = containedASTs . toMap

    modifyContainedASTs f = coerce . modifyContainedASTs f . toMap

instance ASTContainer PathCond Expr where
    containedASTs (ExtCond e _ )   = [e]
    containedASTs (AltCond _ e _) = [e]
    containedASTs (ConsCond _ e _) = [e]
    containedASTs (PCExists _) = []
    containedASTs (AssumePC _ pc) = containedASTs pc

    modifyContainedASTs f (ExtCond e b) = ExtCond (modifyContainedASTs f e) b
    modifyContainedASTs f (AltCond a e b) =
        AltCond (modifyContainedASTs f a) (modifyContainedASTs f e) b
    modifyContainedASTs f (ConsCond dc e b) =
        ConsCond (modifyContainedASTs f dc) (modifyContainedASTs f e) b
    modifyContainedASTs f (AssumePC expr pc) = AssumePC expr (modifyContainedASTs f pc)
    modifyContainedASTs _ pc = pc

instance ASTContainer PathCond Type where
    containedASTs (ExtCond e _)   = containedASTs e
    containedASTs (AltCond e a _) = containedASTs e ++ containedASTs a
    containedASTs (ConsCond dcl e _) = containedASTs dcl ++ containedASTs e
    containedASTs (PCExists i) = containedASTs i
    containedASTs (AssumePC e pc) = containedASTs e ++ containedASTs pc -- todo: check

    modifyContainedASTs f (ExtCond e b) = ExtCond e' b
      where e' = modifyContainedASTs f e
    modifyContainedASTs f (AltCond e a b) = AltCond e' a' b
      where e' = modifyContainedASTs f e
            a' = modifyContainedASTs f a
    modifyContainedASTs f (ConsCond dc e b) =
        ConsCond (modifyContainedASTs f dc) (modifyContainedASTs f e) b
    modifyContainedASTs f (PCExists i) = PCExists (modifyContainedASTs f i)
    modifyContainedASTs f (AssumePC expr pc) = AssumePC expr (modifyContainedASTs f pc)

instance Named PathConds where
    names (PathConds pc) = (catMaybes $ M.keys pc) ++ concatMap (\(p, n) -> names p ++ n) pc

    rename old new (PathConds pc) =
        PathConds . M.mapKeys (\k -> if k == (Just old) then (Just new) else k)
                  $ rename old new pc

    renames hm (PathConds pc) =
        PathConds . M.mapKeys (renames hm)
                  $ renames hm pc

instance Named PathCond where
    names (AltCond am e _) = names am ++ names e
    names (ExtCond e _) = names e
    names (ConsCond d e _) = names d ++  names e
    names (PCExists i) = names i
    names (AssumePC _ pc) = names pc

    rename old new (AltCond am e b) = AltCond (rename old new am) (rename old new e) b
    rename old new (ExtCond e b) = ExtCond (rename old new e) b
    rename old new (ConsCond d e b) = ConsCond (rename old new d) (rename old new e) b
    rename old new (PCExists i) = PCExists (rename old new i)
    rename old new (AssumePC expr pc) = AssumePC (rename old new expr) (rename old new pc)

    renames hm (AltCond am e b) = AltCond (renames hm am) (renames hm e) b
    renames hm (ExtCond e b) = ExtCond (renames hm e) b
    renames hm (ConsCond d e b) = ConsCond (renames hm d) (renames hm e) b
    renames hm (PCExists i) = PCExists (renames hm i)
    renames hm (AssumePC expr pc) = AssumePC (renames hm expr) (renames hm pc)

instance Ided PathConds where
    ids = ids . toMap

instance Ided PathCond where
    ids (AltCond am e _) = ids am ++ ids e
    ids (ExtCond e _) = ids e
    ids (ConsCond d e _) = ids d ++  ids e
    ids (PCExists i) = [i]
    ids (AssumePC e pc) = ids e ++ ids pc
