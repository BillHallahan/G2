{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module G2.Language.PathConds ( PathConds
                             , PathCond (..)
                             , HashedPathCond
                             , Constraint
                             , Assertion
                             , mkAssumePC

                             , toUFMap
                             , toUFList
                             , empty
                             , fromList
                             , fromHashedList
                             , map
                             , mapHashedPCs
                             , map'
                             , filter
                             , alter
                             , alterHashed
                             , insert
                             , null
                             , number
                             , relatedSets
                             , scc
                             , varIdsInPC
                             , varNamesInPC
                             , toList
                             , toHashedList
                             , toHashSet
                             , union
                             -- , intersection
                             -- , difference
                             , mergeWithAssumePCs

                             , hashedPC
                             , unhashedPC
                             , mapHashedPC
                             , hashedAssumePC) where

import qualified G2.Data.UFMap as UF
import G2.Language.AST
import G2.Language.Ids
import qualified G2.Language.KnownValues as KV
import G2.Language.Naming
import G2.Language.Syntax

import Data.Coerce
import Data.Data (Data, Typeable)
import GHC.Generics (Generic)
import Data.Hashable
import qualified Data.HashSet as HS
import qualified Data.HashMap.Lazy as HM
import qualified Data.List as L
import qualified Data.Map as M
import Data.Map.Merge.Lazy
import Data.Maybe
import Prelude hiding (map, filter, null)
import qualified Prelude as P (map)

import Debug.Trace

-- | Conceptually, the path constraints are a graph, with (Maybe Name)'s Nodes.
-- Edges exist between any names that are in the same path constraint.
-- Strongly connected components in the graph must be checked and solved together.
newtype PathConds = PathConds (UF.UFMap (Maybe Name) (HS.HashSet HashedPathCond))
                    deriving (Show, Eq, Read, Typeable, Data)

-- | Path conditions represent logical constraints on our current execution
-- path. We can have path constraints enforced due to case/alt branching, due
-- to assertion / assumptions made, or some externally coded factors.
data PathCond = AltCond Lit Expr Bool -- ^ The expression and Lit must match
              | ExtCond Expr Bool -- ^ The expression must be a (true) boolean
              | AssumePC Id Integer HashedPathCond
              deriving (Show, Eq, Read, Generic, Typeable, Data)

type Constraint = PathCond
type Assertion = PathCond

instance Hashable PathCond where
    hashWithSalt s pc = s `hashWithSalt` hash pc

    hash (AltCond l e b) = (1 :: Int) `hashWithSalt` l `hashWithSalt` e `hashWithSalt` b
    hash (ExtCond e b) = (2 :: Int) `hashWithSalt` e `hashWithSalt` b
    hash (AssumePC i n pc) = hashAssumePC i n pc

{-# INLINE toUFMap #-}
toUFMap :: PathConds -> UF.UFMap (Maybe Name) (HS.HashSet HashedPathCond)
toUFMap = coerce

toUFList :: PathConds -> [([Maybe Name], HS.HashSet HashedPathCond)]
toUFList = mapMaybe (\(ns, pc) -> case pc of Just pc' -> Just (ns, pc'); Nothing -> Nothing) . UF.toList . toUFMap

{-# INLINE empty #-}
-- | Constructs an empty `PathConds`.
empty :: PathConds
empty = PathConds UF.empty

fromList :: [PathCond] -> PathConds
fromList = coerce . foldr insert empty

fromHashedList :: [HashedPathCond] -> PathConds
fromHashedList = coerce . foldr insertHashed empty

fromHashedHashSet :: HS.HashSet HashedPathCond -> PathConds
fromHashedHashSet = coerce . foldr insertHashed empty

map :: (PathCond -> PathCond) -> PathConds -> PathConds
map f = fromList . L.map f . toList

mapHashedPCs :: (HashedPathCond -> HashedPathCond) -> PathConds -> PathConds
mapHashedPCs f = fromHashedList . L.map f . toHashedList

map' :: (PathCond -> a) -> PathConds -> [a]
map' f = L.map f . toList

filter :: (PathCond -> Bool) -> PathConds -> PathConds
filter f = fromHashedList 
         . L.filter (f . unhashedPC)
         . toHashedList

alter :: (PathCond -> Maybe PathCond) -> PathConds -> PathConds
alter f = fromList . mapMaybe f . toList

alterHashed :: (HashedPathCond -> Maybe HashedPathCond) -> PathConds -> PathConds
alterHashed f = fromHashedList . mapMaybe f . toHashedList

-- Each name n maps to all other names that are in any PathCond containing n
-- However, each n does NOT neccessarily map to all PCs containing n- instead each
-- PC is associated with only one name.
-- This is ok, because the PCs can only be externally accessed by toList (which 
-- returns all PCs anyway) or scc (which forces exploration over all shared names)
{-# INLINE insert #-}
insert :: PathCond -> PathConds -> PathConds
insert pc = insertHashed (hashedPC pc)

insertHashed :: HashedPathCond -> PathConds -> PathConds
insertHashed pc (PathConds pcs) =
    let
        sing_pc = HS.singleton pc
    in
    case varNamesInPC (unhashedPC pc) of
        [] -> PathConds $ UF.insertWith HS.union Nothing sing_pc pcs
        vs@(v:_) ->
            let
                ins_pcs = UF.insertWith HS.union (Just v) sing_pc pcs
            in
            PathConds $ UF.joinAll (HS.union) (P.map Just vs) ins_pcs

{-# INLINE number #-}
number :: PathConds -> Int
number = length . toList

{-# INLINE null #-}
null :: PathConds -> Bool
null = UF.null . toUFMap

-- Returns a list of PathConds, where the union of the output PathConds
-- is the input PathConds, and the PathCond are seperated into there SCCs
relatedSets :: PathConds -> [PathConds]
relatedSets (PathConds ufm) =
    let
        c_ufm = UF.clear ufm
    in
    P.map (\(k, v) -> PathConds $ UF.insert k v c_ufm) $ HM.toList (UF.toSimpleMap ufm) 

varIdsInPC :: PathCond -> [Id]
-- [AltCond]
-- Optimization
-- When we have an AltCond with a Var expr, we only have to look at
-- other PC's with that Var's name.  This is because we assign all
-- DCs from the same part in a DC tree the same name, and a DC's
-- parents/children can't impose restrictions on it.  We are completely
-- guided by pattern matching from case statements.
-- See note [ChildrenNames] in Execution/Rules.hs
varIdsInPC (AltCond _ e _) = varIds e
varIdsInPC (ExtCond e _) = varIds e
varIdsInPC (AssumePC i _ pc) = i:varIdsInPC (unhashedPC pc)

varNamesInPC :: PathCond -> [Name]
varNamesInPC = P.map idName . varIdsInPC

-- {-# INLINE scc #-}
scc :: [Name] -> PathConds -> PathConds
scc ns (PathConds pcs) =
    let
        ns' = P.map (flip UF.lookupRep pcs . Just) ns
    in
    PathConds $ UF.filterWithKey (\k _ -> k `L.elem` ns') pcs

{-# INLINE toList #-}
toList :: PathConds -> [PathCond]
toList = P.map unhashedPC . toHashedList

{-# INLINE toHashedList #-}
toHashedList ::  PathConds -> [HashedPathCond]
toHashedList = HS.toList . toHashSet

{-# INLINE toHashSet #-}
toHashSet :: PathConds -> HS.HashSet HashedPathCond
toHashSet = HS.unions . UF.elems . toUFMap

union :: PathConds -> PathConds -> PathConds
union (PathConds pc1) (PathConds pc2) = PathConds $ UF.unionWith HS.union pc1 pc2

mergeWithAssumePCs :: Id -> PathConds -> PathConds -> PathConds
mergeWithAssumePCs i (PathConds pc1) (PathConds pc2) =
    let
        mrg = UF.mergeJoiningWithKey
                    (mergeMatched i)
                    (mergeOnlyIn i 1)
                    (mergeOnlyIn i 2)
                    HS.union
                    HS.union
                    HS.union
                    pc1 pc2
        pc = PathConds $ adjustNothing (idName i) mrg
    in
    pc
    
mergeOnlyIn :: Id -> Integer -> Maybe Name -> HS.HashSet HashedPathCond -> (HS.HashSet HashedPathCond, [(Maybe Name, Maybe Name)])
mergeOnlyIn i n k hpc =
    let
        n_hpc = HS.map (hashedAssumePC i n) hpc
    in
    (n_hpc, if not (HS.null n_hpc) then [(Just $ idName i, k)] else [])

mergeMatched :: Id
             -> Maybe Name
             -> HS.HashSet HashedPathCond
             -> HS.HashSet HashedPathCond
             -> (HS.HashSet HashedPathCond, [(Maybe Name, Maybe Name)])
mergeMatched i k hpc1 hpc2 =
    let
        both = HS.intersection hpc1 hpc2
        onlyIn1 = HS.map (hashedAssumePC i 1) $ HS.difference hpc1 hpc2
        onlyIn2 = HS.map (hashedAssumePC i 2) $ HS.difference hpc2 hpc1

        hpc = HS.union both (HS.union onlyIn1 onlyIn2)
        ks = if not (HS.null onlyIn1) || not (HS.null onlyIn2)
                    then [(Just $ idName i, k)]
                    else []
    in
    (hpc, ks)

adjustNothing :: Name
              -> UF.UFMap (Maybe Name) (HS.HashSet HashedPathCond)
              -> UF.UFMap (Maybe Name) (HS.HashSet HashedPathCond)
adjustNothing n hs
    | Just v <- UF.lookup Nothing hs = UF.insertWith (HS.union) (Just n) v hs
    | otherwise = hs

instance ASTContainer PathConds Expr where
    containedASTs = containedASTs . toUFMap
    
    modifyContainedASTs f = fromList . modifyContainedASTs f . toList

instance ASTContainer PathConds Type where
    containedASTs = containedASTs . toUFMap

    modifyContainedASTs f = fromList . modifyContainedASTs f . toList

instance ASTContainer PathCond Expr where
    containedASTs (ExtCond e _ )   = [e]
    containedASTs (AltCond _ e _) = [e]
    containedASTs (AssumePC _ _ pc) = containedASTs pc

    modifyContainedASTs f (ExtCond e b) = ExtCond (modifyContainedASTs f e) b
    modifyContainedASTs f (AltCond a e b) =
        AltCond (modifyContainedASTs f a) (modifyContainedASTs f e) b
    modifyContainedASTs f (AssumePC i num pc) = AssumePC i num (modifyContainedASTs f pc)

instance ASTContainer PathCond Type where
    containedASTs (ExtCond e _)   = containedASTs e
    containedASTs (AltCond e a _) = containedASTs e ++ containedASTs a
    containedASTs (AssumePC i _ pc) = containedASTs i ++ containedASTs pc

    modifyContainedASTs f (ExtCond e b) = ExtCond e' b
      where e' = modifyContainedASTs f e
    modifyContainedASTs f (AltCond e a b) = AltCond e' a' b
      where e' = modifyContainedASTs f e
            a' = modifyContainedASTs f a
    modifyContainedASTs f (AssumePC i num pc) = AssumePC (modifyContainedASTs f i) num (modifyContainedASTs f pc)

instance Named PathConds where
    -- In rename and renames, we loopup and rename individual keys, to avoid rehashing everything in the PathConds

    names = names . UF.toList . toUFMap

    rename old new (PathConds pcs) =
        let
            pcs' = UF.join HS.union (Just old) (Just new) pcs
        in
        case UF.lookup (Just old) pcs' of
            Just pc -> PathConds $ UF.insert (Just new) (rename old new pc) pcs'
            Nothing -> PathConds pcs'

    renames hm (PathConds pcs) =
        let
            rep_ns = L.foldr (\k -> HS.insert (UF.find (Just k) pcs)) HS.empty $ HM.keys hm
            pcs' = L.foldr (\(k1, k2) -> UF.join HS.union (Just k1) (Just k2)) pcs $ HM.toList hm
        in
        PathConds $ L.foldr (\k pcs_ -> 
                                case UF.lookup k pcs_ of
                                    Just pc -> UF.insert k (renames hm pc) pcs_
                                    Nothing -> pcs_) pcs' rep_ns

instance Named PathCond where
    names (AltCond _ e _) = names e
    names (ExtCond e _) = names e
    names (AssumePC i _ pc) = names i ++ names pc

    rename old new (AltCond l e b) = AltCond l (rename old new e) b
    rename old new (ExtCond e b) = ExtCond (rename old new e) b
    rename old new (AssumePC i num pc) = AssumePC (rename old new i) num (rename old new pc)

    renames hm (AltCond l e b) = AltCond l (renames hm e) b
    renames hm (ExtCond e b) = ExtCond (renames hm e) b
    renames hm (AssumePC i num pc) = AssumePC (renames hm i) num (renames hm pc)

instance Ided PathConds where
    ids = ids . toUFMap

instance Ided PathCond where
    ids (AltCond _ e _) = ids e
    ids (ExtCond e _) = ids e
    ids (AssumePC i _ pc) = ids i ++ ids pc

data HashedPathCond = HashedPC PathCond {-# UNPACK #-} !Int
              deriving (Show, Read, Typeable, Data)

hashedPC :: PathCond -> HashedPathCond
hashedPC pc = HashedPC pc (hash pc)

unhashedPC :: HashedPathCond -> PathCond
unhashedPC (HashedPC pc _) = pc

mapHashedPC :: (PathCond -> PathCond) -> HashedPathCond -> HashedPathCond
mapHashedPC f (HashedPC pc _) = hashedPC (f pc)

instance Eq HashedPathCond where
    HashedPC pc h == HashedPC pc' h' = if h /= h' then False else pc == pc'

instance Hashable HashedPathCond where
    hashWithSalt s (HashedPC _ h) = s `hashWithSalt` h
    hash (HashedPC _ h) = h

instance ASTContainer HashedPathCond Expr where
    containedASTs = containedASTs . unhashedPC
    modifyContainedASTs f = mapHashedPC (modifyContainedASTs f)

instance ASTContainer HashedPathCond Type where
    containedASTs = containedASTs . unhashedPC
    modifyContainedASTs f = mapHashedPC (modifyContainedASTs f)

instance Named HashedPathCond where
    names = names . unhashedPC
    rename old new = mapHashedPC (rename old new)
    renames hm = mapHashedPC (renames hm)

instance Ided HashedPathCond where
  ids = ids . unhashedPC


mkAssumePC :: Id -> Integer -> PathCond -> PathCond
mkAssumePC i n pc = AssumePC i n (hashedPC pc)

hashedAssumePC :: Id -> Integer -> HashedPathCond -> HashedPathCond
hashedAssumePC i n hpc@(HashedPC _ h) = HashedPC (AssumePC i n hpc) (hashAssumePCFromHash i n h)

-- | Helper functions to compute the hash of an AssumePC in various ways
hashAssumePC :: Id -> Integer -> HashedPathCond -> Int
hashAssumePC i n pc = hashAssumePCFromHash i n (hash pc)

hashAssumePCFromHash :: Id
                     -> Integer
                     -> Int -- ^ The hash of the contained PathCond
                     -> Int
hashAssumePCFromHash i n h = (4 :: Int) `hashWithSalt` i `hashWithSalt` n `hashWithSalt` h
