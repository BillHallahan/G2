{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module G2.Language.PathConds ( PathConds(..)
                             , PathCond (..)
                             , HashedPathCond
                             , Constraint
                             , Assertion
                             , mkAssumePC

                             , toMap
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
                             , relevant
                             , relatedSets
                             , scc
                             , pcNames
                             , varIdsInPC
                             , varNamesInPC
                             , toList
                             , toHashedList
                             , toHashSet
                             , union
                             , intersection
                             , difference
                             , mergeWithAssumePCs

                             , hashedPC
                             , unhashedPC
                             , mapHashedPC
                             , hashedAssumePC) where

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
import qualified Data.List as L
import qualified Data.Map as M
import Data.Map.Merge.Lazy
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
newtype PathConds = PathConds (M.Map (Maybe Name) (HS.HashSet HashedPathCond, HS.HashSet Name))
                    deriving (Show, Eq, Read, Typeable, Data)

-- | Path conditions represent logical constraints on our current execution
-- path. We can have path constraints enforced due to case/alt branching, due
-- to assertion / assumptions made, or some externally coded factors.
data PathCond = AltCond Lit Expr Bool -- ^ The expression and Lit must match
              | ExtCond Expr Bool -- ^ The expression must be a (true) boolean
              | ConsCond DataCon Expr Bool -- ^ The expression and datacon must match
              | AssumePC Id Integer HashedPathCond
              deriving (Show, Eq, Read, Generic, Typeable, Data)

type Constraint = PathCond
type Assertion = PathCond

instance Hashable PathCond where
    hashWithSalt s pc = s `hashWithSalt` hash pc

    hash (AltCond l e b) = (1 :: Int) `hashWithSalt` l `hashWithSalt` e `hashWithSalt` b
    hash (ExtCond e b) = (2 :: Int) `hashWithSalt` e `hashWithSalt` b
    hash (ConsCond d e b) = (3 :: Int) `hashWithSalt` d `hashWithSalt` e `hashWithSalt` b
    hash (AssumePC i n pc) = hashAssumePC i n pc

{-# INLINE toMap #-}
toMap :: PathConds -> M.Map (Maybe Name) (HS.HashSet HashedPathCond, HS.HashSet Name)
toMap = coerce

{-# INLINE empty #-}
-- | Constructs an empty `PathConds`.
empty :: PathConds
empty = PathConds M.empty

fromList :: [PathCond] -> PathConds
fromList = coerce . foldr insert empty

fromHashedList :: [HashedPathCond] -> PathConds
fromHashedList = coerce . foldr insertHashed empty

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
insert pc = insert' varNamesInPC (hashedPC pc)

insertHashed :: HashedPathCond -> PathConds -> PathConds
insertHashed = insert' varNamesInPC

insert' :: (PathCond -> [Name]) -> HashedPathCond -> PathConds -> PathConds
insert' f p (PathConds pcs) =
    let
        ns = f (unhashedPC p)

        (hd, insertAt) = case ns of
            [] -> (Nothing, [Nothing])
            (h:_) -> (Just h, P.map Just ns)
    in
    PathConds $ M.adjust (\(p', ns') -> (HS.insert p p', ns')) hd
              $ foldr (M.alter (insert'' ns)) pcs insertAt

insert'' :: [Name] -> Maybe (HS.HashSet HashedPathCond, HS.HashSet Name) -> Maybe (HS.HashSet HashedPathCond, HS.HashSet Name)
insert'' ns Nothing = Just (HS.empty, HS.fromList ns)
insert'' ns (Just (p', ns')) = Just (p', HS.union (HS.fromList ns) ns')

{-# INLINE number #-}
number :: PathConds -> Int
number = length . toList

{-# INLINE null #-}
null :: PathConds -> Bool
null = M.null . toMap

-- | Filters a PathConds to only those PathCond's that potentially impact the
-- given PathCond's satisfiability (i.e. they are somehow linked by variable names)
relevant :: [PathCond] -> PathConds -> PathConds
relevant pc pcs =
    case concatMap varNamesInPC pc of
        [] -> fromList pc
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
              ns' = concat $ map' varNamesInPC s
          in
          s:relatedSets' kv pc (ns L.\\ (k:ns'))
      [] ->  []

-- | Returns list of Names of all the nodes in the PathConds
pcNames :: PathConds -> [Name]
pcNames pc = catMaybes . M.keys $ toMap pc

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
varIdsInPC (ConsCond _ e _) = varIds e
varIdsInPC (AssumePC i _ pc) = i:varIdsInPC (unhashedPC pc)

varNamesInPC :: PathCond -> [Name]
varNamesInPC = P.map idName . varIdsInPC

{-# INLINE scc #-}
scc :: [Name] -> PathConds -> PathConds
scc ns (PathConds pc) = PathConds $ scc' ns pc M.empty

scc' :: [Name]
     -> (M.Map (Maybe Name) (HS.HashSet HashedPathCond, HS.HashSet Name))
     -> (M.Map (Maybe Name) (HS.HashSet HashedPathCond, HS.HashSet Name))
     -> (M.Map (Maybe Name) (HS.HashSet HashedPathCond, HS.HashSet Name))
scc' [] _ pc = pc
scc' (n:ns) pc newpc =
    -- Check if we already inserted the name information
    case M.lookup (Just n) newpc of
        Just _ -> scc' ns pc newpc
        Nothing ->
            -- If we didn't, lookup info to insert,
            -- and add names to the list of names to search
            case M.lookup (Just n) pc of
                Just pcn@(_, ns') -> scc' (ns ++ (HS.toList ns')) pc (M.insert (Just n) pcn newpc)
                Nothing -> scc' ns pc newpc

{-# INLINE toList #-}
toList :: PathConds -> [PathCond]
toList = P.map unhashedPC . concatMap (HS.toList . fst) . M.elems . toMap

{-# INLINE toHashedList #-}
toHashedList ::  PathConds -> [HashedPathCond]
toHashedList = concatMap (HS.toList . fst) . M.elems . toMap

{-# INLINE toHashSet #-}
toHashSet :: PathConds -> HS.HashSet HashedPathCond
toHashSet = HS.unions . P.map fst . M.elems . toMap

union :: PathConds -> PathConds -> PathConds
union (PathConds pc1) (PathConds pc2) = PathConds $ M.unionWith union' pc1 pc2
    where
        union' (hpc1, hn1) (hpc2, hn2) = (HS.union hpc1 hpc2, HS.union hn1 hn2)

intersection :: PathConds -> PathConds -> PathConds
intersection (PathConds pc1) (PathConds pc2) = PathConds $ M.intersectionWith inter pc1 pc2
    where
        inter (hpc1, hn1) (hpc2, hn2) = (HS.intersection hpc1 hpc2, HS.intersection hn1 hn2)

difference :: PathConds -> PathConds -> PathConds
difference (PathConds pc1) (PathConds pc2) =
    PathConds $ M.differenceWith diff pc1 pc2
        where
            diff (hpc1, hn1) (hpc2, hn2) = Just (HS.difference hpc1 hpc2, HS.difference hn1 hn2)

mergeWithAssumePCs :: Id -> PathConds -> PathConds -> PathConds
mergeWithAssumePCs i (PathConds pc1) (PathConds pc2) = 
    let
        (ns, merged) = mergeA 
                          (traverseMissing $ mergeOnlyIn i 1) 
                          (traverseMissing $ mergeOnlyIn i 2) 
                          (zipWithAMatched $ mergeMatched i)
                          pc1 pc2
    in
    PathConds $ M.insert (Just $ idName i) (HS.empty, ns) merged

mergeOnlyIn :: Id -> Integer -> Maybe Name -> (HS.HashSet HashedPathCond, HS.HashSet Name) -> (HS.HashSet Name, (HS.HashSet HashedPathCond, HS.HashSet Name))
mergeOnlyIn i n _ (hpc, hn) =
    let
        hn' = HS.insert (idName i) hn
    in
    ( hn'
    , ( HS.map (hashedAssumePC i n) hpc
      , hn')
    )

mergeMatched :: Id
             -> Maybe Name
             -> (HS.HashSet HashedPathCond, HS.HashSet Name)
             -> (HS.HashSet HashedPathCond, HS.HashSet Name)
             -> (HS.HashSet Name, (HS.HashSet HashedPathCond, HS.HashSet Name))
mergeMatched i _ (hpc1, hn1) (hpc2, hn2) =
    let
        both = HS.intersection hpc1 hpc2
        onlyIn1 = HS.map (hashedAssumePC i 1) $ HS.difference hpc1 hpc2
        onlyIn2 = HS.map (hashedAssumePC i 2) $ HS.difference hpc2 hpc1

        union_hn = HS.union hn1 hn2

        hn = if not (HS.null onlyIn1) || not (HS.null onlyIn2)
                then HS.insert (idName i) union_hn
                else union_hn
    in
    ( hn
    , ( HS.union both (HS.union onlyIn1 onlyIn2)
      , hn)
    )

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
    containedASTs (AssumePC _ _ pc) = containedASTs pc

    modifyContainedASTs f (ExtCond e b) = ExtCond (modifyContainedASTs f e) b
    modifyContainedASTs f (AltCond a e b) =
        AltCond (modifyContainedASTs f a) (modifyContainedASTs f e) b
    modifyContainedASTs f (ConsCond dc e b) =
        ConsCond (modifyContainedASTs f dc) (modifyContainedASTs f e) b
    modifyContainedASTs f (AssumePC i num pc) = AssumePC i num (modifyContainedASTs f pc)

instance ASTContainer PathCond Type where
    containedASTs (ExtCond e _)   = containedASTs e
    containedASTs (AltCond e a _) = containedASTs e ++ containedASTs a
    containedASTs (ConsCond dcl e _) = containedASTs dcl ++ containedASTs e
    containedASTs (AssumePC i _ pc) = containedASTs i ++ containedASTs pc

    modifyContainedASTs f (ExtCond e b) = ExtCond e' b
      where e' = modifyContainedASTs f e
    modifyContainedASTs f (AltCond e a b) = AltCond e' a' b
      where e' = modifyContainedASTs f e
            a' = modifyContainedASTs f a
    modifyContainedASTs f (ConsCond dc e b) =
        ConsCond (modifyContainedASTs f dc) (modifyContainedASTs f e) b
    modifyContainedASTs f (AssumePC i num pc) = AssumePC (modifyContainedASTs f i) num (modifyContainedASTs f pc)

instance Named PathConds where
    names (PathConds pc) = (catMaybes $ M.keys pc) ++ concatMap (\(p, n) -> names p ++ (HS.toList n)) pc

    rename old new (PathConds pc) =
        PathConds . M.mapKeys (\k -> if k == (Just old) then (Just new) else k)
                  $ rename old new pc

    renames hm (PathConds pc) =
        PathConds . M.mapKeys (renames hm)
                  $ renames hm pc

instance Named PathCond where
    names (AltCond _ e _) = names e
    names (ExtCond e _) = names e
    names (ConsCond d e _) = names d ++  names e
    names (AssumePC i _ pc) = names i ++ names pc

    rename old new (AltCond l e b) = AltCond l (rename old new e) b
    rename old new (ExtCond e b) = ExtCond (rename old new e) b
    rename old new (ConsCond d e b) = ConsCond (rename old new d) (rename old new e) b
    rename old new (AssumePC i num pc) = AssumePC (rename old new i) num (rename old new pc)

    renames hm (AltCond l e b) = AltCond l (renames hm e) b
    renames hm (ExtCond e b) = ExtCond (renames hm e) b
    renames hm (ConsCond d e b) = ConsCond (renames hm d) (renames hm e) b
    renames hm (AssumePC i num pc) = AssumePC (renames hm i) num (renames hm pc)

instance Ided PathConds where
    ids = ids . toMap

instance Ided PathCond where
    ids (AltCond _ e _) = ids e
    ids (ExtCond e _) = ids e
    ids (ConsCond d e _) = ids d ++  ids e
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
