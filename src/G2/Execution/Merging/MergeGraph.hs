{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}

module G2.Execution.Merging.MergeGraph ( Status (..)
                                       , work) where

import Prelude hiding (lookup)

import Control.Monad
import Data.Coerce
import Data.Data
import Data.Hashable
import qualified Data.HashMap.Strict as M
import Data.Maybe
import qualified Data.Sequence as S

import GHC.Generics (Generic)

data Status k = Accept | Discard | Switch | KeepWorking | Merge k deriving Show

data AtMerge k = AtMerge k | NotAtMerge deriving (Eq, Show, Generic, Typeable)

instance Hashable k => Hashable (AtMerge k)

newtype MergeGraph k v = MergeGraph (M.HashMap (AtMerge k) [v])

type WorkOrder k = S.Seq (AtMerge k)

work :: (Eq k, Hashable k, Show k)
     => (s -> b -> IO ([s], b, Status k)) -- ^ Work function
     -> (s -> s -> b -> IO (Maybe s, b)) -- ^ Merge function
     -> (s -> b -> Maybe (s, b)) -- ^ Switched to function
     -> [s]
     -> b
     -> IO ([s], b)
work _ _ _ [] b = return ([], b)
work work_fn merge_fn switch_fn (ix:ixs) ib = go (MergeGraph M.empty) S.empty [] ix ixs ib
    where
        go wg ord acc x xs b = do
            (ev_xs, b', status) <- work_fn x b

            case status of
                Accept -> pickNew wg ord (ev_xs ++ acc) xs b'
                Discard -> pickNew wg ord acc xs b'
                KeepWorking ->
                    case ev_xs ++ xs of
                        x':xs' -> go wg ord acc x' xs' b'
                        [] -> pickNew wg ord acc [] b'
                Switch ->
                    let
                        (wg', ord') = switch wg ord NotAtMerge ev_xs
                    in
                    pickNew wg' ord' acc xs b'
                Merge k ->
                    let
                        (wg', ord') = switch wg ord (AtMerge k) ev_xs
                    in
                    pickNew wg' ord' acc xs b'

        switch wg ord am_k xs =
            let
                (prev, wg') = addToNodeLookup am_k xs wg
                ord' = if isJust prev then ord else (ord S.:|> am_k)
            in
            (wg', ord')

        pickNew wg ord acc (x:xs) b =
            case switch_fn x b of
                Just (x', b') -> go wg ord acc x' xs b'
                Nothing -> pickNew wg ord acc xs b
        pickNew wg ord acc [] b =
            case ord of
                S.Empty -> return (acc, b)
                k S.:<| ord'
                    | Just xs <- lookup k wg -> do
                        (m_xs, b') <- case k of 
                                        NotAtMerge -> return (xs, b)
                                        AtMerge _ -> mergeList merge_fn b xs
                        let wg' = delete k wg
                        pickNew wg' ord' acc m_xs b'
                    | otherwise -> pickNew wg ord' acc [] b

mergeList :: Monad m => (s -> s -> b -> m (Maybe s, b)) -> b -> [s] -> m ([s], b)
mergeList merge_fn b (x:xs) =
    foldM (\(xs, b') s -> mergeWherePossible merge_fn b' s xs) ([x], b) xs
mergeList _ b [] = return ([], b)

mergeWherePossible :: Monad m => (s -> s -> b -> m (Maybe s, b)) -> b -> s -> [s] -> m ([s], b)
mergeWherePossible merge_fn b s = go []
    where
        go chcked [] = return $ (s:chcked, b)
        go chcked (x:xs) = do
            r <- merge_fn s x b
            case r of
                (Just ms, b') -> return (ms:chcked ++ xs, b')
                _ -> go (x:chcked) xs

addToNode :: (Eq k, Hashable k) => AtMerge k -> [v] -> MergeGraph k v -> MergeGraph k v
addToNode k v = MergeGraph . M.insertWith (++) k v . coerce

-- | Add to node, while returning the list of values previously at the node
addToNodeLookup :: (Eq k, Hashable k) => AtMerge k -> [v] -> MergeGraph k v -> (Maybe [v], MergeGraph k v)
addToNodeLookup k v = fmap MergeGraph
                    . M.alterF (maybe (Nothing, Just v) (\old -> (Just old, Just $ v ++ old))) k
                    . coerce -- alterF (\old -> (old, Just v)) k

lookup :: (Eq k, Hashable k) => AtMerge k -> MergeGraph k v -> Maybe [v]
lookup k = M.lookup k . coerce

delete :: (Eq k, Hashable k) => AtMerge k -> MergeGraph k v -> MergeGraph k v
delete k = MergeGraph . M.delete k . coerce