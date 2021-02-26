{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}

module G2.Execution.Merging.MergeGraph ( Status (..)
                                       , work) where

import Prelude hiding (lookup)

import Control.Monad
import Data.Coerce
import Data.Data
import Data.Hashable
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Sequence as Seq

import GHC.Generics (Generic)

data Status k = Accept | Discard | Switch | KeepWorking | Split k | Merge k deriving Show

data AtMerge k = AtMerge k | NotAtMerge deriving (Eq, Ord, Show, Generic, Typeable)

data Mergeable v = Mergeable { merge_val :: v, merge_count :: Int }

instance Hashable k => Hashable (AtMerge k)

-- | We want to work on values v until they hit the same merge point k.
-- Then, we insert them into the Map for there corresponding ord.
-- We work on the ords in order of smallest to largest.
-- By ensuring that there are only finite numbers of values that can be
-- assigned the same ord, we ensure progress.
newtype MergeGraph ord k v = MergeGraph { merge_graph :: M.Map ord (M.Map (AtMerge k) [v]) }

type WorkOrder k = Seq.Seq (AtMerge k)

work :: (Show ord, Show k, Ord ord, Ord k)
     => (s -> b -> IO ([s], b, Status k)) -- ^ Work function
     -> (s -> s -> b -> IO (Maybe s, b)) -- ^ Merge function
     -> (s -> b -> Maybe (s, b)) -- ^ Switched to function
     -> ([s] -> b -> ord) -- ^ Ordering function- states with lower orders get processed first
     -> [s]
     -> b
     -> IO ([s], b)
work _ _ _ _ [] b = return ([], b)
work work_fn merge_fn switch_to_fn order_fn (ix:ixs) ib = go (MergeGraph M.empty) Seq.empty [] ix ixs ib
    where
        go wg m_ord acc x xs b = do
            -- print (M.map (M.map length) $ merge_graph wg)
            (ev_xs, b', status) <- work_fn x b
            if not (null ev_xs) then print (order_fn ev_xs b') else return ()

            case status of
                Accept -> pickNew wg m_ord (ev_xs ++ acc) xs b'
                Discard -> pickNew wg m_ord acc xs b'
                KeepWorking
                    | not (null ev_xs)
                    , ord <- order_fn ev_xs b'
                    , Just (min_ord, _) <- lookupMinOrd wg
                    , ord > min_ord -> do
                        putStrLn $ "switch = " ++ show ord
                        print (M.map (M.map length) $ merge_graph wg)
                        let (wg', m_ord') = switch wg m_ord NotAtMerge ev_xs b'
                        pickNew wg' m_ord' acc xs b'
                    | otherwise ->
                        case ev_xs ++ xs of
                            x':xs' -> go wg m_ord acc x' xs' b'
                            [] -> pickNew wg m_ord acc [] b'
                Switch ->
                    let
                        (wg', m_ord') = switch wg m_ord NotAtMerge ev_xs b'
                    in
                    pickNew wg' m_ord' acc xs b'
                Split k ->
                    let
                        m_ord' = AtMerge k Seq.:<| m_ord -- m_ord Seq.:|> AtMerge k
                    in
                    case ev_xs ++ xs of
                        x':xs' -> go wg m_ord' acc x' xs' b'
                        [] -> error "Reducer returned empty list"
                Merge k -> do
                    putStrLn $ "merge = " ++ show k
                    print (M.map (M.map length) $ merge_graph wg)
                    let (wg', m_ord') = switch wg m_ord (AtMerge k) ev_xs b'
                    pickNew wg' m_ord' acc xs b'

        switch wg m_ord am_k [] b = (wg, m_ord)
        switch wg m_ord am_k xs b =
            let
                ord = order_fn xs b
                (prev, wg') = addToNodeLookup ord am_k xs wg
            in
            (wg', m_ord)

        pickNew wg m_ord acc (x:xs) b =
            case switch_to_fn x b of
                Just (x', b') -> go wg m_ord acc x' xs b'
                Nothing -> pickNew wg m_ord acc xs b
        pickNew wg m_ord acc [] b
            | Just (ord, k, xs) <- lookupNext wg = do
                (m_xs, b') <- case k of 
                                NotAtMerge -> return (xs, b)
                                AtMerge _ -> mergeList merge_fn b xs
                let wg' = delete ord k wg
                pickNew wg' m_ord acc m_xs b'
            | otherwise = return (acc, b)

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

addToNode :: (Ord ord, Ord k) => ord -> AtMerge k -> [v] -> MergeGraph ord k v -> MergeGraph ord k v
addToNode ord k v = MergeGraph 
                  . M.alter (Just . maybe (M.singleton k v) (M.insertWith (++) k v)) ord
                  . coerce

-- | Add to node, while returning the list of values previously at the node
addToNodeLookup :: (Ord ord, Ord k) => ord -> AtMerge k -> [v] -> MergeGraph ord k v -> (Maybe [v], MergeGraph ord k v)
addToNodeLookup ord k v =
      fmap MergeGraph
    . M.alterF ( fmap Just 
               . maybe 
                    (Nothing, M.singleton k v)
                    (M.alterF (maybe (Nothing, Just v) (\old -> (Just old, Just $ v ++ old))) k)
               ) ord
    . coerce -- alterF (\old -> (old, Just v)) k

lookup :: (Ord ord, Ord k) => ord -> AtMerge k -> MergeGraph ord k v -> Maybe [v]
lookup ord k mg = M.lookup k =<< M.lookup ord (coerce mg)

lookupMin :: (Ord ord, Ord k) => AtMerge k -> MergeGraph ord k v -> Maybe (ord, [v])
lookupMin k mg = do
    (ord, hm) <- lookupMinOrd mg
    vs <- M.lookup k hm
    return (ord, vs)

-- | We want to select a state with the smallest ordering, but at the latest (largest) merge point
lookupNext :: (Ord ord, Ord k) => MergeGraph ord k v -> Maybe (ord, AtMerge k, [v])
lookupNext mg = do
    (ord, vm) <- lookupMinOrd mg
    (k, vs) <- M.lookupMax vm
    return (ord, k, vs)

lookupMinOrd :: (Ord ord) => MergeGraph ord k v -> Maybe (ord, M.Map (AtMerge k) [v])
lookupMinOrd = M.lookupMin . coerce

delete :: (Ord ord, Ord k) => ord -> AtMerge k -> MergeGraph ord k v -> MergeGraph ord k v
delete ord k = MergeGraph
             . M.update (\m ->
                            let
                                m' = M.delete k m
                            in
                            if M.null m' then Nothing else Just m') ord . coerce
