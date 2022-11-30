-- Based on:
-- A Persistent Union-Find Data Structure
-- by Sylvain Conchon and Jean-Cristophe Filliatre

{-# OPTIONS_GHC -fno-warn-orphans -fno-full-laziness #-}

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE InstanceSigs #-}

module G2.Data.UnionFind ( UnionFind
                         , empty
                         , fromList
                         , toList
                         , toSet
                         , union
                         , unionOfUFs
                         , find) where

import Data.Data (Data (..), Typeable)
import Data.Hashable
import qualified Data.HashMap.Lazy as M
import qualified Data.HashSet as S
import Data.IORef

import System.IO.Unsafe

import Text.Read
import qualified Text.Read.Lex as L
import GHC.Read

import Test.Tasty.QuickCheck

data UnionFind k = UF { rank :: M.HashMap k Int
                      , parent :: IORef (M.HashMap k k) }
                      deriving (Typeable, Data)

{-# NOINLINE empty #-}
empty :: UnionFind k
empty = UF { rank = M.empty
           , parent = unsafePerformIO $ newIORef M.empty }

-- | Build a UnionFind uf, where if k1, k2 are in the same input list,
-- find k1 uf == find k2 uf
fromList :: (Eq k, Hashable k) => [[k]] -> UnionFind k
fromList = foldr unions empty

toList :: (Eq k, Hashable k) => UnionFind k -> [[k]]
toList = map S.toList . S.toList . toSet

toSet :: (Eq k, Hashable k) => UnionFind k -> S.HashSet (S.HashSet k)
toSet uf =
    let
        par = unsafePerformIO $ readIORef (parent uf)
        m = foldr (\k -> M.insertWith S.union (find k uf) $ S.singleton k) M.empty (M.keys par)
    in
    S.fromList . map (\(k, v) -> S.insert k v) $ M.toList m

{-# NOINLINE union #-}
union :: (Eq k, Hashable k) => k -> k -> UnionFind k -> UnionFind k
union x y h =
    let
        cx = find x h
        cy = find y h
    in
    if cx /= cy
        then
            let
                rx = M.lookupDefault 0 cx (rank h)
                ry = M.lookupDefault 0 cy (rank h)
            in
            if rx > ry
                then unsafePerformIO $ do
                    par_h <- readIORef (parent h)
                    par_h' <- newIORef (M.insert cy cx par_h)
                    return $ h { parent = par_h' } 
            else if rx < ry
                then unsafePerformIO $ do
                    par_h <- readIORef (parent h)
                    par_h' <- newIORef (M.insert cx cy par_h)
                    return $ h { parent = par_h' }
            else unsafePerformIO $ do
                par_h <- readIORef (parent h)
                par_h' <- newIORef (M.insert cy cx par_h)
                return $ h { rank = M.insert cx (rx + 1)  (rank h)
                           , parent = par_h' } 
        else h

unions :: (Eq k, Hashable k) => [k] -> UnionFind k -> UnionFind k
unions ks uf = foldr (uncurry union) uf prod
    where prod = [(k1, k2) | k1 <- ks, k2 <- ks]

-- | Take the union of two @UnionFind@s, by taking the union of any overlapping sets.
{-# NOINLINE unionOfUFs #-}
unionOfUFs :: (Eq k, Hashable k) => UnionFind k -> UnionFind k -> UnionFind k
unionOfUFs uf1 (UF { parent = par }) = unsafePerformIO $ do
    par' <- readIORef par
    return $ M.foldrWithKey union uf1 par'

{-# NOINLINE find #-}
find :: (Eq k, Hashable k) => k -> UnionFind k -> k
find x h =
    unsafePerformIO (do
        h_par <- readIORef (parent h)
        let (cx, f) = findAux x h_par
        atomicWriteIORef (parent h) f
        return cx
    )

findAux :: (Eq k, Hashable k) => k -> M.HashMap k k -> (k, M.HashMap k k)
findAux i f =
    let fi = M.lookupDefault i i f in
    if fi == i
        then (i, f)
        else
            let
                (r, f') = findAux fi f
                f'' = M.insert i r f'
            in
            (r, f'')
            
instance (Eq k, Hashable k) => Eq (UnionFind k) where
    x == y = toSet x == toSet y 

instance (Eq k, Hashable k, Show k) => Show (UnionFind k) where
    {-# NOINLINE show #-}
    show uf = "fromList " ++ show (toList uf) 

instance (Eq k, Hashable k, Read k) => Read (UnionFind k) where
    readPrec = parens $
                    do expectP (L.Ident "fromList")
                       x <- step readListPrec
                       return (fromList x)
    readListPrec = readListPrecDefault 

instance (Eq k, Hashable k) => Hashable (UnionFind k) where
    hashWithSalt i = hashWithSalt i . toList

instance (Eq k, Hashable k) => Semigroup (UnionFind k) where
    (<>) = unionOfUFs

instance (Eq k, Hashable k) => Monoid (UnionFind k) where
    mempty = empty

instance (Arbitrary k, Eq k, Hashable k) => Arbitrary (UnionFind k) where
    arbitrary :: (Arbitrary k, Eq k, Hashable k) => Gen (UnionFind k)
    arbitrary = do       
        ks <- arbitrary

        return $ fromList ks

    shrink = map fromList . shrink . toList

-- Hack for compilation
instance Typeable a => Data (IORef a) where
  toConstr _   = error "toConstr"
  gunfold _ _  = error "gunfold"
  dataTypeOf _ = error "dataTypeOf"
