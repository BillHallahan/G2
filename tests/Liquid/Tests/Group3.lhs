\begin{code}
module Group3 where

import Prelude hiding (foldr)
import qualified Data.Map as M

import Data.List as L

data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)
-- instance Targetable a => Targetable (List a)

{-@ measure size      :: List a -> Int
    size (Emp)        = 0
    size ((:+:) x xs) = 1 + size xs
  @-}

-- foldr :: (a -> b -> b) -> b -> List a -> b
-- foldr _  b Emp        = b
-- foldr op b (x :+: xs) = x `op` (foldr op b xs)

\end{code}


\begin{code}

data X = X

{-@ measure size2      :: X -> Int
    size2 X        = 0
  @-}

group    :: (Int, Int) -> M.Map Int X
{-@ group :: (Int, Int) -> M.Map Int ({l:X |size2 l > 0}) @-}
group kv    = addKV

addKV :: M.Map Int X
addKV = M.insert 0 X M.empty

{-@ f :: M.Map {z:Int | z < 1000} {y:Int | y < 4000 } @-}
f :: M.Map Int Int
f = M.fromList [(23, 2353)]


data Map2 k a = Assocs2 [(k, a)]

{-@ f2 :: [Int] @-}
f2 :: [Int]
f2 = fromList2

fromList2 :: [Int]
fromList2 = sby 
  where
    sby = L.foldr (\x ys -> []) [] []

foldr3            :: (a -> b -> b) -> b -> [a] -> b
foldr3 k z = go
          where
            go []     = z
            go (y:ys) = y `k` go ys



{-@ crashes :: {s:Int | s >= 0} @-}
crashes :: Int
crashes = foldr2 [0]

foldr2 :: [a] -> Int
foldr2 _ = 0


\end{code}
