\begin{code}
{-# LANGUAGE ScopedTypeVariables #-}

module Group3 where

import Prelude hiding (Foldable (..))
import qualified Data.Map as M

import qualified Data.List as L


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
f = M.fromList [(2300, 2353)]

{-@ fs :: M.Map {z:Int | z < 1000} Int @-}
fs :: M.Map Int Int
fs = M.fromList [(2300, 2353)]



{-@ fs2 :: M.Map Int Int @-}
fs2 :: M.Map Int Int
fs2 = M.fromList []


{-@ f39 :: M.Map {z:Int | z < 1000} {y:Int | y < 4000 } @-}
f39 :: M.Map Int Int
f39 = M.fromList []


{-@ f2 :: Int -> [Int] @-}
f2 :: Int -> [Int]
f2 x = fromList2

{-@ fromList2 :: {z:[Int] | false} @-}
fromList2 :: [Int]
fromList2 = foldrX [] -- foldr (\x ys -> []) [] [] 

instance Foldable [] where
    foldrX  x = x
    sum     x = x

class Foldable t where
    foldrX :: t a -> t a
    sum :: t a -> t a

{-@ h :: {x:Int | x == 1000} @-}
h = h2

h2 :: Int
h2 = tcf 1

class Test a where
  tcf :: a -> a
  tcg :: a -> Int

instance Test Int where
  tcf x = x 
  tcg x = 33

tcfInt :: (Int -> Int) -> Int -> Int
tcfInt f x = f x

{-@ crashes :: {s:Int | s >= 0} @-}
crashes :: Int
crashes = foldr2 [0]

foldr2 :: [a] -> Int
foldr2 _ = 0


{-@ f3 :: {v:[Int] | false} @-}
f3 :: [Int]
f3 = g3 [0, 1]

{-# NOINLINE g3 #-}
g3 :: a -> a
g3 x = x

\end{code}
