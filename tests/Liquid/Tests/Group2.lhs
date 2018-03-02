\begin{code}
module Group2 where

import Prelude hiding (foldr)
import qualified Data.Map as M

data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)
-- instance Targetable a => Targetable (List a)

{-@ measure size      :: List a -> Int
    size (Emp)        = 0
    size ((:+:) x xs) = 1 + size xs
  @-}

foldr :: (a -> b -> b) -> b -> List a -> b
foldr _  b Emp        = b
foldr op b (x :+: xs) = x `op` (foldr op b xs)

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

group2    :: (Int, Int) -> Int
{-@ group2 :: (Int, Int) -> {l:Int | l == 2} @-}
group2 kv    = 1

\end{code}
