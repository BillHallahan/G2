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

group    :: (Ord k) => List (k, v) -> M.Map k (List v)

\end{code}

\begin{code}
{-@ group :: (Ord k) => {l:List (k, v) | size l>0} -> M.Map k ({l:List v |size l>0}) @-}
group     = foldr addKV  M.empty

addKV (k,v) m = M.insert k vs' m
  where
    vs'       = (M.findWithDefault Emp k m)
\end{code}
