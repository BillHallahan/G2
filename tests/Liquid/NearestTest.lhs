\begin{code}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-termination" @-}

module KMeans where

nearest   :: Int -> Int

{-@ nearest :: k:Int -> {x:Int | x < k} @-}
nearest k = x
        where (x,y) = head []

\end{code}