\begin{code}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-termination" @-}

module KMeans where

nearest   :: Int

{-@ nearest :: {x:Int | x < 5} @-}
nearest = x
        where (x,y) = head []
\end{code}