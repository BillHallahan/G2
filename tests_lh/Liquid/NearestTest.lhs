\begin{code}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-termination" @-}

module Nearest where


{-@ nearest :: {x:Int | x < 5} @-}
nearest :: Int
nearest = x
        where (x,y) = head []

{-@ nearest2 :: Int @-}
nearest2 :: Int
nearest2 = head []
\end{code}