{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined (f) where
    
f :: Int -> Int
f = g

{-@ g :: { xs: Int | false } -> Int @-}
g :: Int -> Int
g _ = 1