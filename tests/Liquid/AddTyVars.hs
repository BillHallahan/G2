{-@ LIQUID "--prune-unsorted" @-}

module AddTyVars where

{-@ f :: x:[[a]] -> {v:[a] | False } @-}
f :: [[a]] -> [a]
f [] = []
f (xs:_) = xs

{-@ measure sumsize @-}
sumsize :: [[a]] -> Int
sumsize [] = 0
sumsize (x:xs) = sumsize xs

{-@ g :: x:[[a]] -> {v:[a] | 1 == sumsize x } @-}
g :: [[a]] -> [a]
g [] = []
g (xs:_) = xs

{-@ h :: x:[a] -> {v:[a] | False } @-}
h :: [a] -> [a]
h [] = []
h xs = xs
