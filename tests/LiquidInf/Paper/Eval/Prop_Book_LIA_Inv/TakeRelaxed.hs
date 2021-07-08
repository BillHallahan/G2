
module TakeRelaxed (test) where

import Prelude hiding (take)

take :: Int -> [a] -> [a]
take 0 _       = []
take _ []      = []
take n (x:xs)  = x : take (n-1) xs

{-@ test :: [{ xs:[String] | len xs == 2 }] @-}
test = [ take 2  ["cat", "dog", "mouse"]
       , take 20 ["cow", "goat"]        ]

{-@ LIQUID "--no-termination" @-}
