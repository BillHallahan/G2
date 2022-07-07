{-@ LIQUID "--no-termination" @-}

module Various (mainSum, mainMult, mainMC) where

import Prelude hiding (sum)

{-@ type TRUE = {v:Bool | v} @-}

{-@ die :: {v:String | false} -> a @-}
die str = error str

{-@ assert :: TRUE -> a -> a @-}
assert :: Bool -> a -> a
assert True x = x
assert _ _ = die "violated assert"

sum :: Int -> Int
sum n = if n <= 0 then 0 else n + sum (n - 1)

mainSum :: Int -> ()
mainSum n = assert (n <= sum n) ()

mult :: Int -> Int -> Int
mult n m = if n <= 0 || m <= 0 then 0 else n + mult n (m - 1)

mainMult :: Int -> ()
mainMult n = assert (n <= mult n n) ()

mc91 :: Int -> Int
mc91 x = if x > 100 then x - 10 else mc91 (mc91 (x + 11))

mainMC :: Int -> ()
mainMC n = if n <= 101 then assert (mc91 n == 91) () else ()