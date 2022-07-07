{-@ LIQUID "--no-termination" @-}

module Sum_add (main) where

import Prelude hiding (sum)

{-@ type TRUE = {v:Bool | v} @-}

{-@ die :: {v:String | false} -> a @-}
die str = error str

{-@ assert :: TRUE -> a -> a @-}
assert :: Bool -> a -> a
assert True x = x
assert _ _ = die "violated assert"

add :: Int -> Int -> Int
add x y = if y <= 0 then x else 1 + add x (y - 1)

sum :: Int -> Int
sum x = if x <= 0 then 0 else add x (sum (x - 1))

main :: Int -> ()
main n = assert (0 <= sum n) ()