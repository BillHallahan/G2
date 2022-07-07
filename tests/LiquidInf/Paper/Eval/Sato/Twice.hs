{-@ LIQUID "--no-termination" @-}

module Twice (main) where

{-@ type TRUE = {v:Bool | v} @-}

{-@ die :: {v:String | false} -> a @-}
die str = error str

{-@ assert :: TRUE -> a -> a @-}
assert :: Bool -> a -> a
assert True x = x
assert _ _ = die "violated assert"

mult :: Int -> Int -> Int
mult n m =
    if m == 0 then 0
        else if m < 0 then
            - n + mult n (m + 1)
        else
            n + mult n (m - 1)

main :: Int -> Int -> ()
main n m =
    let twice f x = f (f x) in
    if n < 0 && m > 0 then assert (0 <= twice (mult n) m) () else ()