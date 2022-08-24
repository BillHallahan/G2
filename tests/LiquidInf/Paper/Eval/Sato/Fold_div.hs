-- We substitute the use of random in the original benchmark with a symbolic [Int].
-- This is because the GHC standard library does not provide a random function

module Fold_div (main) where

{-@ die :: {v:String | false} -> a @-}
die str = error str

fold_left :: (b -> a -> b) -> b -> [a] -> b
fold_left f acc xs =
    case xs of
        [] -> acc
        x:xs' -> fold_left f (f acc x) xs'

randpos :: [Int] -> (Int, [Int])
randpos [] = (1, [])
randpos (x:xs) = if x > 0 then (x, xs) else randpos xs

make_list :: Int -> [Int] -> [Int]
make_list n xs = if n <= 0
                    then []
                    else let (x, xs') = randpos xs in
                            x:make_list (n - 1) xs'

divide :: Int -> Int -> Int
divide _ 0 = die "division by 0"
divide x y = 1 -- Ocaml version uses rand here

main :: [Int] -> Int -> Int -> Int
main rand n m =
    let xs = make_list n rand in
    fold_left divide m xs