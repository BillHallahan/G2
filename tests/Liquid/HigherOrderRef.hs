module HigherOrderRef where

{-@ f1 :: (x1:Int -> {y1:Int | x1 < y1 }) -> x2:Int -> {y2:Int | x2 < y2 } @-}
f1 :: (Int -> Int) -> Int -> Int
f1 g x = g x

{-@ f2 :: (x1:Int -> {y1:Int | x1 <= y1 }) -> x2:Int -> {y2:Int | x2 < y2 } @-}
f2 :: (Int -> Int) -> Int -> Int
f2 g x = g x

{-@ f3 :: ({x1:Int | x1 > 0} -> {y1:Int | x1 < y1 }) -> {x2:Int | x2 > 0} -> Int @-}
f3 :: (Int -> Int) -> Int -> Int
f3 g x = g x

{-@ f4 :: ({x1:Int | x1 > 0} -> {y1:Int | x1 < y1 }) -> {x2:Int | x2 >= 0} -> Int @-}
f4 :: (Int -> Int) -> Int -> Int
f4 g x = g x

{-@ f5 :: [Int -> {x:Int | x > 0}] -> Int -> [{y:Int | y > 0}] @-}
f5 :: [Int -> Int] -> Int -> [Int]
f5 [] _ = []
f5 (f:fs) x = f x:f5 fs x

{-@ f6 :: [Int -> {x:Int | x > 0}] -> Int -> [{y:Int | y >= 0}] @-}
f6 :: [Int -> Int] -> Int -> [Int]
f6 [] _ = []
f6 (f:fs) x = f x:f6 fs x

{-@ f7 :: x:Int -> (Int -> {y:Int | x <= y}) -> {z:Int | z < x } @-}
f7 :: Int -> (Int -> Int) -> Int
f7 x f = f x

{-@ ((Int -> {x:Int | x > 0}) -> Int) -> (Int -> {y:Int | y >= 0}) -> Int @-}
f8 :: ((Int -> Int) -> Int) -> (Int -> Int) -> Int
f8 f g = f g 0

callf :: (Int -> Int) -> Int -> Int
callf = f