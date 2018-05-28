module HigerOrderRef where

{-@ f :: (x1:Int -> {y1:Int | x1 < y1 }) -> x2:Int -> {y2:Int | x2 < y2 } @-}
f :: (Int -> Int) -> Int -> Int
f g x = g x

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

callf :: (Int -> Int) -> Int -> Int
callf = f