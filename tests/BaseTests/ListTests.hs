module ListTests where

-- import qualified Data.Map as M
import Data.List

test :: Int -> Int
test x = x

maxMap :: Int -> Int
maxMap a = maximum (map (+1) [1, 2, a, 4, 5])

minTest :: Int -> Int
minTest a = minimum [1, 2, 3, a]


foldrTest :: Int -> Int
foldrTest a = foldr (+) 0 [1, a, 3]

foldrTest2 :: Int -> Int
foldrTest2 a = foldr (+) 4 [1, a, 3, 4, 5]

hd :: [Int] -> Int
hd xs = head xs

hdTail :: [Int] -> Int
hdTail xs = head $ tail xs

-- g2Entry6 :: Int -> Int
-- g2Entry6 a = let m = M.fromList [(1, 'a'), (2, 'b')]
--                  m' = M.insert a 'c' m
--              in case M.lookup 1 m' of
--                Just _ -> 13579
--                _ -> 24680

fromListIntFloat :: [(Int, Float)] -> [(Int, Float)]
fromListIntFloat = foldr (:) []

fromListInt :: [Int] -> [Int]
fromListInt = foldr (:) []

foldrx :: (a -> b -> b) -> b -> [a] -> b
foldrx k z = go
          where
            go []     = z
            go (y:ys) = y `k` go ys

map2 :: [(a, b)] -> [b]
map2 = map snd

-- g2Entry7 :: Int -> [(Int, Int)]
-- g2Entry7 a = let m = M.fromList [(123456, a)]
--              in M.toList m

-- g2Entry8 :: [(Int, Float)] -> M.Map Int Float
-- g2Entry8 = M.fromList

lengthN :: [Int] -> Int
lengthN xs = length xs
