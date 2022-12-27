module NQueens.Encoding where

import Data.List

type Queen = Int

indexPairs :: Int -> [(Int,Int)]
indexPairs n = [(i, j) | i <- [0..n-1], j <- [i+1..n-1]]

legal :: Int -> Queen -> Bool
legal n qs = 1 <= qs && qs <= n

queenPairSafe :: Int -> [Queen] -> (Int, Int) -> Bool
queenPairSafe n qs (i, j) =
  let qs_i = qs !! i
      qs_j = qs !! j
  in (qs_i /= qs_j)
      -- && (abs (qs_j - qs_i) /= (j - i))
      && qs_j - qs_i /= j - i
      && qs_j - qs_i /= i - j

allQueensSafe :: Int -> [Queen] -> Bool
allQueensSafe n qs =
  (n == length qs)
  && all (legal n) qs
  && (all (queenPairSafe n qs) (indexPairs n))

solveListCompN :: Int -> [Int]
solveListCompN n =
  head . filter (allQueensSafe n) $ [x | x <- mapM (const [1..n]) [1..n]]

{-
-- Gets all pairs of unique positions
pairs :: Ord a => [a] -> [(a, a)]
pairs xs = [(a, b) | a <- xs, b <- xs, a < b]

-- Checks if all elements of list are unique
allUnique :: Ord a => [a] -> Bool
allUnique xs = length xs == length (nub xs)

-- Check if two positions are safe
pairSafe :: (Queen, Queen) -> Bool
pairSafe ((x1, y1), (x2, y2)) =
  -- No same x and y value
  (x1 /= x2) && (y1 /= y2)
  -- Not on the same diagonal
  && (abs (x1 - x2) /= abs (y1 - y2))

-- Check that all queens in a list are safe
allSafe :: [Queen] -> Bool
allSafe queens = all pairSafe $ pairs queens

-- Valid Queens on an n x n board
legalQueens :: Int -> [Queen] -> Bool
legalQueens n queens =
  (length queens == n)
  && (n == length (nub queens))
  && all (\(x, y) -> 1 <= x && x <= n && 1 <= y && y <= n) queens
    -- && all (\p -> (1, 1) <= p && p <= (n, n)) queens

-}

