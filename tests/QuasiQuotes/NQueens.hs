{-# LANGUAGE QuasiQuotes #-}

module NQueens where

import Data.List
import SymH.SymH

type Queen = (Int, Int)

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
    && all (\p -> (1, 1) <= p && p <= (n, n)) queens


queensTestN :: Int -> IO (Maybe [Queen])
queensTestN n = [g2| \(n :: Int) -> ?(queens :: [Queen]) |
                  legalQueens n queens
                    && allSafe queens |] n



