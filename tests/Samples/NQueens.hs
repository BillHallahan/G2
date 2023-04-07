module NQueens where

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
