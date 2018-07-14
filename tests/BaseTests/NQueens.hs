module NQueens where

import Data.List

type Pos = (Int, Int)

find6Easy :: [(Int, Int, Int, Int, Int, Int)]
find6Easy = [ ( p1, p2, p3, p4
              , p5, p6) | p1 <- [0..6]
                        , p2 <- [0..6]
                        , p3 <- [0..6]
                        , p4 <- [0..6]
                        , p5 <- [0..6]
                        , p6 <- [0..6]
                        , check 6 [ (0, p1), (1, p2), (2, p3), (3, p4)
                                  , (4, p5), (5, p6)] ]

find4 :: [(Pos, Pos, Pos, Pos)]
find4 = [ (p1, p2, p3, p4) | p1 <- tupleList 4
                           , p2 <- tupleList 4
                           , p3 <- tupleList 4
                           , p4 <- tupleList 4
                           , check4 p1 p2 p3 p4 ]

find4Easy :: [(Int, Int, Int, Int)]
find4Easy = [ (p1, p2, p3, p4) | p1 <- [0..4]
                               , p2 <- [0..4]
                               , p3 <- [0..4]
                               , p4 <- [0..4]
                               , check4Easy p1 p2 p3 p4 ]
tupleList :: Int -> [Pos]
tupleList n = [(x, y) | x <- [0..n]
                      , y <- [0..n] ]

check4VeryEasy :: Bool
check4VeryEasy = check 4 [(0, 1), (1, 3), (2, 0), (3, 2)]


check4Easy :: Int -> Int -> Int -> Int -> Bool
check4Easy p1 p2 p3 p4 = check 4 [(0, p1), (1, p2), (2, p3), (3, p4)]

check4 :: Pos -> Pos -> Pos -> Pos -> Bool
check4 p1 p2 p3 p4 = check 4 [p1, p2, p3, p4]

check :: Int -> [Pos] -> Bool
check n xs =
    n == length xs && all (validPos n) xs && isSorted xs && uniqRow xs && uniqCol xs && uniqDiag xs

validPos :: Int -> Pos -> Bool
validPos n (x, y) = 0 <= x && x < n && 0 <= y && y < n

uniqRow :: [Pos] -> Bool
uniqRow = uniq fst

uniqCol :: [Pos] -> Bool
uniqCol = uniq snd

uniq :: (Pos -> Int) -> [Pos] -> Bool
uniq f xs =
  let
      rs = map f xs
  in
  length xs == length (nub rs)

uniqDiag :: [Pos] -> Bool
uniqDiag xs =
    not $ or [ abs(x1 - x2) == abs(y1 - y2) && p1 /= p2 | p1@(x1, y1) <- xs, p2@(x2, y2) <- xs ]

isSorted :: (Eq a, Ord a) => [a] -> Bool
isSorted xs = xs == sort xs