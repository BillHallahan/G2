{-# LANGUAGE QuasiQuotes #-}

module Main where

import G2.QuasiQuotes.QuasiQuotes

main :: IO ()
main = do
    r <- f 8 10
    print r

    r2 <- g 7
    print r2
    
    r3 <- h 11
    print r3

    print =<< boolTest 2
    print =<< boolTest 4

    -- print =<< maybeOrderingTest (Just LT)

f :: Int -> Int -> IO (Maybe Int)
f = [g2|(\y z -> \x ? x + 2 == y + z) :: Int -> Int -> Int -> Bool|]

g :: Int  -> IO (Maybe (Int, Int))
g = [g2|(\a -> \x y ? x < a && a < y && y - x > 10) :: Int -> Int -> Int -> Bool|]

h :: Int -> IO (Maybe [Int])
h = [g2|(\total -> \lst ? sum lst == total && length lst >= 2) :: Int -> [Int] -> Bool|]

boolTest :: Int -> IO (Maybe Bool)
boolTest = [g2|(\i -> \b ? (i == 4) == b) :: Int -> Bool -> Bool|]

-- maybeOrderingTest :: Maybe Ordering -> IO (Maybe (Maybe Ordering))
-- maybeOrderingTest = [g2|(\m1 -> \m2 ? fmap succ m1 == m2) :: Maybe Ordering -> Maybe Ordering -> Bool|]