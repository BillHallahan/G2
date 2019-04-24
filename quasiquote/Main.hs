{-# LANGUAGE QuasiQuotes #-}

module Main where

import G2.Language.Syntax
import G2.QuasiQuotes.QuasiQuotes

main :: IO ()
main = do
    r <- f 8 10
    print r

    r2 <- g 7
    print r2

f :: Int -> Int -> IO (Maybe Int)
f = [g2|(\y z -> \x ? x + 2 == y + z) :: Int -> Int -> Int -> Bool|]

g :: Int  -> IO (Maybe (Int, Int))
g = [g2|(\a -> \x y ? x < a && a < y && y - x > 10) :: Int -> Int -> Int -> Bool|]

-- nub_call :: Expr
-- nub_call = [g2| nub [1, 2, 3] |]