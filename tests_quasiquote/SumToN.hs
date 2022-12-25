{-# LANGUAGE QuasiQuotes #-}

module SumToN where

import G2.QuasiQuotes.QuasiQuotes

sumToN :: Int -> [Int] -> IO (Maybe [Int])
sumToN = [g2| \(n :: Int) (xs :: [Int]) -> ?(ys :: [Int])
            |  sum ys == n
            && all (\e -> e `elem` xs) ys
            && length ys >= 1 |]

main :: IO ()
main = do
  print =<< sumToN 0 [-5 , 10, -15 , 20, 25]
