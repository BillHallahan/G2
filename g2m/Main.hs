{-# LANGUAGE QuasiQuotes #-}

module Main where

import G2.QuasiQuotes.QuasiQuotes
import TestFunctions

import Data.Time.Clock
import Data.Maybe

main :: IO ()
main = do
    mergeEffectiveTests

mergeEffectiveTests :: IO ()
mergeEffectiveTests = do
    timeIOActionPrint "subseqOfTest" $ [g2| \(a :: [Int]) -> ?(b :: [Int]) | subseqOfTest a b |] [1,2,1,3]
    timeIOActionPrint "subseqOfTestSM" $ [g2M| \(a :: [Int]) -> ?(b :: [Int]) | subseqOfTest a b |] [1,2,1,3]

    -- timeIOActionPrint "sumEvensTest" $ [g2| \(x :: Int) -> ?(xs :: [Int]) | sumEvensTest xs x |] 5
    -- timeIOActionPrint "sumEvensTestSM" $ [g2M| \(x :: Int) -> ?(xs :: [Int]) | sumEvensTest xs x |] 5

    -- timeIOActionPrint "foldrTest" $ [g2| \(z :: Int) -> ?(xs :: [Maybe Int]) | foldrTest z xs |] 0
    -- timeIOActionPrint "foldrTestSM" $ [g2M| \(z :: Int) -> ?(xs :: [Maybe Int]) | foldrTest z xs |] 0

    -- timeIOActionPrint "foldrTest2" $ [g2| \(z :: Int) -> ?(xs :: [Maybe Int]) ?(ys :: [Maybe Int]) | foldrTest2 z xs ys |] 0
    -- timeIOActionPrint "foldrTest2SM" $ [g2M| \(z :: Int) -> ?(xs :: [Maybe Int]) ?(ys :: [Maybe Int]) | foldrTest2 z xs ys |] 0

    -- timeIOActionPrint "divideTest" $ [g2| \(a :: Int) -> ?(b :: Int) ?(c :: Int) ?(d :: Int) | divideTest c d a b |] 5
    -- timeIOActionPrint "divideTestSM" $ [g2M| \(a :: Int) -> ?(b :: Int) ?(c :: Int) ?(d :: Int) | divideTest c d a b |] 5

miscTests :: IO ()
miscTests = do
    timeIOActionPrint "g2" $ [g2| \(a :: Int) -> ?(xs :: [Int]) ?(ys :: [Int]) | compressTest2 a xs ys |] 1
    timeIOActionPrint "g2M" $ [g2M| \(a :: Int) -> ?(xs :: [Int]) ?(ys :: [Int]) | compressTest2 a xs ys |] 1

    -- timeIOActionPrint "g2" $ [g2| \(i :: Int) -> ?(t :: Tree) | treeSizeTest i t |] 3
    -- timeIOActionPrint "g2M" $ [g2M| \(i :: Int) -> ?(t :: Tree) | treeSizeTest i t |] 3

    -- timeIOActionPrint "g2" $ [g2| \(a :: Int) -> ?(b :: [Int]) | sieveTest a b |] 5 -- too slow
    -- timeIOActionPrint "g2M" $ [g2M| \(a :: Int) -> ?(b :: [Int]) | sieveTest a b|] 5


timeIOAction :: IO a -> IO (a, NominalDiffTime)
timeIOAction action = do
  start <- getCurrentTime
  res <- action
  end <- getCurrentTime
  let diff = diffUTCTime end start
  return (res, diff)

timeIOActionPrint :: Show a => String -> IO a -> IO ()
timeIOActionPrint nm action = do
  (res, time) <- timeIOAction action
  putStrLn nm
  putStrLn $ show res
  putStrLn $ "time: " ++ show time
