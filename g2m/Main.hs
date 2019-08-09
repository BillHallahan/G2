{-# LANGUAGE QuasiQuotes #-}

module Main where

import G2.QuasiQuotes.QuasiQuotes
import TestFunctions

import Data.Time.Clock

main :: IO ()
main = do
    -- timeIOActionPrint $ [g2| \(out :: [Int]) -> ?(i :: [Int]) | compressTest i out |] [2, 1, 2, 3]
    timeIOActionPrint $ [g2M| \(out :: [Int]) -> ?(i :: [Int]) | compressTest i out |] [2, 1, 2, 3]

    -- timeIOActionPrint $ [g2| \(out :: [Int]) -> ?(i :: [Int]) | compressTest2 i out |] [2, 1, 2, 3]
    timeIOActionPrint $ [g2M| \(out :: [Int]) -> ?(i :: [Int]) | compressTest2 i out |] [2, 1, 2, 3]

    -- timeIOActionPrint $ [g2| \(x :: Int) -> ?(xs :: [Int]) | sumEvensTest xs x |] 4
    -- timeIOActionPrint $ [g2M| \(x :: Int) -> ?(xs :: [Int]) | sumEvensTest xs x |] 4

timeIOAction :: IO a -> IO (a, NominalDiffTime)
timeIOAction action = do
  start <- getCurrentTime
  res <- action
  end <- getCurrentTime
  let diff = diffUTCTime end start
  return (res, diff)

timeIOActionPrint :: Show a => IO a -> IO ()
timeIOActionPrint action = do
  (res, time) <- timeIOAction action
  putStrLn $ show res
  putStrLn $ "time: " ++ show time
