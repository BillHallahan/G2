module BenchMarksQuery where

import Control.Exception
import Control.Monad

import Data.List
import Data.List.Split

import System.Directory

import Text.Regex.Posix


import TableQuery
import LiquidQuery

import Text.Regex

reportsDir :: String
reportsDir = "/home/celery/foo/yale/G2/benchmarks-env/benchmark-reports/"

benchFile :: String
benchFile = "/home/celery/foo/yale/G2/benchmarks-env/bench-pairs.txt"

-- Regex magic

whenPat :: String
whenPat = "when\n[a-zA-Z0-9]*"

extractWhenGroup :: String -> String
extractWhenGroup group = (splitOn "\n" group) !! 1

parseTextWhens :: String -> [String]
parseTextWhens raw =
  let groups = raw =~ whenPat :: [[String]] in
    nub $ map extractWhenGroup $ concat groups


-- All the bench files
allBenchFiles :: IO [String]
allBenchFiles = do
  benches <- getDirectoryContents reportsDir
  let noDots = filter (\b -> b /= "." && b /= "..") benches
  let absBenches = map (\b -> reportsDir ++ b) noDots
  return absBenches

whenFromBenchFile :: String -> IO [String]
whenFromBenchFile bench = do
  raw <- readFile bench
  let whens = parseTextWhens raw
  evaluate whens

logFromBench :: String -> String
logFromBench bench =
  intercalate "_" $ tail $ splitOn "_" bench


-- Only those with "Abstract" in them; NOT absolute paths
abstractBenchFilePairs :: IO [(String, [String])]
abstractBenchFilePairs = do
  benches <- allBenchFiles
  whenPairs <- mapM (\b -> whenFromBenchFile b >>= \w -> return (b, w)) benches
  let absPairs = filter (\(_, ws) -> length ws > 0) whenPairs
  let cleanPairs = map (\(b, ws) -> (logFromBench b, ws)) absPairs
  return cleanPairs

loadBenchPairs :: IO ([(String, [String])])
loadBenchPairs = do
  raw <- readFile benchFile
  let pairs = read raw :: [(String, [String])]
  return pairs


