module BenchmarksQuery where

import Control.Exception
import Control.Monad

import Data.List
import Data.List.Split

import System.Directory

import Text.Regex.Posix

import Text.Regex

reportsDir :: String
reportsDir = "/home/celery/foo/yale/G2/benchmarks-env/benchmark-reports/"

benchFile :: String
benchFile = "/home/celery/foo/yale/G2/benchmarks-env/bench-pairs.txt"

-- Regex magic

whenPat :: String
whenPat = ".*\nwhen\n.* "
-- whenPat = "when\n[a-zA-Z0-9]*"

extractWhenGroup :: String -> (String, String)
extractWhenGroup group =
  let splitted = splitOn "\nwhen\n" group in
  let left = splitted !! 0 in
  let right = splitted !! 1 in
  let errFun = (splitOn " " $ (splitOn "'" left) !! 0) !! 1 in
  let absFun = head $ splitOn " " (splitted !! 1) in
    (errFun, absFun)
  
parseWhenPairs :: String -> [(String, String)]
parseWhenPairs raw =
  let groups = raw =~ whenPat :: [[String]] in
    nub $ map extractWhenGroup $ concat groups


-- All the bench files
allBenches :: IO [String]
allBenches = do
  benches <- getDirectoryContents reportsDir
  let noDots = filter (\b -> b /= "." && b /= "..") benches
  let absBenches = map (\b -> reportsDir ++ b) noDots
  return absBenches

whenPairsFromBench :: String -> IO [(String, String)]
whenPairsFromBench bench = do
  raw <- readFile bench
  let pairs = parseWhenPairs raw
  evaluate pairs

logFromBench :: String -> String
logFromBench bench = intercalate "_" $ tail $ splitOn "_" bench

-- Only those with "Abstract" in them; NOT absolute paths
abstractBenches :: IO [(String, [(String, String)])]
abstractBenches = do
  benches <- allBenches
  whenPairs <- mapM (\b -> whenPairsFromBench b >>= return . (,) b) benches
  let absPairs = filter (\(_, ws) -> length ws > 0) whenPairs
  let cleanPairs = map (\(b, ws) -> (logFromBench b, ws)) absPairs
  return cleanPairs

-- CALL THIS
-- Load the log / pairing for where things messed up
loadBenches :: IO ([(String, [(String, String)])])
loadBenches = do
  raw <- readFile benchFile
  let pairs = read raw :: [(String, [(String, String)])]
  return pairs


