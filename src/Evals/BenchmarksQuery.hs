module Evals.BenchmarksQuery
  ( loadBenches
  , loadTriples
  ) where

import Control.Exception
import Control.Monad

import Data.List
import Data.List.Split
import Data.Set as Set hiding (map, filter)

import System.Directory
import Text.Regex.Posix
import Text.Regex

reportsDir :: String
reportsDir = "/home/pldi-g2/G2/benchmarks-env/benchmark-reports/"

benchFile :: String
benchFile = "/home/pldi-g2/G2/benchmarks-env/bench-pairs.txt"

-- Regex magic

whenPat1 :: String
whenPat1 = "The call\n.*\n.*\nwhen\n.*"
-- whenPat1 = "*\n.*\nwhen\n.*"

extractWhen1Group :: String -> (String, String)
extractWhen1Group group =
  let splitted = splitOn "\n" group in
  let errFun = head $ splitOn " " $ splitted !! 1 in
  let absFun = head $ splitOn " " $ last splitted in
    (errFun, absFun)

whenPat2 :: String
-- whenPat2 = "0m.*\nmakes.*\n.*\n.*\n.*\n.*"
whenPat2 = "0m.*\nmakes.*\n(.*\n)*when\n.*"
-- whenPat2 = "0m.*\nmakes.*\n.*"

extractWhen2Group :: String -> (String, String)
extractWhen2Group group =
  let splitted = splitOn "\n" group in
  let errFun = tail $ tail $ head $ splitOn " " $ head splitted in
  let absFun = head $ splitOn " " $ last $ splitted in
    (errFun, absFun)

parseWhenPairs :: String -> [(String, String)]
parseWhenPairs raw =
  let groups1 = raw =~ whenPat1 :: [[String]] in
  let groups2 = raw =~ whenPat2 :: [[String]] in
  let extracts1 = map extractWhen1Group $ concat groups1 in
  let extracts2 = map extractWhen2Group $ concat groups2 in
    -- nub $ filter (\(_, w) -> length w /= 0) $ extracts1 ++ extracts2
    take 1 $ filter (\(_, w) -> length w /= 0) $ extracts1 ++ extracts2

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

blackSet :: Set String
blackSet = Set.fromList []

-- .lhs file, erroring fun, abstracted fun
loadTriples :: IO [(String, String, String)]
loadTriples = do
  benches <- loadBenches
  -- let rawTrips = concatMap (\(b, ws) -> map (\(e, a) -> (b, e, a)) ws) benches
  -- let cleanTrips = filter (\(_, e, _) -> not $ member e blackSet) rawTrips
  let trips = map (\(f, ps) -> let (e, a) = head ps in (f, e, a)) benches
  return trips


