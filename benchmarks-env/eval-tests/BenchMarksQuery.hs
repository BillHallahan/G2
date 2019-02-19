module BenchMarksQuery where

import Data.List
import Data.List.Split

import TableQuery
import LiquidQuery

logFromBench :: String -> String
logFromBench bench = intercalate "_" $ tail $ splitOn "_" bench

parseLog :: String -> Maybe (String, String)
parseLog raw = undefined

