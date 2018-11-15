module Main where

import Data.Maybe

import BenchmarksQuery
import TableQuery
import LiquidQuery
import EvalMain

testDir = "/home/celery/foo/yale/G2/benchmarks-env/liquidhaskell-study/wi15/"
testFile = testDir ++ "unsafe/List.lhs-2015-03-21T02.26.22.lhs"
testListLibSrc = testDir ++ "List.lhs"

main = do
  
  table <- loadFileIdTable
  logs <- loadLogs

  {-
  putStrLn $ show $ length logs
  putStrLn $ show $ length $ filterKindLogs "List" logs
  putStrLn $ show $ length $ filterKindLogs "MapReduce" logs
  putStrLn $ show $ length $ filterKindLogs "KMeans" logs

  mapM (putStrLn) $ filterIdLogs "12" table logs
  putStrLn "------------------"
  putStrLn $ show $ afterLogs testFile table logs
  -}

  {-
  mbSpecs1 <- getVarFileSpecTypes "concat" testFile testDir [testListLibSrc]
  mbSpecs2 <- getVarFileSpecTypes "concat" testFile testDir [testListLibSrc]

  putStrLn $ show mbSpecs1
  putStrLn $ show $ specTypesStructDiffer (fromJust mbSpecs1) (fromJust mbSpecs2)

  res <- structDiffFiles ("concat", testFile) ("concat", testFile)
  putStrLn $ show res

  -}

  {-
  allBenches <- allBenchFiles
  absBenches <- abstractBenchFilePairs
  putStrLn $ show (length allBenches, length absBenches)

  mapM_ (putStrLn . show) absBenches
  -}

  pairs <- loadBenchPairs
  mapM (putStrLn . show) pairs

  putStrLn "compiles!"




