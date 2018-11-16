module Main where

import Data.Maybe

import BenchmarksQuery
import TableQuery
import LiquidQuery
import EvalMain

testDir = "/home/celery/foo/yale/G2/benchmarks-env/liquidhaskell-study/wi15/"
testFile = testDir ++ "unsafe/List.lhs-2015-03-21T02.26.22.lhs"
testListLibSrc = testDir ++ "List.lhs"


testBefore = "/home/celery/foo/yale/G2/benchmarks-env/liquidhaskell-study/wi15/unsafe/flycheck_List.lhs-2015-03-16T00.34.21.lhs"

testAfter = "/home/celery/foo/yale/G2/benchmarks-env/liquidhaskell-study/wi15/unsafe/flycheck_List.lhs-2015-03-16T00.45.34.lhs"


main = do
  
  table <- loadFileIdTable
  logs <- loadLogs


  {-
  mbSpecs1 <- getVarFileSpecTypes "length" testBefore testDir [testListLibSrc]
  mbSpecs2 <- getVarFileSpecTypes "length" testAfter testDir [testListLibSrc]

  putStrLn $ show mbSpecs1

  putStrLn "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%"

  putStrLn $ show mbSpecs2

  putStrLn "The same????"

  putStrLn $ show $ specTypesStructEq (fromJust mbSpecs1) (fromJust mbSpecs2)
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
  allBenches <- allBenches
  absBenches <- abstractBenches
  putStrLn $ show (length allBenches, length absBenches)

  mapM_ (putStrLn . show) absBenches
  -}

  evalMain


  putStrLn "compiles!"




