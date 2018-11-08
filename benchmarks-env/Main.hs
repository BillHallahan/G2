module Main where

import ListQuery

testFile = 
  -- "KMeans.lhs-2015-03-19T03.16.00.lhs"
  "KMeans.lhs-2015-03-19T04.50.47.lhs"

main = do
  
  table <- loadFileIdTable
  logs <- loadLogs

  putStrLn $ show $ length logs
  putStrLn $ show $ length $ filterKindLogs "List" logs
  putStrLn $ show $ length $ filterKindLogs "MapReduce" logs
  putStrLn $ show $ length $ filterKindLogs "KMeans" logs

  mapM (putStrLn) $ filterIdLogs "12" table logs
  putStrLn "------------------"
  putStrLn $ show $ afterLogs testFile table logs




