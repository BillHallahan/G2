module EvalMain where

import Control.Exception

import Data.List

-- import Data.Map hiding (map)
import Data.Set as Set hiding (map, filter)
import Data.Map as Map hiding (map, filter)

import TableQuery
import LiquidQuery
import BenchmarksQuery


{-

  Load thebench mark file triples
    (file, errFun, absFun)

  getList of subsequent files
  does thing appear?

  For each of them, find the NEXT file(s) (until safe?)
  Check changes

  in each (afterLog, afterFile) pair:
    Does error function appear in the afterLog?
      Does refinement type of absfun change?

-}

errExists :: String -> String -> IO Bool
errExists log errFun = do
  raw <- readFile (wi15UnsafeDir ++ log)
  let exists = ("| " ++ errFun) `isInfixOf` raw
  evaluate exists

markTriple :: (String, String, String) -> IO ((String, String, String), Bool)
markTriple (log, errFun, absFun) = do
  exists <- errExists log errFun
  evaluate ((log, errFun, absFun), exists)

checkTriple ::
  Map String String
    -> [String]
    -> (String, String, String) -> IO (Maybe String)
checkTriple table logs (log, errFun, absFun)
  | Just file <- fileFromLog log
  , Just aftLogs <- afterLogs file table logs
  , Just flPairs <- mapM (\l -> fileFromLog l >>= return . (,) l) aftLogs = do
      
      return Nothing

  | otherwise = return Nothing

evalMain :: IO ()
evalMain = do
  -- Load things
  table <- loadFileIdTable
  logs <- loadLogs
  trips <- loadTriples

  -- Mark the triples
  markedTrips <- mapM markTriple trips

  let okayTrips = filter snd markedTrips
  let whatTrips = filter (not . snd) markedTrips

  checkeds <- mapM (checkTriple table logs . fst) okayTrips

  mapM_ (putStrLn . show) checkeds

  return ()
  

