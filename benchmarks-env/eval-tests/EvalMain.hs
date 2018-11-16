module EvalMain where

import Control.Exception

import Data.List

-- import Data.Map hiding (map)
import Data.Set as Set hiding (map, filter)
import Data.Map as Map hiding (map, filter)

import System.Directory

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
      No? Does refinement type of absfun change?

-}

recoverSafeUnsafePath :: String -> IO String
recoverSafeUnsafePath file = do
  let unsafePath = wi15UnsafeDir ++ file
  let safePath = wi15SafeDir ++ file
  unsafeExists <- doesFileExist unsafePath
  if unsafeExists
    then return unsafePath
    else return safePath

absErrExists :: String -> String -> IO Bool
absErrExists log errFun = do
  path <- recoverSafeUnsafePath log
  raw <- readFile path
  let exists = ("| " ++ errFun) `isInfixOf` raw
  evaluate exists

syntaxErrExists :: String -> IO Bool
syntaxErrExists log = do
  path <- recoverSafeUnsafePath log
  raw <- readFile path
  let exists = ("Illegal") `isInfixOf` raw
  evaluate exists

data TripleMark =
    OkayMark
  | NoBarMark
  | SyntaxMark
  deriving (Show, Eq)

markTriple ::
  (String, String, String) -> IO ((String, String, String), TripleMark)
markTriple (trip @ (log, errFun, absFun)) = do
  absErrEx <- absErrExists log errFun
  synErrEx <- syntaxErrExists log
  if synErrEx
    then evaluate (trip, SyntaxMark)
    else if absErrEx
      then evaluate (trip, OkayMark)
      else evaluate (trip, NoBarMark)


linearLogsFind ::
  (String, String, String) -> [(String, String)] -> IO (Maybe String)
linearLogsFind _ [] = return Nothing
linearLogsFind
    (trip @ (file, errFun, absFun)) ((aLog, aFile) : afters) = do
  absErrEx <- absErrExists aLog errFun
  synErrEx <- syntaxErrExists aLog
  if synErrEx || absErrEx
    then linearLogsFind trip afters
    else do
      let origPair = (absFun, wi15UnsafeDir ++ file)
      afterFilePath <- recoverSafeUnsafePath aFile
      let afModPair = (absFun, afterFilePath)
      diffRes <- structEqFiles origPair afModPair
      case diffRes of
        Left err -> linearLogsFind trip afters
        Right SpecTypesDiffer -> return $ Just aLog
        Right otherwise -> do
          putStrLn $ "linearLogsCompare: Looks promising on " ++ show aLog
          return $ Just aLog
        -- otherwise -> linearLogsFind trip afters



{-
checkTripleOnLogs ::
  (String, String, String) -> [(String, String)] -> Int -> Int
    -> IO (Maybe String)
checkTripleOnLogs (trip @ (file, errFun, absFun)) logs lo hi
  | lo > hi = return Nothing
  | otherwise = do
      let mid = (lo + hi) / 2
      let (aLog, aFile) = logs !! mid
      absErrEx <- absErrExists aLog errFun
      synErrEx <- syntaxErrExists aLog
      if synErrEx || absErrEx
        -- Go later
        then checkTripleOnLogs trip logs mid hi
        else do
          let origPair = (absFun, wi15UnsafeDir ++ file)
          afterFilePath <- recoverSafeUnsafePath aFile
          let afModPair = (absFun, afterFilePath)
          diffRes <- structEqFiles origPair afModPair
          case diffRes of
            Left err -> checkTripleOnLogs trip afters
            Right SpecTypesDiffer -> return $ Just (aLog, aFile)
            otherwise -> checkTripleOnLogs trip afters
  
-}



{-
-}



-- Careful: some of these are absolute paths and some are not.
checkTriple ::
  Map String String
    -> [String]
    -> (String, String, String) -> IO (Maybe String)
checkTriple table logs (log, errFun, absFun)
  | Just file <- fileFromLog log
  , Just aftLogs <- afterLogs file table logs
  , Just flPairs <- mapM (\l -> fileFromLog l >>= return . (,) l) aftLogs = do
      putStrLn $ "checkTriple: " 
                  ++ "[" ++ (show $ length flPairs) ++ "] "
                  ++ show (log, errFun, absFun)

      checkRes <- linearLogsFind (file, errFun, absFun) flPairs

      putStrLn $ "checkTriple: result: " ++ show checkRes
      putStrLn "^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^"
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

  let okayTrips = filter (\(_, m) -> m == OkayMark) markedTrips
  let whatTrips = filter (\(_, m) -> m == NoBarMark) markedTrips
  let synTrips = filter (\(_, m) -> m == SyntaxMark) markedTrips

  checkeds <- mapM (checkTriple table logs . fst) $ take 100 okayTrips

  -- mapM_ (putStrLn . show) checkeds

  return ()
  

