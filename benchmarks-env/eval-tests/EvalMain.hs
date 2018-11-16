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


nothingFile :: String
nothingFile = "dump-nothing.txt"

goodFile :: String
goodFile = "dump-good.txt"

manualFile :: String
manualFile = "dump-manual.txt"

appendFileLn :: String -> String -> IO ()
appendFileLn file text = appendFile file (text ++ "\n")


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
  (String, String, String) -> [(String, String)] -> IO (Maybe (String, Bool))
linearLogsFind _ [] = return Nothing
linearLogsFind
    (trip @ (file, errFun, absFun)) ((aLog, aFile) : afters) = do
  absErrEx <- absErrExists aLog errFun
  synErrEx <- syntaxErrExists aLog
  if synErrEx || absErrEx
    then linearLogsFind trip afters
    else do
      let origPair = (absFun, wi15UnsafeDir ++ file)
      aFullFile <- recoverSafeUnsafePath aFile
      let afModPair = (absFun, aFullFile)
      diffRes <- structEqFiles origPair afModPair
      case diffRes of
        Left err -> linearLogsFind trip afters
        Right SpecTypesDiffer -> return $ Just (aFullFile, True)
        Right SpecTypesSame -> return $ Just (aFullFile, False)


-- Careful: some of these are absolute paths and some are not.
checkTriple ::
  Map String String
    -> [String]
    -> (String, String, String) -> IO ()
checkTriple table logs (log, errFun, absFun)
  | Just file <- fileFromLog log
  , Just aftLogs <- afterLogs file table logs
  , Just flPairs <- mapM (\l -> fileFromLog l >>= return . (,) l) aftLogs = do

      checkRes <- linearLogsFind (file, errFun, absFun) flPairs
      _ <- case checkRes of
        Nothing -> do
          appendFileLn nothingFile $ wi15UnsafeDir ++ file
          appendFileLn nothingFile $ show (errFun, absFun)
          appendFileLn nothingFile "^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^"
          return ()
        Just (aFile, True) -> do
          appendFileLn goodFile $ wi15UnsafeDir ++ file
          appendFileLn goodFile $ aFile
          appendFileLn goodFile $ show (errFun, absFun)
          appendFileLn goodFile "^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^"
          return ()
        Just (aFile, False) -> do
          appendFileLn manualFile $ wi15UnsafeDir ++ file
          appendFileLn manualFile $ aFile
          appendFileLn manualFile $ show (errFun, absFun)
          appendFileLn manual "^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^"
          return ()

      return ()

  | otherwise = return ()

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

  checkeds <- mapM (checkTriple table logs . fst) $ take 50 okayTrips

  -- mapM_ (putStrLn . show) checkeds

  return ()
  

