module Evals.EvalMain where

import Control.Exception

import Data.List hiding (lookup)

import Prelude hiding (lookup)

-- import Data.Map hiding (map)
import Data.Set as Set hiding (map, filter)
import Data.Map as Map hiding (map, filter)

import System.Directory

import Evals.TableQuery
import Evals.LiquidQuery
import Evals.BenchmarksQuery


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

whatFile :: String
whatFile = "dump-what.txt"

syntaxFile :: String
syntaxFile = "dump-syntax.txt"

etcFile :: String
etcFile = "dump-etc.txt"

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
  let exists = (("| " ++ errFun) `isInfixOf` raw)
                || (errFun == "mapReduce" &&
                      ("  kvm " `isInfixOf` raw
                      || "  kvs " `isInfixOf` raw
                      || "  kvsm " `isInfixOf` raw
                      || " then collapse " `isInfixOf` raw))
                || (errFun == "kmeans1" &&
                      ("  normalize " `isInfixOf` raw
                      || "  newClusters " `isInfixOf` raw
                      || "  fm " `isInfixOf` raw
                      || "  fr " `isInfixOf` raw))
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

-- Finds the first file that does not cause LiquidHaskell to error
linearLogsFind ::
  (String, String, String) -> [(String, String)] -> IO (Maybe (String, Bool))
linearLogsFind _ [] = return Nothing
linearLogsFind
    (trip @ (file, errFun, absFun)) ((aLog, aFile) : afters) = do
  absErrEx <- absErrExists aLog errFun
  synErrEx <- syntaxErrExists aLog
  if synErrEx || absErrEx
    -- Have error? Keep going
    then linearLogsFind trip afters
    -- This file does not have errors, so we are interested in checking 
    -- if the refinement types are different.
    else do
      let origPair = (absFun, wi15UnsafeDir ++ file)
      aFullFile <- recoverSafeUnsafePath aFile
      let afModPair = (absFun, aFullFile)
      -- DO the refinement types differ?
      diffRes <- structEqFiles origPair afModPair
      case diffRes of
        -- OOPS!
        Left err -> linearLogsFind trip afters
        -- Yes! They do differ! This means G2 correctly localized
        Right SpecTypesDiffer -> return $ Just (aFullFile, True)
        -- No, they are not different, so G2 did not correctly localize
        Right SpecTypesSame -> return $ Just (aFullFile, False)


-- Careful: some of these are absolute paths land some are not.
checkTriple ::
  Map String String
    -> [String]
    -> (String, String, String) -> IO ()
checkTriple table logs (log, errFun, absFun)
  | Just file <- fileFromLog log
  , Just sid <- lookup file table
  , Just aftLogs <- afterLogs file table logs
  , Just flPairs <- mapM (\l -> fileFromLog l >>= return . (,) l) aftLogs = do

      checkRes <- linearLogsFind (file, errFun, absFun) flPairs
      _ <- case checkRes of
        -- Failed to find any(!) helpful LH logs
        Nothing -> do
          appendFileLn nothingFile $ "ID: " ++ sid
          appendFileLn nothingFile $ wi15UnsafeDir ++ file
          appendFileLn nothingFile $ show (errFun, absFun)
          appendFileLn nothingFile "^^^^^"
          appendFileLn nothingFile ""
          return ()
        -- Successfully found something that G2 localized
        Just (aFile, True) -> do
          appendFileLn goodFile $ "ID: " ++ sid
          appendFileLn goodFile $ wi15UnsafeDir ++ file
          appendFileLn goodFile $ aFile
          appendFileLn goodFile $ show (errFun, absFun)
          appendFileLn goodFile "^^^^^"
          appendFileLn goodFile ""
          return ()
        -- The first correct file did not have a changed refinement type for
        -- the function that G2 ended up abstracting.
        Just (aFile, False) -> do
          case (errFun, absFun) of
            -- Special case this because 
            ("kmeans1", "map") -> do
              appendFileLn etcFile $ "ID: " ++ sid
              appendFileLn etcFile $ wi15UnsafeDir ++ file
              appendFileLn etcFile $ aFile
              appendFileLn etcFile $ show (errFun, absFun)
              appendFileLn etcFile "^^^^^"
              appendFileLn etcFile ""
              return ()
            _ -> do
              appendFileLn manualFile $ "ID: " ++ sid
              appendFileLn manualFile $ wi15UnsafeDir ++ file
              appendFileLn manualFile $ aFile
              appendFileLn manualFile $ show (errFun, absFun)
              appendFileLn manualFile "^^^^^"
              appendFileLn manualFile ""
              return ()

      return ()

  | otherwise = return ()

-- Execution starts here
evalMain :: IO ()
evalMain = do
  -- Table matches files to the students' id numbers
  table <- loadFileIdTable

  -- Raw information of all the log files via getDirectoryCOntents
  logs <- loadLogs

  -- [(.LHS files, erroring function, abstracted function)]
  -- We are interested in seeing if the abstract functions correctly localize errors
  -- Want to see if the user ended up changing the refinement type of the abstracted
  trips <- loadTriples

  -- Filter the triples 
  let nubbedTrips = nubBy (\(a, b, c) (d, e, f) -> (a, b) == (d, e)) trips

  -- Mark the triples into different categories
  -- OkayMark = the erroring function has an actual error we want to pursue
  -- NoBarMark = no syntax error and no other errors?
  -- SyntaxMark = erroring function has syntax error
  markedTrips <- mapM markTriple nubbedTrips
  let okayTrips = map fst $ filter (\(_, m) -> m == OkayMark) markedTrips
  let whatTrips = map fst $ filter (\(_, m) -> m == NoBarMark) markedTrips
  let synTrips = map fst $ filter (\(_, m) -> m == SyntaxMark) markedTrips
  
  putStrLn $ "okays: " ++ (show $ length okayTrips)
  putStrLn $ "what: " ++ (show $ length whatTrips)
  putStrLn $ "syns: " ++ (show $ length synTrips)
  putStrLn $ "nubbed: " ++ (show $ length nubbedTrips)

  -- checkeds <- mapM (checkTriple table logs) $ take 100 okayTrips
  checkeds <- mapM (checkTriple table logs) okayTrips

  -- mapM_ (putStrLn . show) checkeds

  -- Dump the what things
  -- The things that were NoBarMark, need to look at these manually since they weird
  mapM_ (appendFileLn whatFile . show) whatTrips

  -- Files with syntax errors
  mapM_ (appendFileLn syntaxFile . show) synTrips

  -- Just everything
  mapM_ (appendFileLn "dump-raw.txt" . show) checkeds

  -- Dump the syntax errors

  return ()

