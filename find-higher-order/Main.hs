{-# LANGUAGE MultiWayIf, OverloadedStrings, ScopedTypeVariables, TupleSections #-}

module Main (main) where

import qualified Data.Text as T

import G2.Config
import G2.Interface
import qualified G2.Initialization.Types as IT
import G2.Language
import qualified G2.Language.ExprEnv as E
import G2.Language.HPC
import qualified G2.Language.TyVarEnv as TV
import G2.Translation

import Control.Exception
import Control.Monad
import qualified Data.HashSet as HS
import Data.List
import qualified Data.Text as T
import System.Directory
import System.Environment
import System.FilePath

main :: IO ()
main = do
  as <- getArgs
  case as of
      [path] -> runAllInFolder path
      [path, fl] -> runFile (path </> fl)

runAllInFolder :: FilePath -> IO ()
runAllInFolder src = do
  allFiles <- listDirectory src
  let potential_folders = map (src </>) allFiles
  folders <- filterM doesDirectoryExist potential_folders 

  all_res <- mapM (\path -> catch (do
                      m_fl <- getFile path
                      case m_fl of
                          Just fl -> do
                              res <- outputProj fl
                              return (T.pack fl, Just res)
                          Nothing ->
                              return (T.pack path, Nothing))
                          (\(_ :: SomeException) -> return (T.pack path, Nothing))) folders
  mapM_ (\ar -> do
            putStrLn "------"
            printFinalRes ar) all_res

  mapM_ (\ar -> do
            let ar' = (\(n, fs) -> (n, fmap (filter ((>= 100) . snd)) fs)) ar
            printInputToScript ar') all_res

runFile :: FilePath -> IO ()
runFile src =
    printFinalRes . (T.pack src,) . Just =<< outputProj src

getFile :: FilePath -> IO (Maybe FilePath)
getFile fp = do
    let p1 = fp </> "Main.hs"
        p2 = fp </> "Main.lhs"
    
    p1_exists <- doesFileExist p1
    p2_exists <- doesFileExist p2

    return $ if | p1_exists -> Just p1
                | p2_exists -> Just p2
                | otherwise -> Nothing

outputProj :: String -> IO [(Name, Int)]
outputProj src = do
  (s@(State { expr_env = eenv }), mods) <- getStateMods src
  ns <- getHigherOrder s mods
  let mods_hs = HS.fromList mods
      ns_hpc = map (\n -> (n, HS.size $ reachesHPC mods_hs eenv (E.lookup n eenv))) ns 
  putStrLn . T.unpack . T.intercalate "\n"
           . map (\(n, c) -> formatName n <> ", " <> T.pack (show c)) $ ns_hpc
  return ns_hpc

getStateMods :: String -> IO (State (), [Maybe T.Text])
getStateMods src = do
  config <- getConfigDirect

  proj <- guessProj (includePaths config) src

  (s, bindings, mods) <- initialStateNoStartFunc
                            proj [src]
                            (simplTranslationConfig { hpc_ticks = True })
                            (config { hpc = True })
  return (s, mods)

getHigherOrder :: State t -> [Maybe T.Text] -> IO [Name]
getHigherOrder s mods = do
  let rel_eenv = E.filterWithKey (\(Name _ m _ _) _ -> m `elem` mods) $ expr_env s
  let rel_funcs_eenv = E.filter isHigherOrderFunc rel_eenv
  return $ E.keys rel_funcs_eenv

isHigherOrderFunc :: Expr -> Bool
isHigherOrderFunc = not . null . higherOrderFuncs . typeOf TV.empty

formatName :: Name -> T.Text
formatName (Name n Nothing _ _) = n
formatName (Name n (Just m) _ _) = m <> "." <> n

printFinalRes :: (T.Text, Maybe [(Name, Int)]) -> IO ()
printFinalRes (fl, Just funcs) =
  putStrLn . T.unpack
           $ fl <> "\n"
                <> T.intercalate
                      "\n"
                      (map (\(n, c) -> formatName n <> ", " <> T.pack (show c)) funcs)
printFinalRes (fl, Nothing) = putStrLn . T.unpack $ fl <> "\nNOT FOUND"

printInputToScript :: (T.Text, Maybe [(Name, Int)]) -> IO ()
printInputToScript (fl, Just funcs) =
    mapM_ (\(n, c) -> 
      putStrLn $ T.unpack fl
             <> ","
             <> T.unpack (formatName n) <> ", " <> show c) funcs

printInputToScript (_, Nothing) = return ()