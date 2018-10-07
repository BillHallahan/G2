module G2.Internals.Config.Interface where

import G2.Internals.Config.Config
import G2.Internals.Config.ParseConfig

import qualified Data.Map as M
import System.Directory

configName :: FilePath
configName = "g2.cfg"

getConfig :: [String] -> IO Config
getConfig ars = do
    ex <- configExists

    case ex of
        True -> do
            conf <- parseConfig configName

            case conf of
                Right conf' -> return (mkConfig ars conf')
                Left e -> do
                    putStrLn "Configuration file parsing error:"
                    print e
                    return (mkConfig ars M.empty)
        False -> return (mkConfig ars M.empty)

configExists :: IO Bool
configExists = do
    ex <- doesFileExist configName

    case ex of
        True -> return ()
        False -> putStrLn $ "Configuration file " ++ configName ++ " missing"

    return ex
