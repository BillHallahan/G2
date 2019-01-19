module G2.Config.Interface where

import G2.Config.Config
import G2.Config.ParseConfig

import qualified Data.Map as M
import System.Directory

configName :: FilePath
configName = "g2.cfg"

getConfig :: [String] -> IO Config
getConfig ars = do
    let con = strArg "config" ars M.empty id configName

    ex <- configExists con

    case ex of
        True -> do
            conf <- parseConfig con

            case conf of
                Right conf' -> return (mkConfig ars conf')
                Left e -> do
                    putStrLn "Configuration file parsing error:"
                    print e
                    return (mkConfig ars M.empty)
        False -> return (mkConfig ars M.empty)

configExists :: FilePath -> IO Bool
configExists cn = do
    ex <- doesFileExist cn

    case ex of
        True -> return ()
        False -> putStrLn $ "Configuration file " ++ cn ++ " missing"

    return ex
