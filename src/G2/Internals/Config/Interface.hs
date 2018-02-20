module G2.Internals.Config.Interface where

import G2.Internals.Config.Config
import G2.Internals.Config.ParseConfig

import qualified Data.Map as M

getConfig :: [String] -> IO Config
getConfig ars = do
    conf <- parseConfig "g2.cfg"

    case conf of
        Right conf' -> return (mkConfig ars conf')
        Left e -> do
            putStrLn "Configuration file parsing error:"
            print e
            return (mkConfig ars M.empty)