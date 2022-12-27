module G2.Config.Interface where

import G2.Config.Config

import qualified Data.Map.Lazy as M
import Data.Monoid ((<>))
import Options.Applicative
import System.Directory

configName :: FilePath
configName = "g2.cfg"

getConfigDirect :: IO Config
getConfigDirect = do
    homedir <- getHomeDirectory
    return $ mkConfigDirect homedir [] M.empty

getConfig :: IO (String, String, Maybe String, Maybe String, Config)
getConfig = do
    homedir <- getHomeDirectory
    execParser (mkConfigInfo homedir)

mkConfigInfo :: String -> ParserInfo (String, String, Maybe String, Maybe String, Config)
mkConfigInfo homedir =
    info (((,,,,)
                <$> getFileName
                <*> getFunctionName
                <*> option (eitherReader (Right . Just))
                   (long "assume"
                   <> metavar "F"
                   <> value Nothing
                   <> help "a function to use as an assumption")
                <*> option (eitherReader (Right . Just))
                   (long "assert"
                   <> metavar "F"
                   <> value Nothing
                   <> help "a function to use as an assertion")
                <*> mkConfig homedir) <**> helper)
          ( fullDesc
          <> progDesc "Symbolic Execution of Haskell code"
          <> header "The G2 Symbolic Execution Engine" )

getFileName :: Parser String
getFileName = argument str (metavar "FILE")

getFunctionName :: Parser String
getFunctionName = argument str (metavar "FUNCTION")

configExists :: FilePath -> IO Bool
configExists cn = do
    ex <- doesFileExist cn

    case ex of
        True -> return ()
        False -> putStrLn $ "Configuration file " ++ cn ++ " missing"

    return ex
