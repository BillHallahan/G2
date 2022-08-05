module G2.Config.Interface where

import G2.Config.Config

import Options.Applicative
import System.Directory


configName :: FilePath
configName = "g2.cfg"

getConfig :: [String] -> IO (String, String, Config)
getConfig ars = do
    homedir <- getHomeDirectory
    execParser (mkConfigInfo homedir)

mkConfigInfo :: String -> ParserInfo (String, String, Config)
mkConfigInfo homedir =
    info (((,,) <$> getFileName <*> getFunctionName <*> mkConfig homedir) <**> helper)
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
