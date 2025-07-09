module G2.Verify.Config ( VerifyConfig (..)
                        , getVerifyConfigs
                        , defVerifyConfig) where

import G2.Config

import Data.Maybe
import Options.Applicative
import System.Directory

data VerifyConfig = VerifyConfig { rev_abs :: Bool
                                 , approx :: Bool }

getVerifyConfigs :: IO (String, String, VerifyConfig, Config)
getVerifyConfigs = do
    homedir <- getHomeDirectory
    execParser (mkFullVerifyConfigInfo homedir)

mkFullVerifyConfigInfo :: String -> ParserInfo (String, String, VerifyConfig, Config)
mkFullVerifyConfigInfo homedir =
    info (((,,,)
                <$> getFileName
                <*> getFunctionName
                <*> mkVerifyConfig
                <*> mkConfig homedir) <**> helper)
          ( fullDesc
          <> progDesc "Verification and Refutation of Haskell Properties"
          <> header "The G2 Verifier" )

mkVerifyConfigInfo :: ParserInfo VerifyConfig
mkVerifyConfigInfo = info 
          mkVerifyConfig
          ( fullDesc
          <> progDesc "Verification and Refutation of Haskell Properties"
          <> header "The G2 Verifier" )

mkVerifyConfig :: Parser VerifyConfig
mkVerifyConfig = VerifyConfig
            <$> flag True False (long "no-rev-abs" <> help "Do not use reversible abstractions")
            <*> flag True False (long "no-approx" <> help "Do not use approximation")

defVerifyConfig :: VerifyConfig
defVerifyConfig = fromJust . getParseResult $ execParserPure defaultPrefs mkVerifyConfigInfo []