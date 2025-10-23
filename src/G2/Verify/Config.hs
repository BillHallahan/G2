module G2.Verify.Config ( VerifyConfig (..)
                        , AbsFuncArgs (..)
                        , getVerifyConfigs
                        , defVerifyConfig) where

import G2.Config

import Data.Maybe
import Options.Applicative
import System.Directory

data VerifyConfig = VerifyConfig { rev_abs :: Bool
                                 , arg_rev_abs :: AbsFuncArgs
                                 , approx :: Bool }

data AbsFuncArgs = AbsFuncArgs | NoAbsFuncArgs deriving Eq

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
            <*> flag AbsFuncArgs NoAbsFuncArgs (long "no-arg-rev-abs" <> help "Do not apply reversible abstractions to function arguments")
            <*> flag True False (long "no-approx" <> help "Do not use approximation")

defVerifyConfig :: VerifyConfig
defVerifyConfig = fromJust . getParseResult $ execParserPure defaultPrefs mkVerifyConfigInfo []