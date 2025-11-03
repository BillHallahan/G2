module G2.Verify.Config ( VerifyConfig (..)
                        , AbsFuncArgs (..)
                        , AbsDataArgs (..)
                        , SharedVarHeuristic (..)
                        , getVerifyConfigs
                        , defVerifyConfig) where

import G2.Config

import Data.Maybe
import Options.Applicative
import System.Directory

data VerifyConfig = VerifyConfig { rev_abs :: Bool
                                 , arg_rev_abs :: AbsFuncArgs
                                 , data_arg_rev_abs :: AbsDataArgs
                                 , shared_var_heuristic :: SharedVarHeuristic
                                 , approx :: Bool }

data AbsFuncArgs = AbsFuncArgs | NoAbsFuncArgs deriving Eq

data AbsDataArgs = AbsDataArgs | NoAbsDataArgs deriving Eq

data SharedVarHeuristic = SharedVarHeuristic | NoSharedVarHeuristic deriving Eq

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
            <*> flag NoAbsDataArgs AbsDataArgs (long "data-arg-rev-abs" <> help "Apply reversible abstraction through data constructors in function arguments")
            <*> flag NoSharedVarHeuristic SharedVarHeuristic (long "shared-var-heuristic" <> help "Apply reversible abstraction to function argumentsonly if there are shared variables")
            <*> flag True False (long "no-approx" <> help "Do not use approximation")

defVerifyConfig :: VerifyConfig
defVerifyConfig = fromJust . getParseResult $ execParserPure defaultPrefs mkVerifyConfigInfo []