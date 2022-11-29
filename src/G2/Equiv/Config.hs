module G2.Equiv.Config ( NebulaConfig (..)
                       , SummaryMode (..)
                       , UseLabeledErrors (..)
                       , getNebulaConfig
                       , mkNebulaConfigInfo
                       , mkNebulaConfig) where

import Data.Monoid ((<>))
import qualified Data.Text as T
import Options.Applicative

-- Config options
data NebulaConfig = NC { limit :: Int
                       , num_lemmas :: Int
                       , print_summary :: SummaryMode
                       , use_labeled_errors :: UseLabeledErrors
                       , sync :: Bool }

data SummaryMode = NoHistory | WithHistory | NoSummary deriving Eq

data UseLabeledErrors = UseLabeledErrors | NoLabeledErrors deriving (Eq, Show, Read)

getNebulaConfig :: IO (String, String, [T.Text], NebulaConfig)
getNebulaConfig = execParser mkNebulaConfigInfo

mkNebulaConfigInfo :: ParserInfo (String, String, [T.Text], NebulaConfig)
mkNebulaConfigInfo =
    info (((,,,) <$> getFileName <*> getRuleName <*> getTotal <*> mkNebulaConfig) <**> helper)
          ( fullDesc
          <> progDesc "Equivalence Checking for Haskell Rewrite Rules"
          <> header "The Nebula Equivalence Checker" )

getFileName :: Parser String
getFileName = argument str (metavar "FILE")

getRuleName :: Parser String
getRuleName = argument str (metavar "RULE")

getTotal :: Parser [T.Text]
getTotal = many (argument (maybeReader (Just . T.pack)) (metavar "TOTAL"))

mkNebulaConfig :: Parser NebulaConfig
mkNebulaConfig = NC
        <$> option auto (long "limit"
                   <> metavar "N"
                   <> value (-1)
                   <> help "how many iterations the equivalence checker should go through before giving up")
        <*> option auto (long "num_lemmas"
                   <> metavar "L"
                   <> value 2
                   <> help "how many lemmas can be applied to an expression simultaneously")
        <*> mkSummaryMode
        <*> flag UseLabeledErrors NoLabeledErrors (long "no-labeled-errors" <> help "disable labeled errors, treating all errors as equivalent")
        <*> flag False True (long "sync" <> help "sync the left and right expressions prior to symbolic execution")

mkSummaryMode :: Parser SummaryMode
mkSummaryMode =
    (flag NoSummary NoHistory
            (long "summarize"
            <> help "log all states with raw printing"))
    <|>
    (flag NoSummary WithHistory
            (long "hist-summarize"
            <> help "log all states with pretty printing"))
