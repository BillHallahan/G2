module G2.Equiv.Config ( NebulaConfig (..)
                       , SummaryMode (..)
                       , UseLabeledErrors (..)
                       , getNebulaConfig
                       , getNebulaConfigPlugin
                       , mkNebulaConfigInfo
                       , mkNebulaConfig) where

import G2.Config.Config

import qualified Data.Text as T
import Options.Applicative

-- Config options
data NebulaConfig = NC { limit :: Int
                       , num_lemmas :: Int
                       , print_summary :: SummaryMode
                       , use_labeled_errors :: UseLabeledErrors
                       , log_states :: LogMode -- ^ Determines whether to Log states, and if logging states, how to do so.
                       , log_rule :: Maybe String -- ^ Allow user to log the states for specific rule. 
                       , sync :: Bool 
                       , symbolic_unmapped :: Bool}

data SummaryMode = SM { have_summary :: Bool
                      , have_history :: Bool
                      , have_lemma_details :: Bool
                      , only_unresolved :: Bool }

noSummary :: SummaryMode
noSummary = SM False False False False

data UseLabeledErrors = UseLabeledErrors | NoLabeledErrors deriving (Eq, Show, Read)

getNebulaConfig :: IO (String, String, [T.Text], NebulaConfig)
getNebulaConfig = execParser mkNebulaConfigInfo

getNebulaConfigPlugin :: [String] -> ParserResult (Maybe String, NebulaConfig)
getNebulaConfigPlugin =
    execParserPure defaultPrefs $
        info (((,) <$> maybeGetRuleName <*> mkNebulaConfig) <**> helper)
              ( fullDesc
              <> progDesc "Equivalence Checking for Haskell Rewrite Rules"
              <> header "The Nebula Equivalence Checker" )

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

maybeGetRuleName :: Parser (Maybe String)
maybeGetRuleName =
    argument (maybeReader (Just . Just)) (metavar "RULE" <> value Nothing)

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
        <*> mkLogMode
        <*> mkLogRule
        <*> flag False True (long "sync" <> help "sync the left and right expressions prior to symbolic execution")
        <*> flag True False (long "sym-unmapped" <> help "automatically treat unmapped function as symbolic")

mkLogRule :: Parser (Maybe String)
mkLogRule =
    option (maybeReader (Just . Just))
            ( long "log-rule"
            <> metavar "RULE"
            <> value Nothing
            <> help "Output states for this rule when logging")

mkSummaryMode :: Parser SummaryMode
mkSummaryMode =
    (flag noSummary (SM True False False False)
            (long "summarize"
            <> help "provide a summary with no history"))
    <|>
    (flag noSummary (SM True False False True)
            (long "unresolved-summarize"
            <> help "summarize only the unresolved obligations"))
    <|>
    (flag noSummary (SM True True False True)
            (long "unresolved-hist-summarize"
            <> help "unresolved obligations with histories"))
    <|>
    (flag noSummary (SM True True False False)
            (long "hist-summarize"
            <> help "provide a summary with history"))
    <|>
    (flag noSummary (SM True False True False)
            (long "lemmas-summarize"
            <> help "provide a summary with all lemma results"))
    <|>
    (flag noSummary (SM True True True False)
            (long "lemmas-hist-summarize"
            <> help "provide a summary with history and lemma results"))
