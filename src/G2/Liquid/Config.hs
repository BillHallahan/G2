module G2.Liquid.Config ( LHConfig (..)
                        , Counterfactual (..)
                        , CFModules (..)
                        , BlockErrorsMethod (..)
                        , getLHConfig
                        , mkLHConfig
                        , mkLHConfigDirect) where

import G2.Config.Config

import qualified Data.HashSet as S
import qualified Data.Map.Lazy as M
import qualified Data.Text as T
import Options.Applicative
import System.Directory

data Counterfactual = Counterfactual CFModules | NotCounterfactual deriving (Eq, Show, Read)

data CFModules = CFAll | CFOnly (S.HashSet (T.Text, Maybe T.Text)) deriving (Eq, Show, Read)

data BlockErrorsMethod = ArbBlock
                       | AssumeBlock deriving (Eq, Show, Read)

data LHConfig = LHConfig {
      cut_off :: Int -- ^ How many steps to take after finding an equally good equiv state, in LH mode
    , switch_after :: Int --- ^ How many steps to take in a single step, in LH mode
    , counterfactual :: Counterfactual -- ^ Which functions should be able to generate abstract counterexamples
    , only_top :: Bool -- ^ Only try to find counterexamples in the very first function definition, or directly called functions?
    , block_errors_in :: (S.HashSet (T.Text, Maybe T.Text)) -- ^ Prevents calls from errors occuring in the indicated functions
    , block_errors_method :: BlockErrorsMethod -- ^ Should errors be blocked with an Assume or with an arbitrarily inserted value
    , reduce_abs :: Bool
    , add_tyvars :: Bool
    }

getLHConfig :: IO (String, String, Config, LHConfig)
getLHConfig = do
    homedir <- getHomeDirectory
    execParser (mkConfigInfo homedir)

mkConfigInfo :: String -> ParserInfo (String, String, Config, LHConfig)
mkConfigInfo homedir =
    info (((,,,) <$> getFileName <*> getFunctionName <*> mkConfig homedir <*> mkLHConfig) <**> helper)
          ( fullDesc
          <> progDesc "Allows symbolically executing LiquidHaskell code"
          <> header "The G2 Symbolic Execution Engine" )

getFileName :: Parser String
getFileName = argument str (metavar "FILE")

getFunctionName :: Parser String
getFunctionName = argument str (metavar "FUNCTION")

mkLHConfig :: Parser LHConfig
mkLHConfig = LHConfig
    <$> option auto (long "cut-off"
                   <> metavar "N"
                   <> value 600
                   <> help "how many steps to take after finding an equally good equivalent state, in LH mode ")
    <*> option auto (long "switch-after"
                   <> metavar "N"
                   <> value 300
                   <> help "how many steps to take before switching states, in LH mode ")
    <*> flag (Counterfactual CFAll) (NotCounterfactual) (long "no-counterfactual" <> help "disable counterfactual counterexamples")
    <*> pure False
    <*> pure S.empty
    <*> pure AssumeBlock
    <*> pure True
    <*> pure False


mkLHConfigDirect :: [String] -> M.Map String [String] -> LHConfig
mkLHConfigDirect as m = LHConfig {
      cut_off = strArg "cut-off" as m read 600
    , switch_after = strArg "switch-after" as m read 300
    , counterfactual = boolArg' "counterfactual" as
                        (Counterfactual CFAll) (Counterfactual CFAll) NotCounterfactual
    , only_top = False
    , block_errors_in = S.empty
    , block_errors_method = AssumeBlock
    , reduce_abs = True
    , add_tyvars = False
}
