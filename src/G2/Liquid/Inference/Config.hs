{-# LANGUAGE OverloadedStrings #-}

module G2.Liquid.Inference.Config ( InferenceConfig (..)
                                  , mkInferenceConfig
                                  , adjustConfig) where

import G2.Config.Config
import G2.Initialization.Types
import G2.Language (ExprEnv
                   , Name (..)
                   , Type (..)
                   , returnType)
import qualified G2.Language.ExprEnv as E

import qualified Data.HashSet as S
import qualified Data.Map as M
import qualified Data.Text as T
import Data.Time.Clock

data InferenceConfig = InferenceConfig { modules :: S.HashSet (Maybe T.Text)
                                       , max_ce :: Int 
                                       
                                       , timeout_se :: NominalDiffTime
                                       , timeout_sygus :: NominalDiffTime }

mkInferenceConfig :: [String] -> InferenceConfig
mkInferenceConfig as =
    InferenceConfig { modules = S.empty
                    , max_ce = strArg "max-ce" as M.empty read 25
                    , timeout_se = strArg "timeout-se" as M.empty (fromInteger . read) 10
                    , timeout_sygus = strArg "timeout-sygus" as M.empty (fromInteger . read) 10 }

adjustConfig :: Maybe T.Text -> SimpleState -> Config -> Config
adjustConfig main_mod (SimpleState { expr_env = eenv }) config =
    let
        ns_mm = refinable main_mod eenv

        ns_nmm = map (\(Name n m _ _) -> (n, m))
               . filter (\(Name _ m _ _) -> m /= main_mod)
               $ E.keys eenv
    in
    config { counterfactual = Counterfactual CFAll -- . CFOnly $ S.fromList ns_mm
           , block_errors_in = S.empty }

refinable :: Maybe T.Text -> ExprEnv -> [(T.Text, Maybe T.Text)]
refinable main_mod eenv = 
    let
        ns_mm = filter (\(Name _ m _ _) -> m == main_mod) $ E.keys eenv
        ns_mm' = map (\(Name n m _ _) -> (n, m)) ns_mm
    in
    ns_mm'