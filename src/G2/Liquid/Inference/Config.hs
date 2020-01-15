{-# LANGUAGE OverloadedStrings #-}

module G2.Liquid.Inference.Config ( InferenceConfig (..)
                                  , mkInferenceConfig
                                  , adjustConfig) where

import G2.Config.Config
import G2.Initialization.Types
import G2.Language ( ExprEnv
                   , Expr
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

                                       , refinable_funcs :: S.HashSet (T.Text, Maybe T.Text)
                                       
                                       , timeout_se :: NominalDiffTime
                                       , timeout_sygus :: NominalDiffTime }

mkInferenceConfig :: [String] -> InferenceConfig
mkInferenceConfig as =
    InferenceConfig { modules = S.empty
                    , max_ce = strArg "max-ce" as M.empty read 25
                    , timeout_se = strArg "timeout-se" as M.empty (fromInteger . read) 10
                    , timeout_sygus = strArg "timeout-sygus" as M.empty (fromInteger . read) 10 }

adjustConfig :: Maybe T.Text -> SimpleState -> Config -> InferenceConfig -> (Config, InferenceConfig)
adjustConfig main_mod (SimpleState { expr_env = eenv }) config infconfig =
    let
        ns_mm = map (\(Name n m _ _) -> (n, m))
              . E.keys $ E.filter (not . tyVarRetTy) eenv

        ns_nmm = map (\(Name n m _ _) -> (n, m))
               . filter (\(Name _ m _ _) -> m /= main_mod)
               $ E.keys eenv
    
        config' = config { counterfactual = Counterfactual . CFOnly $ S.fromList ns_mm
                         , block_errors_in = S.empty }

        infconfig' = infconfig { modules = S.singleton main_mod 
                               , refinable_funcs = S.fromList ns_mm }
    in
    (config', infconfig')

refinable :: Maybe T.Text -> ExprEnv -> [(T.Text, Maybe T.Text)]
refinable main_mod eenv = 
    let
        ns_mm = filter (\(Name _ m _ _) -> m == main_mod)
              . E.keys $ E.filter (not . tyVarRetTy) eenv
        ns_mm' = map (\(Name n m _ _) -> (n, m)) ns_mm
    in
    ns_mm'

tyVarRetTy :: Expr -> Bool
tyVarRetTy e =
    case returnType e of
        TyVar _ -> True
        _ -> False