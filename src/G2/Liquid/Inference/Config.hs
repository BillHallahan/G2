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
import G2.Liquid.Conversion
import G2.Translation.Haskell

import Language.Haskell.Liquid.Types (GhcInfo (..), GhcSpec (..))
import Var as V

import qualified Data.HashSet as S
import qualified Data.Map as M
import qualified Data.Text as T
import Data.Time.Clock

data InferenceConfig = InferenceConfig { keep_quals :: Bool

                                       , modules :: S.HashSet (Maybe T.Text)
                                       , max_ce :: Int

                                       , pre_refined :: S.HashSet  (T.Text, Maybe T.Text)
                                       , refinable_funcs :: S.HashSet (T.Text, Maybe T.Text)
                                       
                                       , timeout_se :: NominalDiffTime
                                       , timeout_sygus :: NominalDiffTime }

mkInferenceConfig :: [String] -> InferenceConfig
mkInferenceConfig as =
    InferenceConfig { keep_quals = boolArg "keep-quals" as M.empty On
                    , modules = S.empty
                    , max_ce = strArg "max-ce" as M.empty read 25
                    , timeout_se = strArg "timeout-se" as M.empty (fromInteger . read) 10
                    , timeout_sygus = strArg "timeout-sygus" as M.empty (fromInteger . read) 10 }

adjustConfig :: Maybe T.Text -> SimpleState -> Config -> InferenceConfig -> [GhcInfo]-> (Config, InferenceConfig)
adjustConfig main_mod (SimpleState { expr_env = eenv }) config infconfig ghci =
    let
        ref = refinable main_mod eenv

        pre = S.fromList
            . map (\(Name n m _ _) -> (n, m))
            . map (mkName . V.varName . fst)
            $ concatMap (gsTySigs . spec) ghci

        ns_mm = map (\(Name n m _ _) -> (n, m))
              . filter (\(Name n m _ _) -> not $ (n, m) `S.member` pre)
              . filter (\(Name n m _ _) -> (n, m) `elem` ref)
              . E.keys $ E.filter (not . tyVarRetTy) eenv

        ns_not_main = map (\(Name n m _ _) -> (n, m))
                    . filter (\(Name _ m _ _) -> m /= main_mod)
                    $ E.keys eenv
    
        config' = config { counterfactual = Counterfactual . CFOnly $ S.fromList ns_mm
                         , only_top = True
                         , block_errors_in = S.fromList ns_not_main }

        infconfig' = infconfig { modules = S.singleton main_mod
                               , pre_refined = pre
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