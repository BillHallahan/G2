{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Liquid.Inference.Config (
                                    Progress (..)
                                  , Progresser (..)
                                  , ProgresserM (..)
                                  , newProgress
                                  , runProgresser

                                  , InfConfigM (..)
                                  , InferenceConfig (..)
                                  , Configs (..)
                                  , InfConfig (..)
                                  , runConfigs

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
import qualified Language.Haskell.Liquid.Types as LH
import Var as V

import Control.Monad.Reader
import Control.Monad.State.Lazy
import qualified Data.HashSet as S
import qualified Data.Map as M
import qualified Data.Text as T
import Data.Time.Clock

-------------------------------
-- Progresser
-------------------------------

data Progress = Progress { ex_max_ce :: Int -- ^ Gives an extra budget for maximum ce number
                         , ex_max_depth :: Int -- ^ Gives an extra budget for the depth limit
                         }

newProgress :: Progress
newProgress = Progress { ex_max_ce = 0 
                       , ex_max_depth = 0  }

class Progresser p where
    extraMaxCEx ::  p -> Int
    incrMaxCEx :: p -> p

    extraMaxDepth ::  p -> Int
    incrMaxDepth :: p -> p

instance Progresser Progress where
    extraMaxCEx (Progress { ex_max_ce = m }) = m
    incrMaxCEx p@(Progress { ex_max_ce = m }) = p { ex_max_ce = m + 2 }

    extraMaxDepth (Progress { ex_max_depth = m }) = m
    incrMaxDepth p@(Progress { ex_max_depth = m }) = p { ex_max_depth = m + 200 }

class Monad m => ProgresserM m where
    extraMaxCExM :: m Int
    incrMaxCExM :: m ()

    extraMaxDepthM :: m Int
    incrMaxDepthM :: m ()

instance (Monad m, Progresser p) => ProgresserM (StateT p m) where
    extraMaxCExM = gets extraMaxCEx
    incrMaxCExM = modify' incrMaxCEx

    extraMaxDepthM = gets extraMaxDepth
    incrMaxDepthM = modify' incrMaxDepth

instance ProgresserM m => ProgresserM (ReaderT env m) where
    extraMaxCExM = lift extraMaxCExM
    incrMaxCExM = lift incrMaxCExM

    extraMaxDepthM = lift extraMaxDepthM
    incrMaxDepthM = lift incrMaxDepthM

runProgresser :: (Monad m, Progresser p) => StateT p m a -> p -> m a
runProgresser = evalStateT

-------------------------------
-- Configurations
-------------------------------

data Configs = Configs { g2_config :: Config
                       , lh_config :: LH.Config
                       , inf_config :: InferenceConfig }

class InfConfig c where
    g2Config :: c -> Config
    lhConfig :: c -> LH.Config
    infConfig :: c -> InferenceConfig

class Monad m => InfConfigM m where
    g2ConfigM :: m Config
    lhConfigM :: m LH.Config
    infConfigM :: m InferenceConfig

instance InfConfig Configs where
    g2Config = g2_config
    lhConfig = lh_config
    infConfig = inf_config

instance InfConfig env => InfConfig (ReaderT env m a) where
    g2Config = return . g2Config =<< ask
    lhConfig = return . lhConfig =<< ask
    infConfig = return . infConfig =<< ask

instance (Monad m, InfConfig env) => InfConfigM (ReaderT env m) where 
    g2ConfigM = return . g2Config =<< ask 
    lhConfigM = return . lhConfig =<< ask 
    infConfigM = return . infConfig =<< ask 

instance InfConfigM m => InfConfigM (StateT env m) where
    g2ConfigM = lift g2ConfigM
    lhConfigM = lift lhConfigM
    infConfigM = lift infConfigM


data InferenceConfig = InferenceConfig { keep_quals :: Bool

                                       , modules :: S.HashSet (Maybe T.Text)
                                       , max_ce :: Int

                                       , pre_refined :: S.HashSet  (T.Text, Maybe T.Text)
                                       , refinable_funcs :: S.HashSet (T.Text, Maybe T.Text)
                                       
                                       , timeout_se :: NominalDiffTime
                                       , timeout_sygus :: NominalDiffTime }

runConfigs :: InfConfig env => ReaderT env m a -> env -> m a
runConfigs = runReaderT

mkInferenceConfig :: [String] -> InferenceConfig
mkInferenceConfig as =
    InferenceConfig { keep_quals = boolArg "keep-quals" as M.empty On
                    , modules = S.empty
                    , max_ce = strArg "max-ce" as M.empty read 10
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
              -- . filter (\(Name n m _ _) -> not $ (n, m) `S.member` pre)
              . filter (\(Name n _ _ _) -> n `notElem` [ "mapReduce", "singleton", "concat", "append"
                                                       , "map", "replicate", "empty", "zipWith", "add", "divide"])
              . filter (\(Name n m _ _) -> (n, m) `elem` ref)
              . E.keys $ E.filter (not . tyVarRetTy) eenv

        ns_not_main = filter (\(n, _) -> n == "foldr1")
                    . map (\(Name n m _ _) -> (n, m))
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

