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
                                  , adjustConfig
                                  , adjustConfigPostLH ) where

import G2.Config.Config
import G2.Initialization.Types
import G2.Language ( ExprEnv
                   , Expr
                   , Name (..)
                   , Type (..))
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.Support as S
import G2.Language.Typing
import G2.Liquid.Conversion
import G2.Liquid.Helpers
import G2.Liquid.TCValues
import G2.Liquid.Types
import G2.Liquid.Inference.PolyRef
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

data Progress =
    Progress { ex_max_ce :: M.Map (T.Text, Maybe T.Text) Int -- ^ Gives an extra budget for maximum ce number
             , ex_max_depth :: Int -- ^ Gives an extra budget for the depth limit
             , ex_max_time :: M.Map (T.Text, Maybe T.Text) NominalDiffTime -- ^ Gives an extra max bufget for time
             }

newProgress :: Progress
newProgress = Progress { ex_max_ce = M.empty
                       , ex_max_depth = 0
                       , ex_max_time = M.empty }

class Progresser p where
    extraMaxCEx ::  (T.Text, Maybe T.Text) -> p -> Int
    incrMaxCEx :: (T.Text, Maybe T.Text) -> p -> p

    extraMaxDepth ::  p -> Int
    incrMaxDepth :: p -> p

    extraMaxTime :: (T.Text, Maybe T.Text) -> p -> NominalDiffTime
    incrMaxTime :: (T.Text, Maybe T.Text) -> p -> p

instance Progresser Progress where
    extraMaxCEx n (Progress { ex_max_ce = m }) = M.findWithDefault 0 n m
    incrMaxCEx n p@(Progress { ex_max_ce = m }) =
        p { ex_max_ce = M.insertWith (+) n 2 m }

    extraMaxDepth (Progress { ex_max_depth = m }) = m
    incrMaxDepth p@(Progress { ex_max_depth = m }) = p { ex_max_depth = m + 200 }

    extraMaxTime n (Progress { ex_max_time = m }) = M.findWithDefault 0 n m
    incrMaxTime n p@(Progress { ex_max_time = m }) =
        p { ex_max_time = M.insertWith (+) n 4 m }

class Monad m => ProgresserM m where
    extraMaxCExM :: (T.Text, Maybe T.Text) -> m Int
    incrMaxCExM :: (T.Text, Maybe T.Text) -> m ()

    extraMaxDepthM :: m Int
    incrMaxDepthM :: m ()

    extraMaxTimeM :: (T.Text, Maybe T.Text) -> m NominalDiffTime
    incrMaxTimeM :: (T.Text, Maybe T.Text) -> m ()

instance (Monad m, Progresser p) => ProgresserM (StateT p m) where
    extraMaxCExM n = gets (extraMaxCEx n)
    incrMaxCExM n = modify' (incrMaxCEx n)

    extraMaxDepthM = gets extraMaxDepth
    incrMaxDepthM = modify' incrMaxDepth

    extraMaxTimeM n = gets (extraMaxTime n)
    incrMaxTimeM n = modify' (incrMaxTime n)

instance ProgresserM m => ProgresserM (ReaderT env m) where
    extraMaxCExM n = lift (extraMaxCExM n)
    incrMaxCExM n = lift (incrMaxCExM n)

    extraMaxDepthM = lift extraMaxDepthM
    incrMaxDepthM = lift incrMaxDepthM

    extraMaxTimeM n = lift (extraMaxTimeM n)
    incrMaxTimeM n = lift (incrMaxTimeM n)

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


data InferenceConfig =
    InferenceConfig { keep_quals :: Bool

                    , modules :: S.HashSet (Maybe T.Text)
                    , max_ce :: Int

                    , pre_refined :: S.HashSet  (T.Text, Maybe T.Text)
                    , refinable_funcs :: S.HashSet (T.Text, Maybe T.Text)

                    , restrict_coeffs :: Bool -- ^ If true, only allow coefficients in the range of -1 <= c <= 1

                    , use_extra_fcs :: Bool -- ^ If true, generate as many constraints as possible, if false, generate
                                            -- only those that are essential to block bad specifications 
                   
                    , timeout_se :: NominalDiffTime
                    , timeout_sygus :: NominalDiffTime }

runConfigs :: InfConfig env => ReaderT env m a -> env -> m a
runConfigs = runReaderT

mkInferenceConfig :: [String] -> InferenceConfig
mkInferenceConfig as =
    InferenceConfig { keep_quals = boolArg "keep-quals" as M.empty On
                    , modules = S.empty
                    , max_ce = strArg "max-ce" as M.empty read 5
                    , restrict_coeffs = boolArg "restrict-coeffs" as M.empty Off
                    , use_extra_fcs = boolArg "use-extra-fc" as M.empty On
                    , timeout_se = strArg "timeout-se" as M.empty (fromInteger . read) 5
                    , timeout_sygus = strArg "timeout-sygus" as M.empty (fromInteger . read) 10 }

adjustConfig :: Maybe T.Text -> SimpleState -> Config -> InferenceConfig -> [GhcInfo] -> (Config, InferenceConfig)
adjustConfig main_mod (SimpleState { expr_env = eenv }) config infconfig ghci =
    let
        -- ref = refinable main_mod meas tcv eenv

        pre = S.fromList
            . map (\(Name n m _ _) -> (n, m))
            . map (mkName . V.varName . fst)
            $ concatMap (gsTySigs . spec) ghci

        -- ns_mm = map (\(Name n m _ _) -> (n, m))
        --       -- . filter (\(Name n m _ _) -> not $ (n, m) `S.member` pre)
        --       -- . filter (\(Name n _ _ _) -> n `notElem` [ "mapReduce" ])
        --       -- . filter (\(Name n _ _ _) -> n `notElem` [ "mapReduce", "singleton", "concat", "append"
        --       --                                          , "map", "replicate", "empty", "zipWith", "add"])
        --       . filter (\(Name n m _ _) -> (n, m) `elem` ref)
        --       . E.keys
        --       . E.filter (not . tyVarNoMeas meas tcv)
        --       $ E.filter (not . tyVarRetTy) eenv

        ns_not_main = filter (\(n, _) -> n == "foldr1")
                    . map (\(Name n m _ _) -> (n, m))
                    . filter (\(Name _ m _ _) -> m /= main_mod)
                    $ E.keys eenv
    
        config' = config { only_top = True
                         , block_errors_in = S.fromList ns_not_main }

        infconfig' = infconfig { modules = S.singleton main_mod
                               , pre_refined = pre }
    in
    (config', infconfig')

adjustConfigPostLH :: Maybe T.Text -> Measures -> TCValues -> S.State t -> [GhcInfo] -> Config -> Config
adjustConfigPostLH main_mod meas tcv (S.State { S.expr_env = eenv, S.known_values = kv }) ghci config =
    let
        ref = refinable main_mod meas tcv ghci kv eenv
        
        ns_mm = map (\(Name n m _ _) -> (n, m))
              -- . filter (\(Name n m _ _) -> not $ (n, m) `S.member` pre)
              -- . filter (\(Name n _ _ _) -> n `notElem` [ "mapReduce" ])
              -- . filter (\(Name n _ _ _) -> n `notElem` [ "mapReduce", "singleton", "concat", "append"
              --                                          , "map", "replicate", "empty", "zipWith", "add"])
              . filter (\(Name n m _ _) -> (n, m) `elem` ref)
              $ E.keys eenv
              -- . E.filter (not . tyVarNoMeas meas tcv)
              -- $ E.filter (not . tyVarRetTy) eenv

    in
    config { counterfactual = Counterfactual . CFOnly $ S.fromList ns_mm }

refinable :: Maybe T.Text -> Measures -> TCValues -> [GhcInfo] -> S.KnownValues -> ExprEnv -> [(T.Text, Maybe T.Text)]
refinable main_mod meas tcv ghci kv eenv = 
    let
        ns_mm = E.keys
              . E.filter (\e -> not (tyVarNoMeas meas tcv ghci e) || isPrimRetTy kv e)
              . E.filter (not . tyVarRetTy)
              $ E.filterWithKey (\(Name _ m _ _) _ -> m == main_mod) eenv
        ns_mm' = map (\(Name n m _ _) -> (n, m)) ns_mm
    in
    ns_mm'

isPrimRetTy :: S.KnownValues -> Expr -> Bool
isPrimRetTy kv e =
    let
        rel_t = extractValues . extractTypePolyBound $ returnType e
    in
    any (\t -> t == tyInt kv) rel_t

tyVarNoMeas :: Measures -> TCValues -> [GhcInfo] -> Expr -> Bool
tyVarNoMeas meas tcv ghci e =
    let
        rel_t = extractValues . extractTypePolyBound $ returnType e
        rel_meas = E.filter (\e -> 
                            case filter notLH . argumentTypes . PresType . inTyForAlls $ typeOf e of
                                  [t] -> any (\t' -> fst $ t' `specializes` t) rel_t
                                  _ -> False ) meas'
    in
    E.null rel_meas
    where
        meas_names = measureNames ghci
        meas_nameOcc = map (\(Name n md _ _) -> (n, md)) $ map symbolName meas_names
        meas' = E.filterWithKey (\(Name n m _ _) _ -> (n, m) `elem` meas_nameOcc) meas

        notLH t
            | TyCon n _ <- tyAppCenter t = n /= lhTC tcv
            | otherwise = False

tyVarRetTy :: Expr -> Bool
tyVarRetTy e =
    case returnType e of
        TyVar _ -> True
        _ -> False

