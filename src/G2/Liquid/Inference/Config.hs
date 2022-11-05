{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Liquid.Inference.Config (
                                    Progress (..)
                                  , Progresser (..)
                                  , ProgresserM (..)
                                  , MaxSize (..)
                                  , newProgress
                                  , runProgresser

                                  , InfConfigM (..)
                                  , InferenceConfig (..)
                                  , Configs (..)
                                  , InfConfig (..)
                                  , runConfigs

                                  , getAllConfigsForInf
                                  , mkInferenceConfig
                                  , mkInferenceConfigDirect
                                  , adjustConfig
                                  , adjustConfigPostLH

                                  , incrMaxSize ) where

import G2.Config.Config
import G2.Initialization.Types
import G2.Language ( ExprEnv
                   , Expr
                   , Name (..)
                   , Type (..))
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.Support as S
import G2.Language.Typing
import G2.Liquid.Config
import G2.Liquid.Conversion
import G2.Liquid.Helpers
import G2.Liquid.TCValues
import G2.Liquid.Types
import G2.Liquid.Inference.PolyRef
import G2.Translation.Haskell

#if MIN_VERSION_liquidhaskell(0,8,10)
import G2.Liquid.Types (GhcInfo (..), GhcSpec (..))
#else
import Language.Haskell.Liquid.Types (GhcInfo (..), GhcSpec (..))
#endif
import qualified Language.Haskell.Liquid.Types as LH
import Var as V

import Control.Monad.Reader
import Control.Monad.State.Lazy
import qualified Data.HashSet as S
import qualified Data.Map as M
import Data.Monoid ((<>))
import qualified Data.Text as T
import Data.Time.Clock
import Options.Applicative
import System.Directory


-------------------------------
-- Progresser
-------------------------------

newtype MaxSize = MaxSize Integer

data Progress =
    Progress { ex_max_ce :: M.Map (T.Text, Maybe T.Text) Int -- ^ Gives an extra budget for maximum ce number
             , ex_max_depth :: Int -- ^ Gives an extra budget for the depth limit
             , ex_max_time :: M.Map (T.Text, Maybe T.Text) NominalDiffTime -- ^ Gives an extra max bufget for time
             , max_synth_form_size :: MaxSize
             , max_synth_coeff_size :: MaxSize
             , synth_fresh :: Int -- ^ An int to increment to get fresh names
             }

newProgress :: Progress
newProgress = Progress { ex_max_ce = M.empty
                       , ex_max_depth = 0
                       , ex_max_time = M.empty
                       , max_synth_form_size = MaxSize 1
                       , max_synth_coeff_size = MaxSize 2
                       , synth_fresh = 0 }

class Progresser p where
    extraMaxCEx ::  (T.Text, Maybe T.Text) -> p -> Int
    incrMaxCEx :: (T.Text, Maybe T.Text) -> p -> p

    extraMaxDepth ::  p -> Int
    incrMaxDepth :: p -> p

    extraMaxTime :: (T.Text, Maybe T.Text) -> p -> NominalDiffTime
    incrMaxTime :: (T.Text, Maybe T.Text) -> p -> p

    maxSynthFormSize :: p -> MaxSize
    incrMaxSynthFormSize :: p -> p

    maxSynthCoeffSize :: p -> MaxSize
    incrMaxSynthCoeffSize :: p -> p
    setMaxSynthCoeffSize :: MaxSize -> p -> p

    synthFresh :: p -> Int
    incrSynthFresh :: p -> p

instance Progresser Progress where
    extraMaxCEx n (Progress { ex_max_ce = m }) = M.findWithDefault 0 n m
    incrMaxCEx n p@(Progress { ex_max_ce = m }) =
        p { ex_max_ce = M.insertWith (+) n 2 m }

    extraMaxDepth (Progress { ex_max_depth = m }) = m
    incrMaxDepth p@(Progress { ex_max_depth = m }) = p { ex_max_depth = m + 200 }

    extraMaxTime n (Progress { ex_max_time = m }) = M.findWithDefault 0 n m
    incrMaxTime n p@(Progress { ex_max_time = m }) =
        p { ex_max_time = M.insertWith (+) n 4 m }

    maxSynthFormSize (Progress { max_synth_form_size = mss }) = mss
    incrMaxSynthFormSize p@(Progress { max_synth_form_size = mss }) = p { max_synth_form_size = incrMaxSize 1 mss }

    maxSynthCoeffSize (Progress { max_synth_coeff_size = mss }) = mss
    incrMaxSynthCoeffSize p@(Progress { max_synth_coeff_size = mss }) = p { max_synth_coeff_size = incrMaxSize 2 mss }
    setMaxSynthCoeffSize max_size p = p { max_synth_coeff_size = max_size }


    synthFresh (Progress { synth_fresh = syf }) = syf
    incrSynthFresh p@(Progress { synth_fresh = syf }) = p { synth_fresh = syf + 1 }

class Monad m => ProgresserM m where
    extraMaxCExM :: (T.Text, Maybe T.Text) -> m Int
    incrMaxCExM :: (T.Text, Maybe T.Text) -> m ()

    extraMaxDepthM :: m Int
    incrMaxDepthM :: m ()

    extraMaxTimeM :: (T.Text, Maybe T.Text) -> m NominalDiffTime
    incrMaxTimeM :: (T.Text, Maybe T.Text) -> m ()

    maxSynthFormSizeM :: m MaxSize
    incrMaxSynthFormSizeM :: m ()

    maxSynthCoeffSizeM :: m MaxSize
    incrMaxSynthCoeffSizeM :: m ()
    setMaxSynthCoeffSizeM :: MaxSize -> m ()

    synthFreshM :: m Int
    incrSynthFreshM :: m ()

instance (Monad m, Progresser p) => ProgresserM (StateT p m) where
    extraMaxCExM n = gets (extraMaxCEx n)
    incrMaxCExM n = modify' (incrMaxCEx n)

    extraMaxDepthM = gets extraMaxDepth
    incrMaxDepthM = modify' incrMaxDepth

    extraMaxTimeM n = gets (extraMaxTime n)
    incrMaxTimeM n = modify' (incrMaxTime n)

    maxSynthFormSizeM = gets maxSynthFormSize
    incrMaxSynthFormSizeM = modify' incrMaxSynthFormSize

    maxSynthCoeffSizeM = gets maxSynthCoeffSize
    incrMaxSynthCoeffSizeM = modify' incrMaxSynthCoeffSize
    setMaxSynthCoeffSizeM max_size = modify' (setMaxSynthCoeffSize max_size)

    synthFreshM = gets synthFresh
    incrSynthFreshM = modify' incrSynthFresh

instance ProgresserM m => ProgresserM (ReaderT env m) where
    extraMaxCExM n = lift (extraMaxCExM n)
    incrMaxCExM n = lift (incrMaxCExM n)

    extraMaxDepthM = lift extraMaxDepthM
    incrMaxDepthM = lift incrMaxDepthM

    extraMaxTimeM n = lift (extraMaxTimeM n)
    incrMaxTimeM n = lift (incrMaxTimeM n)

    maxSynthFormSizeM = lift maxSynthFormSizeM
    incrMaxSynthFormSizeM = lift incrMaxSynthFormSizeM

    maxSynthCoeffSizeM = lift maxSynthCoeffSizeM
    incrMaxSynthCoeffSizeM = lift incrMaxSynthCoeffSizeM
    setMaxSynthCoeffSizeM max_size = lift (setMaxSynthCoeffSizeM max_size)

    synthFreshM = lift synthFreshM
    incrSynthFreshM = lift incrSynthFreshM

runProgresser :: (Monad m, Progresser p) => StateT p m a -> p -> m a
runProgresser = evalStateT

incrMaxSize :: Integer -> MaxSize -> MaxSize
incrMaxSize incr (MaxSize sz) = MaxSize (sz + incr)

-------------------------------
-- Configurations
-------------------------------

data Configs = Configs { g2_config :: Config
                       , g2lh_config :: LHConfig -- ^ Configurations for running G2 in LH mode
                       , lh_config :: LH.Config -- ^ LiquidHaskell configuration settings
                       , inf_config :: InferenceConfig }

class InfConfig c where
    g2Config :: c -> Config
    g2lhConfig :: c -> LHConfig
    lhConfig :: c -> LH.Config
    infConfig :: c -> InferenceConfig

class Monad m => InfConfigM m where
    g2ConfigM :: m Config
    g2lhConfigM :: m LHConfig
    lhConfigM :: m LH.Config
    infConfigM :: m InferenceConfig

instance InfConfig Configs where
    g2Config = g2_config
    g2lhConfig = g2lh_config
    lhConfig = lh_config
    infConfig = inf_config

instance InfConfig env => InfConfig (ReaderT env m a) where
    g2Config = return . g2Config =<< ask
    g2lhConfig = return . g2lhConfig =<< ask
    lhConfig = return . lhConfig =<< ask
    infConfig = return . infConfig =<< ask

instance (Monad m, InfConfig env) => InfConfigM (ReaderT env m) where 
    g2ConfigM = return . g2Config =<< ask 
    g2lhConfigM = return . g2lhConfig =<< ask
    lhConfigM = return . lhConfig =<< ask 
    infConfigM = return . infConfig =<< ask 

instance InfConfigM m => InfConfigM (StateT env m) where
    g2ConfigM = lift g2ConfigM
    g2lhConfigM = lift g2lhConfigM
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
                    , use_level_dec :: Bool
                    , use_negated_models :: Bool

                    , use_binary_minimization :: Bool -- ^ In parallel to the SMT's solvers minimization support,
                                                      --   use a binary search to minimize synthesis solutions

                    , use_invs :: Bool
                   
                    , timeout_se :: NominalDiffTime
                    , timeout_sygus :: NominalDiffTime }

getAllConfigsForInf :: IO (String, Bool, Config, LHConfig, InferenceConfig, Maybe String)
getAllConfigsForInf = do
    homedir <- getHomeDirectory
    execParser (mkAllConfigsForInf homedir)

mkAllConfigsForInf :: String -> ParserInfo (String, Bool, Config, LHConfig, InferenceConfig, Maybe String)
mkAllConfigsForInf homedir =
    info (((,,,,,) <$> getFileName
                <*> flag False True (long "count" <> help "count the number of functions in the file")
                <*> mkConfig homedir
                <*> mkLHConfig
                <*> mkInferenceConfig
                <*> mkFuncCheck) <**> helper)
          ( fullDesc
          <> progDesc "Automatically infers specifications to verify code using LiquidHaskell."
          <> header "The G2 Symbolic Execution Engine" )

getFileName :: Parser String
getFileName = argument str (metavar "FILE")

runConfigs :: InfConfig env => ReaderT env m a -> env -> m a
runConfigs = runReaderT

mkInferenceConfig :: Parser InferenceConfig
mkInferenceConfig = InferenceConfig
    <$> flag True False (long "keep-quals" <> help "allow qualifiers to be generated and used during inference")
    <*> pure S.empty
    <*> option auto (long "max-ce"
                   <> metavar "M"
                   <> value 5
                   <> help "the initial maximal number of counterexamples to return from any symbolic execution call")
    <*> pure S.empty
    <*> pure S.empty
    <*> switch (long "restrict-coeffs-1" <> help "restrict coefficients to -1, 0, 1")
    <*> flag True False (long "no-extra-fcs" <> help "do not generate extra (non-blocking) constraints")
    <*> flag True False (long "no-level-dec" <> help "do not use level descent")
    <*> flag True False (long "no-negated-models" <> help "do not use negated models")
    <*> flag True False (long "no-binary-min" <> help "use binary minimization during synthesis")
    <*> switch (long "use-invs" <> help "use invariant mode (benchmarking only)")
    <*> option (maybeReader (Just . fromInteger . read)) (long "timeout-se"
                   <> metavar "T"
                   <> value 5
                   <> help "timeout for symbolic execution")
    <*> option (maybeReader (Just . fromInteger . read)) (long "timeout-sygus"
                   <> metavar "T"
                   <> value 5
                   <> help "timeout for synthesis")

mkFuncCheck :: Parser (Maybe String)
mkFuncCheck =
    option (eitherReader (Right . Just))
            ( long "liquid-func"
            <> metavar "FUNC"
            <> value Nothing
            <> help "a function to directly run symbolic execution on")


mkInferenceConfigDirect :: [String] -> InferenceConfig
mkInferenceConfigDirect as =
    InferenceConfig { keep_quals = boolArg "keep-quals" as M.empty On
                    , modules = S.empty
                    , max_ce = strArg "max-ce" as M.empty read 5
                    , pre_refined = S.empty
                    , refinable_funcs = S.empty
                    , restrict_coeffs = boolArg "restrict-coeffs" as M.empty Off
                    , use_extra_fcs = boolArg "use-extra-fc" as M.empty On
                    , use_level_dec = boolArg "use-level-dec" as M.empty On
                    , use_negated_models = boolArg "use-negated-models" as M.empty On
                    , use_binary_minimization = False
                    , use_invs = boolArg "use-invs" as M.empty Off
                    , timeout_se = strArg "timeout-se" as M.empty (fromInteger . read) 5
                    , timeout_sygus = strArg "timeout-sygus" as M.empty (fromInteger . read) 10 }

adjustConfig :: Maybe T.Text -> SimpleState -> Config -> LHConfig -> InferenceConfig -> [GhcInfo] -> (Config, LHConfig, InferenceConfig)
adjustConfig main_mod (SimpleState { expr_env = eenv }) config lhconfig infconfig ghci =
    let
        -- ref = refinable main_mod meas tcv eenv

        pre = S.fromList
            . map (\(Name n m _ _) -> (n, m))
            . map (mkName . V.varName . fst)
            $ concatMap getTySigs ghci

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
    
        lhconfig' = lhconfig { only_top = True
                             , block_errors_in = S.fromList ns_not_main }

        infconfig' = infconfig { modules = S.singleton main_mod
                               , pre_refined = pre }
    in
    (config, lhconfig', infconfig')

adjustConfigPostLH :: Maybe T.Text -> Measures -> TCValues -> S.State t -> [GhcInfo] -> LHConfig -> LHConfig
adjustConfigPostLH main_mod meas tcv (S.State { S.expr_env = eenv, S.known_values = kv }) ghci lhconfig =
    let
        ref = refinable main_mod meas tcv ghci kv eenv
        
        ns_mm = map (\(Name n m _ _) -> (n, m))
              . filter (\(Name n m _ _) -> (n, m) `elem` ref)
              $ E.keys eenv

    in
    lhconfig { counterfactual = Counterfactual . CFOnly $ S.fromList ns_mm }

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
    any (\t -> t == tyInt kv || t == tyBool kv) rel_t

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

