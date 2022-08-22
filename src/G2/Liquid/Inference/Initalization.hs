module G2.Liquid.Inference.Initalization ( initStateAndConfig
                                         , createStateForInference
                                         , getGHCI ) where

import G2.Config.Config as G2
import qualified G2.Initialization.Types as IT
import G2.Interface hiding (violated)
import G2.Language
import qualified G2.Language.ExprEnv as E
import G2.Translation

import G2.Liquid.AddTyVars
import G2.Liquid.Config
import G2.Liquid.Interface
import G2.Liquid.Types
import G2.Liquid.Inference.Config
import G2.Liquid.Inference.Verify

import Language.Haskell.Liquid.Types as LH hiding (measures)
import qualified Language.Fixpoint.Types.Config as FP

import qualified Data.Text as T

initStateAndConfig :: ExtractedG2 -> Maybe T.Text -> G2.Config -> LHConfig -> InferenceConfig -> [GhcInfo]
                   -> (LiquidReadyState, G2.Config, LHConfig, InferenceConfig)
initStateAndConfig exg2 main_mod g2config lhconfig infconfig ghci = 
    let
        simp_s = initSimpleState exg2
        (g2config', lhconfig', infconfig') = adjustConfig main_mod simp_s g2config lhconfig infconfig ghci

        lrs = createStateForInference simp_s g2config' lhconfig' ghci

        lh_s = lr_state lrs
        lhconfig'' = adjustConfigPostLH main_mod (measures lh_s) (tcvalues lh_s) (state lh_s) ghci lhconfig'
    in
    (lrs, g2config', lhconfig'', infconfig')

createStateForInference :: SimpleState -> G2.Config -> LHConfig -> [GhcInfo] -> LiquidReadyState
createStateForInference simp_s config lhconfig ghci =
    let
        (simp_s', ph_tyvars) = if add_tyvars lhconfig
                                then fmap Just $ addTyVarsEEnvTEnv simp_s
                                else (simp_s, Nothing)
        (s, b) = initStateFromSimpleState simp_s' True 
                    (\_ ng _ _ _ _ _ -> (Prim Undefined TyBottom, [], [], ng))
                    (E.higherOrderExprs . IT.expr_env)
                    config
    in
    createLiquidReadyState s b ghci ph_tyvars lhconfig

getGHCI :: InferenceConfig -> [FilePath] -> [FilePath] -> IO ([GhcInfo], LH.Config)
getGHCI infconfig proj fp = do
    lhconfig <- defLHConfig proj
    let lhconfig' = lhconfig { pruneUnsorted = True
                             -- Block qualifiers being auto-generated by LH
                             , maxParams = if keep_quals infconfig then maxParams lhconfig else 0
                             , eliminate = if keep_quals infconfig then eliminate lhconfig else FP.All
                             , higherorderqs = False
                             , scrapeImports = False
                             , scrapeInternals = False
                             , scrapeUsedImports = False }
    ghci <- ghcInfos Nothing lhconfig' fp
    return (ghci, lhconfig)
